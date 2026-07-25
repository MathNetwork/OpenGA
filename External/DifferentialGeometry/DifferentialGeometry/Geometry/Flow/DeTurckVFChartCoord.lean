import DifferentialGeometry.Geometry.Flow.VectorField
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.ChartVectorField
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartLeviCivitaParallelExtend


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartBasisVecFiber_eq_chartParallelExtend_on_baseSet
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (j : Fin (Module.finrank ℝ E)) :
    ∀ b' ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      chartBasisVecFiber (I := I) α j b' =
        chartParallelExtend (I := I) α b
          (chartBasisVecFiber (I := I) α j b) b' := by
  intro b' _hb'
  unfold chartParallelExtend
  change (trivializationAt E (TangentSpace I) α).symm b' ((chartModelBasis E) j) =
    trivFromE (I := I) α b'
      (trivToE (I := I) α b
        ((trivializationAt E (TangentSpace I) α).symm b ((chartModelBasis E) j)))
  have hround : trivToE (I := I) α b
      ((trivializationAt E (TangentSpace I) α).symm b ((chartModelBasis E) j)) =
      (chartModelBasis E) j := by
    change trivToE (I := I) α b
        (trivFromE (I := I) α b ((chartModelBasis E) j)) = (chartModelBasis E) j
    exact trivToE_trivFromE (I := I) α hb ((chartModelBasis E) j)
  rw [hround]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartBasisVecFiber_eventuallyEq_chartParallelExtend
    (α : M) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (j : Fin (Module.finrank ℝ E)) :
    (fun b' : M => chartBasisVecFiber (I := I) α j b') =ᶠ[𝓝 b]
      fun b' : M =>
        chartParallelExtend (I := I) α b (chartBasisVecFiber (I := I) α j b) b' := by
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hbase_nhds : (trivializationAt E (TangentSpace I) α).baseSet ∈ 𝓝 b :=
    hopen.mem_nhds hb_base
  refine Filter.eventually_of_mem hbase_nhds ?_
  intro b' hb'
  exact chartBasisVecFiber_eq_chartParallelExtend_on_baseSet (I := I) α hb_base j b' hb'

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartBasisVecFiber_mdifferentiableAt
    (α : M) (j : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    MDiffAt (T% (fun b' : M => chartBasisVecFiber (I := I) α j b')) b := by
  classical
  have hcontMDiff_on := chartBasisVec_contMDiffOn (I := I) α j
  have hopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hcontMDiff_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (chartBasisVec (I := I) α j) b :=
    (hcontMDiff_on b hb).contMDiffAt (hopen.mem_nhds hb)
  exact hcontMDiff_at.mdifferentiableAt (by norm_num)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma LeviCivita_chartBasisVecFiber_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (j : Fin (Module.finrank ℝ E)) (v : TangentSpace I b) :
    (LeviCivita (I := I) g).toFun
        (fun b' : M => chartBasisVecFiber (I := I) α j b') b v =
      trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b ((chartModelBasis E) j) v) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hsection_diff : MDiffAt
      (T% (fun b' : M => chartBasisVecFiber (I := I) α j b')) b :=
    chartBasisVecFiber_mdifferentiableAt (I := I) α j
      (chartLeviCivitaGoodSet_mem_baseSet (I := I) hb)
  have hparallel_diff : MDiffAt
      (T% (fun b' : M => chartParallelExtend (I := I) α b
        (chartBasisVecFiber (I := I) α j b) b')) b :=
    chartParallelExtend_mdifferentiableAt (I := I) α hb
      (chartBasisVecFiber (I := I) α j b)
  have heq : (fun b' : M => chartBasisVecFiber (I := I) α j b') =ᶠ[𝓝 b]
      fun b' : M =>
        chartParallelExtend (I := I) α b (chartBasisVecFiber (I := I) α j b) b' :=
    chartBasisVecFiber_eventuallyEq_chartParallelExtend (I := I) α hb j
  have hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  have hgood_nhds : chartLeviCivitaGoodSet (I := I) α ∈ 𝓝 b :=
    hgood_open.mem_nhds hb
  have hcov_eq :
      (LeviCivita (I := I) g).toFun
          (fun b' : M => chartBasisVecFiber (I := I) α j b') b =
        (LeviCivita (I := I) g).toFun
          (fun b' : M =>
            chartParallelExtend (I := I) α b (chartBasisVecFiber (I := I) α j b) b') b := by
    have hLC := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv
    exact hLC.congr_of_eventuallyEq hsection_diff hparallel_diff
      (Filter.univ_mem) heq
  rw [show
        (LeviCivita (I := I) g).toFun
            (fun b' : M => chartBasisVecFiber (I := I) α j b') b v
          = (LeviCivita (I := I) g).toFun
              (fun b' : M =>
                chartParallelExtend (I := I) α b
                  (chartBasisVecFiber (I := I) α j b) b') b v from by
          rw [hcov_eq]]
  rw [LeviCivita_chart_apply (I := I) g α hb hparallel_diff v]
  have hcompute := chartLeviCivita_chartParallelExtend_symm (I := I) g α hb
    (chartBasisVecFiber (I := I) α j b) (fun _ : M => v)
  rw [hcompute]
  congr 1
  have hcancel := christoffelCorrection_symm_cancel (I := I) g α b
    (chartBasisVecFiber (I := I) α j b) v
  rw [hcancel]
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have htriv : trivToE (I := I) α b
      (chartBasisVecFiber (I := I) α j b) = (chartModelBasis E) j := by
    change trivToE (I := I) α b
        (trivFromE (I := I) α b ((chartModelBasis E) j)) = (chartModelBasis E) j
    exact trivToE_trivFromE (I := I) α hb_base ((chartModelBasis E) j)
  rw [htriv]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connDiff_chartBasis_pair_eq
    (g g' : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (j k : Fin (Module.finrank ℝ E)) :
    connDiff (I := I) g g' x
        (chartBasisVecFiber (I := I) α j x)
        (chartBasisVecFiber (I := I) α k x) =
      trivFromE (I := I) α x
        (christoffelCorrection (I := I) g α x ((chartModelBasis E) j)
          (chartBasisVecFiber (I := I) α k x)) -
      trivFromE (I := I) α x
        (christoffelCorrection (I := I) g' α x ((chartModelBasis E) j)
          (chartBasisVecFiber (I := I) α k x)) := by
  classical
  have hsection_diff : MDiffAt
      (T% (fun b' : M => chartBasisVecFiber (I := I) α j b')) x :=
    chartBasisVecFiber_mdifferentiableAt (I := I) α j
      (chartLeviCivitaGoodSet_mem_baseSet (I := I) hx)
  rw [connDiff_apply (I := I) g g' hsection_diff
        (chartBasisVecFiber (I := I) α k x)]
  rw [LeviCivita_chartBasisVecFiber_eq (I := I) g α hx j
        (chartBasisVecFiber (I := I) α k x)]
  rw [LeviCivita_chartBasisVecFiber_eq (I := I) g' α hx j
        (chartBasisVecFiber (I := I) α k x)]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma coord_christoffelCorrection_chartBasis_pair
    (g : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (j k p : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).coord p)
        (christoffelCorrection (I := I) g α x ((chartModelBasis E) j)
          (chartBasisVecFiber (I := I) α k x)) =
      chartChristoffel (I := I) g α k j p (extChartAt I α x) := by
  classical
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  rw [christoffelCorrection_apply (I := I) g α x ((chartModelBasis E) j)
        (chartBasisVecFiber (I := I) α k x)]
  have htriv : trivToE (I := I) α x
      (chartBasisVecFiber (I := I) α k x) = (chartModelBasis E) k := by
    change trivToE (I := I) α x
        (trivFromE (I := I) α x ((chartModelBasis E) k)) = (chartModelBasis E) k
    exact trivToE_trivFromE (I := I) α hx_base ((chartModelBasis E) k)
  rw [htriv]
  rw [map_sum]
  rw [Finset.sum_eq_single k]
  · rw [map_sum]
    rw [Finset.sum_eq_single j]
    · rw [map_sum]
      rw [Finset.sum_eq_single p]
      · rw [LinearMap.map_smul, smul_eq_mul]
        simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_apply, ↓reduceIte]
        ring
      · intro k' _ hk'
        rw [LinearMap.map_smul, smul_eq_mul]
        simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_apply, if_neg hk', mul_zero]
      · intro h
        exact absurd (Finset.mem_univ p) h
    · intro j' _ hj'
      rw [map_sum]
      refine Finset.sum_eq_zero (fun p' _ => ?_)
      rw [LinearMap.map_smul, smul_eq_mul]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply, if_neg (Ne.symm hj')]
      ring
    · intro h
      exact absurd (Finset.mem_univ j) h
  · intro k' _ hk'
    rw [map_sum]
    refine Finset.sum_eq_zero (fun j' _ => ?_)
    rw [map_sum]
    refine Finset.sum_eq_zero (fun p' _ => ?_)
    rw [LinearMap.map_smul, smul_eq_mul]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, if_neg (Ne.symm hk')]
    ring
  · intro h
    exact absurd (Finset.mem_univ k) h

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma tangent_vector_eq_chartBasisVecFiber_sum
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (w : TangentSpace I x) :
    w =
      ∑ p : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (trivToE (I := I) α x w)) p •
          chartBasisVecFiber (I := I) α p x := by
  classical
  have hround : trivFromE (I := I) α x (trivToE (I := I) α x w) = w :=
    trivFromE_trivToE (I := I) α hx w
  conv_lhs => rw [← hround]
  set u : E := trivToE (I := I) α x w with hu_def
  have hexp : u =
      ∑ p : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr u) p • (chartModelBasis E) p := by
    exact ((chartModelBasis E).sum_equivFun u).symm
  conv_lhs => rw [hexp]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [ContinuousLinearMap.map_smul]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma trivFromE_eq_chartBasisVecFiber_sum
    (α : M) (x : M) (y : E) :
    trivFromE (I := I) α x y =
      ∑ p : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr y) p •
          chartBasisVecFiber (I := I) α p x := by
  classical
  have hexp : y =
      ∑ p : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr y) p • (chartModelBasis E) p := by
    exact ((chartModelBasis E).sum_equivFun y).symm
  conv_lhs => rw [hexp]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [ContinuousLinearMap.map_smul]
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connDiff_chartBasis_pair_eq_sum
    (g g' : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (j k : Fin (Module.finrank ℝ E)) :
    connDiff (I := I) g g' x
        (chartBasisVecFiber (I := I) α j x)
        (chartBasisVecFiber (I := I) α k x) =
      ∑ p : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
          chartChristoffel (I := I) g' α k j p (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α p x := by
  classical
  rw [connDiff_chartBasis_pair_eq (I := I) g g' α hx j k]
  set Cg : E := christoffelCorrection (I := I) g α x ((chartModelBasis E) j)
    (chartBasisVecFiber (I := I) α k x) with hCg_def
  set Cg' : E := christoffelCorrection (I := I) g' α x ((chartModelBasis E) j)
    (chartBasisVecFiber (I := I) α k x) with hCg'_def
  rw [trivFromE_eq_chartBasisVecFiber_sum (I := I) α x Cg]
  rw [trivFromE_eq_chartBasisVecFiber_sum (I := I) α x Cg']
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [← sub_smul]
  congr 1
  have hcoord_g : ((chartModelBasis E).repr Cg) p =
      ((chartModelBasis E).coord p) Cg := rfl
  have hcoord_g' : ((chartModelBasis E).repr Cg') p =
      ((chartModelBasis E).coord p) Cg' := rfl
  rw [hcoord_g, hcoord_g']
  rw [hCg_def, hCg'_def]
  rw [coord_christoffelCorrection_chartBasis_pair (I := I) g α hx j k p]
  rw [coord_christoffelCorrection_chartBasis_pair (I := I) g' α hx j k p]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckChartLocal_eq_chartDeTurckVFComp_sum
    (g g' : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    deTurckChartLocal (I := I) g g' α x =
      ∑ p : Fin (Module.finrank ℝ E),
        DeTurckLinearization.chartDeTurckVFComp (I := I) g g' α p (extChartAt I α x) •
          chartBasisVecFiber (I := I) α p x := by
  classical
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  rw [deTurckChartLocal_def]
  have hreplace :
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x j k •
          connDiff (I := I) g g' x
            (chartBasisVecFiber (I := I) α j x)
            (chartBasisVecFiber (I := I) α k x) =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x j k •
          ∑ p : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
              chartChristoffel (I := I) g' α k j p (extChartAt I α x)) •
              chartBasisVecFiber (I := I) α p x := by
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [connDiff_chartBasis_pair_eq_sum (I := I) g g' α hx j k]
  rw [hreplace]
  have hpush :
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x j k •
          ∑ p : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
              chartChristoffel (I := I) g' α k j p (extChartAt I α x)) •
              chartBasisVecFiber (I := I) α p x =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ∑ p : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) g α x j k *
            (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
              chartChristoffel (I := I) g' α k j p (extChartAt I α x))) •
            chartBasisVecFiber (I := I) α p x := by
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [smul_smul]
  rw [hpush]
  have hcomm1 :
      ∀ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : Fin (Module.finrank ℝ E),
            (chartInvGramMatrix (I := I) g α x j k *
              (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
                chartChristoffel (I := I) g' α k j p (extChartAt I α x))) •
              chartBasisVecFiber (I := I) α p x =
        ∑ p : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (chartInvGramMatrix (I := I) g α x j k *
              (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
                chartChristoffel (I := I) g' α k j p (extChartAt I α x))) •
              chartBasisVecFiber (I := I) α p x := by
    intro j
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl (fun j _ => hcomm1 j)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro p _
  have hinner_pull :
      ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (chartInvGramMatrix (I := I) g α x j k *
              (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
                chartChristoffel (I := I) g' α k j p (extChartAt I α x))) •
              chartBasisVecFiber (I := I) α p x =
        ∑ j : Fin (Module.finrank ℝ E),
          (∑ k : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α x j k *
                (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
                  chartChristoffel (I := I) g' α k j p (extChartAt I α x))) •
            chartBasisVecFiber (I := I) α p x := by
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [← Finset.sum_smul]
  rw [hinner_pull]
  rw [← Finset.sum_smul]
  congr 1
  rw [DeTurckLinearization.chartDeTurckVFComp_def]
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro b _
  have hinv_eq : chartInvGramMatrix (I := I) g α x a b =
      chartInvGramOnE (I := I) g α a b (extChartAt I α x) := by
    rw [chartInvGramOnE_def]
    have hsrc : x ∈ (extChartAt I α).source :=
      chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
    have hinv : (extChartAt I α).symm ((extChartAt I α) x) = x :=
      (extChartAt I α).left_inv hsrc
    rw [hinv]
  rw [hinv_eq]
  congr 1
  rw [chartChristoffel_symm (I := I) g α b a p (extChartAt I α x)]
  rw [chartChristoffel_symm (I := I) g' α b a p (extChartAt I α x)]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckVF_apply_eq_chartDeTurckVFComp_sum
    (g g' : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (deTurckVF (I := I) g g' :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ p : Fin (Module.finrank ℝ E),
        DeTurckLinearization.chartDeTurckVFComp (I := I) g g' α p (extChartAt I α x) •
          chartBasisVecFiber (I := I) α p x := by
  rw [deTurckVF_apply (I := I) g g' x]
  have hxα_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  rw [← deTurckChartLocal_eq_deTurckFun (I := I) g g' α hxα_base]
  exact deTurckChartLocal_eq_chartDeTurckVFComp_sum (I := I) g g' α hx

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckVF_apply_eq_chartDeTurckVFComp_sum_self
    (g g' : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g g' :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ p : Fin (Module.finrank ℝ E),
        DeTurckLinearization.chartDeTurckVFComp (I := I) g g' x p (extChartAt I x x) •
          ((chartModelBasis E) p : TangentSpace I x) := by
  rw [deTurckVF_apply_eq_chartDeTurckVFComp_sum (I := I) g g' x
    (self_mem_chartLeviCivitaGoodSet (I := I) (α := x))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  congr 1
  exact chartBasisVecFiber_self (I := I) x p

end DeTurck
end PDE
end DifferentialGeometry
