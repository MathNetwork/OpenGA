import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieThreeArmCancel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0JointSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetIntegral










noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped Topology Manifold BigOperators ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem unitModel_add_app
    (g : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 (A + B) x v =
      unitModel (I := I) (M := M) g 2 A x v +
        unitModel (I := I) (M := M) g 2 B x v := by
  have hfun : unitModel (I := I) (M := M) g 2 (A + B) x =
      unitModel (I := I) (M := M) g 2 A x +
        unitModel (I := I) (M := M) g 2 B x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]
  rw [hfun, ContinuousMultilinearMap.add_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem unitModel_smul_app
    (g : SmoothRiemannianMetric I M) (c : ℝ) (A : SmoothCcTensor g 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 (c • A) x v =
      c * unitModel (I := I) (M := M) g 2 A x v := by
  have hfun : unitModel (I := I) (M := M) g 2 (c • A) x =
      c • unitModel (I := I) (M := M) g 2 A x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul]
  rw [hfun, ContinuousMultilinearMap.smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem jointRS_smul {r q : ℕ} {S : Set ℝ} (c : ℝ)
    (A : ∀ p : M × ℝ, TensorRSSpace r q I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r q ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r q ℝ E)
        (E := fun z : M => TensorRSSpace r q I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r q ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r q ℝ E)
        (E := fun z : M => TensorRSSpace r q I z) p.1 (c • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r q
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (TensorRSModel r q ℝ E)
    (fun z : M => TensorRSSpace r q I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := TensorRSModel r q ℝ E)
    (E := fun z : M => TensorRSSpace r q I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := c)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul c (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      c (A p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem hjoint_smul
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g r 2) {δ δ' : ℝ} (c : ℝ)
    (hΦ : linearizedRicciThreeArmHjoint (I := I) (M := M) g r Φ
      (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun s => c • Φ s) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint] at hΦ ⊢
  have h := jointRS_smul (I := I) (M := M) c
    (fun p : M × ℝ => (Φ p.2).toSection p.1) hΦ
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel r 2 ℝ E)
    (E := fun z : M => TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem hjoint_add
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ Ψ : ℝ → SmoothCcTensor g r 2) {δ δ' : ℝ}
    (hΦ : linearizedRicciThreeArmHjoint (I := I) (M := M) g r Φ
      (δ := δ) (δ' := δ'))
    (hΨ : linearizedRicciThreeArmHjoint (I := I) (M := M) g r Ψ
      (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun s => Φ s + Ψ s) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint] at hΦ hΨ ⊢
  have h := joint_rs_add (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (Φ p.2).toSection p.1)
    (fun p : M × ℝ => (Ψ p.2).toSection p.1) hΦ hΨ
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel r 2 ℝ E)
    (E := fun z : M => TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem symmS_eq_self_local
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (hS : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g S x v w = smoothCcTensorBilinForm (I := I) g S x w v) :
    ccTensor02Symm (I := I) (M := M) g S = S := by
  have hswap : domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g 2 S x ![u, w] =
          unitModel (I := I) (M := M) g 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x w u]
      exact hS x u w
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  rw [ccTensor02Symm, hswap, ← two_smul ℝ S, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

omit [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem chartLie_symm
    (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartLieDeTurckComp (I := I) g g_bg x i j y =
      chartLieDeTurckComp (I := I) g g_bg x j i y := by
  have hA : (∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) g g_bg x k y *
          partialDeriv (E := E) k (chartGramOnE (I := I) g x i j) y) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) g g_bg x k y *
          partialDeriv (E := E) k (chartGramOnE (I := I) g x j i) y := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    apply congrArg (fun f : E → ℝ => partialDeriv (E := E) k f y)
    funext z
    exact chartGramOnE_symm (I := I) g x i j z
  have hB : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g x k j y *
          partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg x k) y) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g x j k y *
          partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g g_bg x k) y := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g x k j y]
  have hC : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g x i k y *
          partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g g_bg x k) y) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g x k i y *
          partialDeriv (E := E) j (chartDeTurckVFComp (I := I) g g_bg x k) y := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g x i k y]
  rw [chartLieDeTurckComp_def, chartLieDeTurckComp_def, hA, hB, hC]
  ring

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private theorem lieSlope_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j : Fin (Module.finrank ℝ E)) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        g_bg x i j s (extChartAt I x x) =
      lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        g_bg x j i s (extChartAt I x x) := by
  rw [← deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope (I := I)
      g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg x i j hs,
    ← deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope (I := I)
      g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg x j i hs]
  congr 1
  funext t
  exact chartLie_symm (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' t) g_bg x i j (extChartAt I x x)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in


theorem lieSum_eq_arms
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    lieSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (deTurckLieCoeffField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg +
                lieCorr0Field (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 0
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) +
            operatorFieldApply (I := I) (M := M) g₀ 3 2
              (deTurckLieArm1Coeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 1
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) +
            operatorFieldApply (I := I) (M := M) g₀ 4 2
              (deTurckLieArm2PrincipalCoeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 2
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x ![v, w] := by
  classical
  let W : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg +
            lieCorr0Field (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) +
        operatorFieldApply (I := I) (M := M) g₀ 3 2
          (deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 1
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) +
        operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
  unfold lieSumSlope
  change (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
        lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          g_bg x i k s (extChartAt I x x)) =
    unitModel (I := I) (M := M) g₀ 2 W x ![v, w]
  calc
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
            g_bg x k i s (extChartAt I x x) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [lieSlope_symm (I := I) g₀ g_bg T T'
        hδ_lt hδ hδ'_lt hδ' x i k hs]
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          unitModel (I := I) (M := M) g₀ 2 W x
            ![(chartModelBasis E) k, (chartModelBasis E) i] := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [lieSlope_eq_arms (I := I) g₀ g_bg T T'
        hδ_lt hδ hδ'_lt hδ' s x k i]
    _ = _ := unitModel_basis_expand_two (I := I) (M := M) g₀ W x ![v, w]



def rhsLow0Coeff
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  (-2 : ℝ) • linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s +
    (deTurckLieCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg +
      lieCorr0Field (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)



def rhsLow1Coeff
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 3 2 :=
  (-2 : ℝ) • linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s +
    deTurckLieArm1Coeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg



theorem rhsLow0_path_joint
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => rhsLow0Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s)
      (δ := δ) (δ' := δ') := by
  have hR := linearizedRicciConnDiffOrder0Coeff_jointContMDiffOn_smallPerturbationSet
    (I := I) g₀ T T' hδ hδ'
  have hL := deTurckLieCoeffField_realizedFam_jointSmooth
    (I := I) g₀ T T' hδ hδ' g_bg
  have hC := lieCorr0_path_joint (I := I) g₀ T T' hδ hδ' g_bg
  have hLC := hjoint_add (I := I) (M := M) g₀ 2 _ _ hL hC
  have hR' := hjoint_smul (I := I) (M := M) g₀ 2 _ (-2 : ℝ) hR
  simpa only [rhsLow0Coeff] using hjoint_add (I := I) (M := M) g₀ 2 _ _ hR' hLC



theorem rhsLow1_path_joint
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (fun s => rhsLow1Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s)
      (δ := δ) (δ' := δ') := by
  have hR := linearizedRicciConnDiffOrder1Coeff_jointContMDiffOn_smallPerturbationSet
    (I := I) g₀ T T' hδ hδ'
  have hL := deTurckLieArm1Coeff_realizedFam_jointSmooth
    (I := I) g₀ T T' hδ hδ' g_bg
  have hR' := hjoint_smul (I := I) (M := M) g₀ 3 _ (-2 : ℝ) hR
  simpa only [rhsLow1Coeff] using hjoint_add (I := I) (M := M) g₀ 3 _ _ hR' hL

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in


theorem rhsLow_eq_arms
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    rhsLowTerm (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (rhsLow0Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 3 2
            (rhsLow1Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x ![v, w] := by
  classical
  have hsubsymm : ∀ (y : M) (u z : TangentSpace I y),
      smoothCcTensorBilinForm (I := I) g₀ (T - T') y u z =
        smoothCcTensorBilinForm (I := I) g₀ (T - T') y z u := by
    intro y u z
    rw [ccTensorBilin_sub, ccTensorBilin_sub, hTsymm y u z, hT'symm y u z]
  have hsymmS : ccTensor02Symm (I := I) (M := M) g₀ (T - T') = T - T' :=
    symmS_eq_self_local (I := I) (M := M) g₀ (T - T') hsubsymm
  have hLie := lieSum_eq_arms (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x v w hs
  have hLieSplit := lieSum_eq_split (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x v w s
  have hTop := lieTop_add_swap (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x v w s
  rw [hsymmS] at hLie hTop
  have hLower :
      lieOneSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s +
          lieZeroSum (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s -
          lieTopTailSwap (I := I) g₀ T T' hδ hδ' x v w s =
        unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (deTurckLieCoeffField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg +
                lieCorr0Field (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
            operatorFieldApply (I := I) (M := M) g₀ 3 2
              (deTurckLieArm1Coeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x ![v, w] := by
    simp only [unitModel_add_app] at hLie ⊢
    linear_combination hLie - hLieSplit - hTop
  have hR0 :
      linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s +
          (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s -
            linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s) =
        linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s := by
    abel
  have hR1 :
      linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s +
          (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s -
            linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s) =
        linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s := by
    abel
  unfold rhsLowTerm rhsLow0Coeff rhsLow1Coeff
  rw [hR0, hR1]
  simp only [appCc_add_left, unitModel_add_app] at hLower
  simp only [appCc_add_left, appCc_smul_left, unitModel_add_app, unitModel_smul_app]
  linear_combination hLower

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in




theorem rhsSlope_eq_arms
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (rhsLow0Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 3 2
            (rhsLow1Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T T' hδ hδ' s))
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x ![v, w] := by
  rw [rhsSlope_eq_split (I := I) g₀ g_bg T T' hTsymm hT'symm
    hδ_lt hδ hδ'_lt hδ' x v w hs]
  rw [rhsLow_eq_arms (I := I) g₀ g_bg T T' hTsymm hT'symm
    hδ_lt hδ hδ'_lt hδ' x v w hs]
  unfold rhsTopTerm
  simp only [unitModel_add_app]
  ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
