import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ExtendedSolutionRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ChartRicciJetIdentity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridge
import DifferentialGeometry.Geometry.Coordinates.CoordinateFrame

set_option autoImplicit false









noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Analysis
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open IntrinsicSpectral.DeTurckCoefficients
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable [BoundarylessManifold I M]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma coordFrame_chartSum
    (x0 : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x0)
    (i : CoordinateIdx (𝕜 := Real) E) :
    coordinateFrameAt (I := I) x0 i x =
      ∑ j : Fin (Module.finrank Real E),
        (chartModelBasis E).repr ((Module.finBasis Real E) i) j •
          chartBasisVecFiber (I := I) x0 j x := by
  let e := trivializationAt E (TangentSpace I) x0
  change e.localFrame (Module.finBasis Real E) i x = _
  rw [e.localFrame_apply_of_mem_baseSet (b := Module.finBasis Real E) hx]
  calc
    e.basisAt (Module.finBasis Real E) hx i =
        e.symmL Real x ((Module.finBasis Real E) i) := by
      simp [Bundle.Trivialization.basisAt]
    _ = e.symmL Real x
        (∑ j : Fin (Module.finrank Real E),
          (chartModelBasis E).repr ((Module.finBasis Real E) i) j •
            chartModelBasis E j) := by
      rw [(chartModelBasis E).sum_repr ((Module.finBasis Real E) i)]
    _ = ∑ j : Fin (Module.finrank Real E),
        (chartModelBasis E).repr ((Module.finBasis Real E) i) j •
          e.symmL Real x (chartModelBasis E j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
    _ = ∑ j : Fin (Module.finrank Real E),
        (chartModelBasis E).repr ((Module.finBasis Real E) i) j •
          chartBasisVecFiber (I := I) x0 j x := by
      rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [BoundarylessManifold I M] in


omit [SigmaCompactSpace M] in
theorem solnChartGramSmooth
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hS : IsSolutionOn (I := I) S)
    (x0 : M) (i j : Fin (Module.finrank Real E)) :
    ContMDiffOn ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M =>
        chartGramMatrix (I := I) (S.base.metric p.1) x0 p.2 i j)
      (Set.Ioo alpha omega ×ˢ
        (trivializationAt E (TangentSpace I) x0).baseSet) := by
  let e := trivializationAt E (TangentSpace I) x0
  have hframe :
      IsLocalFrameOn I E (∞ : WithTop ℕ∞)
        (e.localFrame (chartModelBasis E)) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞)
      (chartModelBasis E)
  have hbridge : ∀ {x : M}, x ∈ e.baseSet ->
      ∀ k : Fin (Module.finrank Real E),
        e.localFrame (chartModelBasis E) k x =
          chartBasisVecFiber (I := I) x0 k x := by
    intro x hx k
    rw [e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hx]
    rfl
  have hcomp :=
    hS.smoothMetric.frameCompSmooth
      (e.localFrame (chartModelBasis E)) hframe i j
  refine hcomp.congr fun p hp => ?_
  simp only [chartGramMatrix_apply, hbridge hp.2 i, hbridge hp.2 j,
    SolutionOn.family]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in


private lemma jet2GramD2Local
    (g : SmoothRiemannianMetric I M) (x0 : M) {y : E}
    (hG1 : ∀ᶠ z in nhds y,
      DifferentiableAt Real (chartGramPi (I := I) g x0) z)
    (hG2 : DifferentiableAt Real
      (fun z => fderiv Real (chartGramPi (I := I) g x0) z) y)
    (m i l j : Fin (Module.finrank Real E)) :
    (jet2 (chartGramPi (I := I) g x0) y).2.2
        (chartModelBasis E m) (chartModelBasis E i) l j =
      partialDeriv (E := E) m
        (partialDeriv (E := E) i (chartGramOnE (I := I) g x0 l j)) y := by
  simp only [jet2]
  rw [fderiv2_matEntry hG2 (chartModelBasis E m) (chartModelBasis E i) l j]
  have heq :
      (fun z => (fderiv Real (chartGramPi (I := I) g x0) z)
        (chartModelBasis E i) l j) =ᶠ[nhds y]
      partialDeriv (E := E) i (chartGramOnE (I := I) g x0 l j) := by
    filter_upwards [hG1] with z hz
    rw [fderiv_matEntry hz (chartModelBasis E i) l j]
    rfl
  rw [heq.fderiv_eq]
  rfl

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartChrDerivJet
    (g : SmoothRiemannianMetric I M) (x0 : M) {y : E}
    (hy : y ∈ interior (extChartAt I x0).target)
    (hG : DifferentiableAt Real (chartGramPi (I := I) g x0) y)
    (hG1 : ∀ᶠ z in nhds y,
      DifferentiableAt Real (chartGramPi (I := I) g x0) z)
    (hG2 : DifferentiableAt Real
      (fun z => fderiv Real (chartGramPi (I := I) g x0) z) y)
    (m i j k : Fin (Module.finrank Real E)) :
    partialDeriv (E := E) m (chartChristoffel (I := I) g x0 i j k) y =
      jetChristoffelDeriv (chartModelBasis E)
        (jet2 (chartGramPi (I := I) g x0) y) m i j k := by
  rw [partialDeriv_chartChristoffel_eq g x0 m i j k hy]
  simp only [jetChristoffelDeriv]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [partialDeriv_chartInvGramOnE_eq g x0 y m k l hy]
  simp only [gramBracket, gramBracketDeriv,
    jet2_chartGram_invGram g x0 y,
    jet2_chartGram_d1 g x0 hG,
    jet2GramD2Local (I := I) g x0 hG1 hG2]

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartRmEqJet
    (g : SmoothRiemannianMetric I M) (x0 : M) {y : E}
    (hy : y ∈ interior (extChartAt I x0).target)
    (hG : DifferentiableAt Real (chartGramPi (I := I) g x0) y)
    (hG1 : ∀ᶠ z in nhds y,
      DifferentiableAt Real (chartGramPi (I := I) g x0) z)
    (hG2 : DifferentiableAt Real
      (fun z => fderiv Real (chartGramPi (I := I) g x0) z) y)
    (i j k l : Fin (Module.finrank Real E)) :
    chartRiemannTensor (I := I) g x0 i j k l y =
      jetRiemann (chartModelBasis E)
        (jet2 (chartGramPi (I := I) g x0) y) i j k l := by
  rw [chartRiemannTensor_def]
  simp only [jetRiemann]
  rw [chartChrDerivJet (I := I) g x0 hy hG hG1 hG2 j i k l,
    chartChrDerivJet (I := I) g x0 hy hG hG1 hG2 k i j l]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [chartChristoffel_eq_jet g x0 hG j m l,
    chartChristoffel_eq_jet g x0 hG i k m,
    chartChristoffel_eq_jet g x0 hG k m l,
    chartChristoffel_eq_jet g x0 hG i j m]

omit [CompleteSpace E] in


omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRmSmoothAt [CompactSpace M]
    (g : Real -> SmoothRiemannianMetric I M)
    (a b : Real) (x0 : M)
    (hsmooth : ∀ x : M, ∀ i j : Fin (Module.finrank Real E),
      ContMDiffOn ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g p.1) x p.2 i j)
        (Set.Ioo a b ×ˢ
          (trivializationAt E (TangentSpace I) x).baseSet))
    {t : Real} {y : E} (ht : t ∈ Set.Ioo a b)
    (hy : y ∈ interior (extChartAt I x0).target)
    (i j k l : Fin (Module.finrank Real E)) :
    ContDiffAt Real ∞
      (fun q : Real × E =>
        chartRiemannTensor (I := I) (g q.1) x0 i j k l q.2) (t, y) := by
  let G : Real -> E -> (Fin (Module.finrank Real E) ->
      Fin (Module.finrank Real E) -> Real) :=
    fun s z => chartGramPi (I := I) (g s) x0 z
  let U : Set (Real × E) :=
    Set.Ioo a b ×ˢ interior (extChartAt I x0).target
  have hG : ContDiffOn Real ∞ (Function.uncurry G) U := by
    refine contDiffOn_pi.mpr fun r => contDiffOn_pi.mpr fun s => ?_
    simpa [G, U, chartGramPi_apply] using
      chartGramOnE_jointContDiffOn (I := I) g a b x0 hsmooth r s
  have hD1 : ContDiffOn Real ∞
      (Function.uncurry (fun s z => fderiv Real (G s) z)) U :=
    spatialFDeriv_contDiffOn isOpen_Ioo.uniqueDiffOn isOpen_interior hG
  have hD2 : ContDiffOn Real ∞
      (Function.uncurry
        (fun s z => fderiv Real (fun w => fderiv Real (G s) w) z)) U :=
    spatialFDeriv_contDiffOn isOpen_Ioo.uniqueDiffOn isOpen_interior hD1
  have hjetOn : ContDiffOn Real ∞
      (fun q : Real × E => jet2 (G q.1) q.2) U := by
    simpa [jet2, Function.uncurry] using hG.prodMk (hD1.prodMk hD2)
  have hmem : (t, y) ∈ U := ⟨ht, hy⟩
  have hUnhd : U ∈ nhds (t, y) :=
    (isOpen_Ioo.prod isOpen_interior).mem_nhds hmem
  have hjet : ContDiffAt Real ∞
      (fun q : Real × E => jet2 (G q.1) q.2) (t, y) :=
    hjetOn.contDiffAt hUnhd
  have hx :
      (extChartAt I x0).symm y ∈
        (trivializationAt E (TangentSpace I) x0).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I x0).map_target (interior_subset hy)
  have hmat :
      Matrix.of (jet2 (G t) y).1 =
        chartGramMatrix (I := I) (g t) x0 ((extChartAt I x0).symm y) := by
    ext r s
    simp [G, jet2, chartGramPi, chartGramOnE_def]
  have hdet : (Matrix.of (jet2 (G t) y).1).det ≠ 0 := by
    rw [hmat]
    exact ne_of_gt (chartGramMatrix_det_pos (I := I) (g t) x0 hx)
  have houter : ContDiffAt Real ∞
      (fun p : MatJet E (Module.finrank Real E) =>
        jetRiemann (chartModelBasis E) p i j k l)
      (jet2 (G t) y) :=
    contDiffAt_jetRiemann (chartModelBasis E) hdet i j k l
  have hmodel : ContDiffAt Real ∞
      (fun q : Real × E =>
        jetRiemann (chartModelBasis E) (jet2 (G q.1) q.2) i j k l)
      (t, y) := by
    simpa only [Function.comp_apply] using houter.comp (t, y) hjet
  have heq :
      (fun q : Real × E =>
        chartRiemannTensor (I := I) (g q.1) x0 i j k l q.2) =ᶠ[nhds (t, y)]
      (fun q : Real × E =>
        jetRiemann (chartModelBasis E) (jet2 (G q.1) q.2) i j k l) := by
    filter_upwards [hUnhd] with q hq
    have hStatic : ContDiffOn Real ∞
        (chartGramPi (I := I) (g q.1) x0)
        (interior (extChartAt I x0).target) := by
      refine contDiffOn_pi.mpr fun r => contDiffOn_pi.mpr fun s => ?_
      exact (chartGramOnE_contDiffOn (I := I) (g q.1) x0 r s).mono
        interior_subset
    have hAt : ContDiffAt Real ∞
        (chartGramPi (I := I) (g q.1) x0) q.2 :=
      hStatic.contDiffAt (isOpen_interior.mem_nhds hq.2)
    have hDiff : DifferentiableAt Real
        (chartGramPi (I := I) (g q.1) x0) q.2 :=
      hAt.differentiableAt (by simp)
    have hDiffNhd : ∀ᶠ z in nhds q.2,
        DifferentiableAt Real (chartGramPi (I := I) (g q.1) x0) z := by
      filter_upwards [isOpen_interior.mem_nhds hq.2] with z hz
      exact (hStatic.contDiffAt (isOpen_interior.mem_nhds hz)).differentiableAt
        (by simp)
    have hDiff2 : DifferentiableAt Real
        (fun z => fderiv Real (chartGramPi (I := I) (g q.1) x0) z) q.2 :=
      (hAt.fderiv_right (m := ∞) le_rfl).differentiableAt (by simp)
    simpa [G] using
      chartRmEqJet (I := I) (g q.1) x0 hq.2 hDiff hDiffNhd hDiff2 i j k l
  exact hmodel.congr_of_eventuallyEq heq



omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem coordRmSmoothInf [CompactSpace M]
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hS : IsSolutionOn (I := I) S)
    (x0 : M)
    (t : RealTimeInterval.RegularTime
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega))
    (x : M) (hx : x ∈ chartLeviCivitaGoodSet (I := I) x0)
    (idx : Fin 4 -> Fin (Module.finrank Real E)) :
    ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M => S.base.rm04 p.1 p.2
        (fun q : Fin 4 => chartBasisVecFiber (I := I) x0 (idx q) p.2))
      ((t : Real), x) := by
  let y := extChartAt I x0 x
  have hy : y ∈ interior (extChartAt I x0).target :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  have hsmooth := fun z i j =>
    solnChartGramSmooth (I := I) hS z i j
  have hLower : ContDiffAt Real ∞
      (fun q : Real × E =>
        ∑ l : Fin (Module.finrank Real E),
          chartRiemannTensor (I := I) (S.base.metric q.1) x0
              (idx 2) (idx 0) (idx 1) l q.2 *
            chartGramOnE (I := I) (S.base.metric q.1) x0 (idx 3) l q.2)
      ((t : Real), y) := by
    refine ContDiffAt.sum fun l _ => (chartRmSmoothAt
      (I := I) S.base.metric alpha omega x0 hsmooth t.2 hy
      (idx 2) (idx 0) (idx 1) l).mul ?_
    exact (chartGramOnE_jointContDiffOn
      (I := I) S.base.metric alpha omega x0 hsmooth (idx 3) l).contDiffAt
        ((isOpen_Ioo.prod isOpen_interior).mem_nhds ⟨t.2, hy⟩)
  have hxsrc : x ∈ (extChartAt I x0).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  have hxchart : x ∈ (chartAt H x0).source := by
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact hxsrc
  have hmap : ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real (Real × E)) ∞
      (fun p : Real × M => (p.1, extChartAt I x0 p.2))
      ((t : Real), x) := by
    have hfst : ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun p : Real × M => p.1) ((t : Real), x) :=
      contMDiffAt_fst
    have hsnd : ContMDiffAt ((modelWithCornersSelf Real Real).prod I) I ∞
        (fun p : Real × M => p.2) ((t : Real), x) :=
      contMDiffAt_snd
    have hchart : ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real E) ∞
        (fun p : Real × M => extChartAt I x0 p.2) ((t : Real), x) :=
      (contMDiffAt_extChartAt' (I := I) (n := ∞) hxchart).comp ((t : Real), x) hsnd
    rw [contMDiffAt_prod_module_iff]
    exact ⟨by simpa only [Function.comp_apply] using hfst,
      by simpa only [Function.comp_apply] using hchart⟩
  have hLowerM : ContMDiffAt (modelWithCornersSelf Real (Real × E))
      (modelWithCornersSelf Real Real) ∞
      (fun q : Real × E =>
        ∑ l : Fin (Module.finrank Real E),
          chartRiemannTensor (I := I) (S.base.metric q.1) x0
              (idx 2) (idx 0) (idx 1) l q.2 *
            chartGramOnE (I := I) (S.base.metric q.1) x0 (idx 3) l q.2)
      ((t : Real), y) :=
    contMDiffAt_iff_contDiffAt.mpr hLower
  have hcomp := hLowerM.comp ((t : Real), x) hmap
  refine hcomp.congr_of_eventuallyEq ?_
  have hgoodNhd :
      {p : Real × M | p.2 ∈ chartLeviCivitaGoodSet (I := I) x0} ∈
        nhds ((t : Real), x) :=
    ((chartLeviCivitaGoodSet_isOpen (I := I) x0).preimage continuous_snd).mem_nhds hx
  filter_upwards [hgoodNhd] with p hp
  change metricRm04 (I := I) (M := M) (S.base.metric p.1) p.2
      (fun q : Fin 4 => chartBasisVecFiber (I := I) x0 (idx q) p.2) = _
  rw [metricRm04_apply,
    rm04_coord_eq (I := I) (S.base.metric p.1) x0 idx hp]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [chartGramOnE_def, (extChartAt I x0).left_inv
    (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hp)]



omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem coordRmFinSmooth [CompactSpace M]
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hS : IsSolutionOn (I := I) S)
    (x0 : M)
    (t : RealTimeInterval.RegularTime
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega))
    (x : M) (hx : x ∈ chartLeviCivitaGoodSet (I := I) x0)
    (idx : Fin 4 -> CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M => realizedRmBase (I := I) S x0 p.1 p.2 idx)
      ((t : Real), x) := by
  let coeff : CoordinateIdx (𝕜 := Real) E ->
      Fin (Module.finrank Real E) -> Real :=
    fun i j => (chartModelBasis E).repr ((Module.finBasis Real E) i) j
  have hsum : ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M =>
        ∑ slots : Fin 4 -> Fin (Module.finrank Real E),
          (∏ q : Fin 4, coeff (idx q) (slots q)) *
            S.base.rm04 p.1 p.2
              (fun q : Fin 4 =>
                chartBasisVecFiber (I := I) x0 (slots q) p.2))
      ((t : Real), x) := by
    refine ContMDiffAt.sum fun slots _ => contMDiffAt_const.mul ?_
    exact coordRmSmoothInf (I := I) hS x0 t x hx slots
  refine hsum.congr_of_eventuallyEq ?_
  have hxframe : x ∈ coordinateFrameSet (I := I) x0 :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hframeNhd :
      {p : Real × M | p.2 ∈ coordinateFrameSet (I := I) x0} ∈
        nhds ((t : Real), x) :=
    ((coordinateFrameSet_open (I := I) x0).preimage continuous_snd).mem_nhds hxframe
  filter_upwards [hframeNhd] with p hp
  simp only [realizedRmBase_apply]
  let A := S.base.rm04 p.1 p.2
  change A (fun q : Fin 4 => coordinateFrameAt (I := I) x0 (idx q) p.2) = _
  calc
    A (fun q : Fin 4 => coordinateFrameAt (I := I) x0 (idx q) p.2) =
        A (fun q : Fin 4 =>
          ∑ j : Fin (Module.finrank Real E),
            coeff (idx q) j • chartBasisVecFiber (I := I) x0 j p.2) := by
      congr 1
      funext q
      exact coordFrame_chartSum (I := I) x0 hp (idx q)
    _ = ∑ slots : Fin 4 -> Fin (Module.finrank Real E),
        A (fun q : Fin 4 => coeff (idx q) (slots q) •
          chartBasisVecFiber (I := I) x0 (slots q) p.2) := by
      exact A.map_sum fun q j =>
        coeff (idx q) j • chartBasisVecFiber (I := I) x0 j p.2
    _ = ∑ slots : Fin 4 -> Fin (Module.finrank Real E),
        (∏ q : Fin 4, coeff (idx q) (slots q)) *
          A (fun q : Fin 4 =>
            chartBasisVecFiber (I := I) x0 (slots q) p.2) := by
      refine Finset.sum_congr rfl fun slots _ => ?_
      rw [A.map_smul_univ, smul_eq_mul]

end DifferentialGeometry.PDE.RicciFlow
