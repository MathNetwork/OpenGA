import DifferentialGeometry.Analysis.Calculus.MapConvergenceComp
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageComparison

set_option autoImplicit false













noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Filter Topology
open Set Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace





theorem MapCInfConvOnCompacts.pullbackAlong
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup W] [NormedSpace Real W] [ProperSpace W]
    [ProperSpace ((W →L[Real] W →L[Real] Real) × (V →L[Real] W))]
    {U : Set V} {D : Set W} (hU : IsOpen U) (hD : IsOpen D)
    {A : Nat → V → W} {Ainf : V → W}
    {B : Nat → W → (W →L[Real] W →L[Real] Real)}
    {Binf : W → (W →L[Real] W →L[Real] Real)}
    (hA : MapCInfConvOnCompacts U A Ainf)
    (hB : MapCInfConvOnCompacts D B Binf)
    (hAc : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (A n) U)
    (hAinfC : ContDiffOn Real (∞ : WithTop ℕ∞) Ainf U)
    (hBc : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (B n) D)
    (hBinfC : ContDiffOn Real (∞ : WithTop ℕ∞) Binf D)
    (hmapInf : Set.MapsTo Ainf U D)
    (hmap : ∀ n, Set.MapsTo (A n) U D) :
    MapCInfConvOnCompacts U
      (fun n z ↦ _root_.DifferentialGeometry.HCGCompactness.pullbackForm
        (B n (A n z), fderiv Real (A n) z))
      (fun z ↦ _root_.DifferentialGeometry.HCGCompactness.pullbackForm
        (Binf (Ainf z), fderiv Real Ainf z)) := by
  have hBA : MapCInfConvOnCompacts U
      (fun n z ↦ B n (A n z)) (fun z ↦ Binf (Ainf z)) :=
    MapCInfConvOnCompacts.comp hU hD hA hB hAc hAinfC hBc hBinfC
      hmapInf hmap
  have hDA : MapCInfConvOnCompacts U
      (fun n z ↦ fderiv Real (A n) z) (fun z ↦ fderiv Real Ainf z) :=
    hA.fderivOn hU hAc hAinfC
  have hBAc : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z ↦ B n (A n z)) U := by
    intro n
    simpa only [Function.comp_def] using
      ContDiffOn.comp (hBc n) (hAc n) (hmap n)
  have hBAinfC : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z ↦ Binf (Ainf z)) U := by
    simpa only [Function.comp_def] using
      ContDiffOn.comp hBinfC hAinfC hmapInf
  have hDAc : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z ↦ fderiv Real (A n) z) U := by
    intro n z hz
    exact (((hAc n).contDiffAt (hU.mem_nhds hz)).fderiv_right
      (m := (∞ : WithTop ℕ∞)) (by simp)).contDiffWithinAt
  have hDAinfC : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z ↦ fderiv Real Ainf z) U := by
    intro z hz
    exact ((hAinfC.contDiffAt (hU.mem_nhds hz)).fderiv_right
      (m := (∞ : WithTop ℕ∞)) (by simp)).contDiffWithinAt
  exact hBA.pullbackForm hU hDA hBAc hBAinfC hDAc hDAinfC

set_option synthInstance.maxHeartbeats 800000 in


theorem pullback_sub_norm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (B₀ B₁ : V →L[Real] V →L[Real] Real) (A : V →L[Real] V) :
    ‖_root_.DifferentialGeometry.HCGCompactness.pullbackForm (B₁, A) - B₀‖ ≤
      ‖B₁‖ * ‖A - ContinuousLinearMap.id Real V‖ * (1 + ‖A‖) + ‖B₁ - B₀‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w ↦ ?_
  simpa only [ContinuousLinearMap.sub_apply,
    _root_.DifferentialGeometry.HCGCompactness.pullbackForm_apply,
    Real.norm_eq_abs, mul_assoc] using
      (bilinPerturbTri (B₀ := B₀) (B₁ := B₁) (A := A) v w)

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in



theorem HasStageJetData.coeff_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    (R : Real) (hRr : R < r) (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      ∀ alpha : LiveSlot L inp.pack r, ∀ z ∈ C0 alpha,
        let Lphi := L.subseq hphi
        let Yk := X.obj (Lphi.φ k)
        let Yl := X.obj (Lphi.φ l)
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : TopologicalSpace Yl.M := Yl.topology
        letI : ChartedSpace H Yl.M := Yl.charted
        letI : IsManifold I ∞ Yl.M := Yl.smooth
        letI : T2Space Yl.M := Yl.t2
        letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
        let ck := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
        let cl := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
        let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric ck
        let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric cl
        let Fkl := fun w ↦
          chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm w))
        z ∈ interior (C0 alpha) →
        chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k →
          ‖_root_.DifferentialGeometry.HCGCompactness.pullbackForm
              (normalCoordMetric (I := I) Yl cl (Fkl z),
                fderiv Real Fkl z) -
            normalCoordMetric (I := I) Yk ck z‖ ≤ eps := by
  classical
  letI : NormedAddCommGroup (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedSpace
  rcases hstage with ⟨hdata, hmetric, hjets, _hbase⟩
  have hshape := hdata
  dsimp only [HasSuppConvData] at hshape
  rcases hshape with
    ⟨_hopen, _hU8, hC0compact, hC1compact, hC01, hC1U, _hrest⟩
  let Lphi := L.subseq hphi
  let tau : Real := min 1 (eps / 10)
  have htau : 0 < tau := by
    dsimp only [tau]
    exact lt_min zero_lt_one (div_pos heps (by norm_num))
  have htau_one : tau ≤ 1 := min_le_left _ _
  have htau_eps : tau ≤ eps / 10 := min_le_right _ _
  choose rho hrho hthick using fun alpha ↦
    (hC0compact alpha).exists_cthickening_subset_open
      isOpen_interior (hC01 alpha)
  let metricScale : Real := inp.normalBounds.metricC 1 + 1
  have hmetricScale : 0 < metricScale := by
    dsimp only [metricScale]
    linarith [inp.normalBounds.metricC_nonneg 1]
  let jetTol : LiveSlot L inp.pack r → Real := fun alpha ↦
    min tau (min (rho alpha) (tau / metricScale))
  have hjetTol : ∀ alpha, 0 < jetTol alpha := by
    intro alpha
    dsimp only [jetTol]
    exact lt_min htau (lt_min (hrho alpha)
      (div_pos htau hmetricScale))
  have hjetAll : ∀ alpha : LiveSlot L inp.pack r,
      HasStageJetTail (I := I) inp P L hr phi hphi hconn C0 R 1
        (jetTol alpha) := fun alpha ↦
    hjets R hRr 1 (jetTol alpha) (hjetTol alpha)
  choose Njet hNjet using hjetAll
  have hmetricCP : ∀ alpha : LiveSlot L inp.pack r,
      MapCPConvOn (C1 alpha) 0
        (fun n ↦ normalCoordMetric (I := I)
          (X.obj (Lphi.φ n))
          (seqCenterD inp.decay P Lphi n (alpha.1 : Nat)))
        (gInf alpha) := by
    intro alpha
    exact (hmetric alpha).2.2.1 (C1 alpha) (hC1compact alpha)
      (hmetric alpha).1 0
  choose Nmetric hNmetric using fun alpha ↦ hmetricCP alpha tau htau
  letI := Fintype.ofFinite (LiveSlot L inp.pack r)
  let Nalpha : LiveSlot L inp.pack r → Nat := fun alpha ↦
    max (Njet alpha) (Nmetric alpha)
  refine ⟨Finset.univ.sup Nalpha, ?_⟩
  intro k hk l hl alpha z hzC0
  dsimp only
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : T2Space Yl.M := Yl.t2
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  let ck := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let cl := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric ck
  let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric cl
  let Fkl := fun w ↦
    chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm w))
  intro hzInt hxR
  have hAlpha : Nalpha alpha ≤ Finset.univ.sup Nalpha :=
    Finset.le_sup (f := Nalpha) (Finset.mem_univ alpha)
  have hkJet : Njet alpha ≤ k :=
    (Nat.le_max_left _ _).trans (hAlpha.trans hk)
  have hlJet : Njet alpha ≤ l :=
    (Nat.le_max_left _ _).trans (hAlpha.trans hl)
  have hkMetric : Nmetric alpha ≤ k :=
    (Nat.le_max_right _ _).trans (hAlpha.trans hk)
  have hlMetric : Nmetric alpha ≤ l :=
    (Nat.le_max_right _ _).trans (hAlpha.trans hl)
  have hjet := hNjet alpha k hkJet l hlJet alpha z hzC0 hzInt hxR
  have hFclose : dist (Fkl z) z ≤ jetTol alpha := by
    simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, id_eq,
      dist_eq_norm, Fkl, chiK, chiL, ck, cl, Yk, Yl, Lphi] using
        hjet.2.2 0 (by omega)
  have hjet_rho : jetTol alpha ≤ rho alpha :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hFthick : Fkl z ∈ Metric.cthickening (rho alpha) (C0 alpha) :=
    Metric.mem_cthickening_of_dist_le (Fkl z) z (rho alpha) (C0 alpha)
      hzC0 (hFclose.trans hjet_rho)
  have hFC1 : Fkl z ∈ C1 alpha :=
    interior_subset (hthick alpha hFthick)
  have hzC1 : z ∈ C1 alpha := interior_subset (hC01 alpha hzC0)
  have hsource :
      ‖normalCoordMetric (I := I) Yk ck z - gInf alpha z‖ ≤ tau := by
    simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, Yk, ck, Lphi] using
      hNmetric alpha k hkMetric 0 le_rfl z hzC1
  have htarget :
      ‖normalCoordMetric (I := I) Yl cl z - gInf alpha z‖ ≤ tau := by
    simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, Yl, cl, Lphi] using
      hNmetric alpha l hlMetric 0 le_rfl z hzC1
  have hzBall : z ∈ Metric.closedBall z (rho alpha) := by
    simpa only [Metric.mem_closedBall, dist_self] using (hrho alpha).le
  have hFBall : Fkl z ∈ Metric.closedBall z (rho alpha) := by
    exact hFclose.trans hjet_rho
  have hsegU : segment Real z (Fkl z) ⊆ U alpha := by
    intro q hq
    have hqBall :=
      (convex_closedBall z (rho alpha)).segment_subset hzBall hFBall hq
    have hqThick : q ∈ Metric.cthickening (rho alpha) (C0 alpha) :=
      Metric.mem_cthickening_of_dist_le q z (rho alpha) (C0 alpha)
        hzC0 hqBall
    exact hC1U alpha (interior_subset (hthick alpha hqThick))
  have hgeomL := hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf l alpha
  let G := normalCoordMetric (I := I) Yl cl
  have hGsm : ContDiffOn Real (∞ : WithTop ℕ∞) G (U alpha) :=
    (normalCoordMetric_contDiffOn_expBall (I := I) Yl cl).mono hgeomL.2.1
  have hGdiff : ∀ q ∈ segment Real z (Fkl z), DifferentiableAt Real G q := by
    intro q hq
    have hqU := hsegU hq
    exact ((hGsm q hqU).contDiffAt ((_hopen alpha).mem_nhds hqU)).differentiableAt
      (by simp)
  have hGbound : ∀ q ∈ segment Real z (Fkl z),
      ‖fderiv Real G q‖ ≤ inp.normalBounds.metricC 1 := by
    intro q hq
    rw [← norm_iteratedFDeriv_one (f := G)]
    exact inp.normalBounds.metric_deriv (Lphi.φ l) 1 cl q
      (hgeomL.1 (hsegU hq))
  have hspatial :
      ‖normalCoordMetric (I := I) Yl cl (Fkl z) -
          normalCoordMetric (I := I) Yl cl z‖ ≤
        inp.normalBounds.metricC 1 * ‖Fkl z - z‖ := by
    simpa only [G] using
      (convex_segment z (Fkl z)).norm_image_sub_le_of_norm_fderiv_le
        hGdiff hGbound (left_mem_segment Real z (Fkl z))
          (right_mem_segment Real z (Fkl z))
  have hspatial_tau :
      ‖normalCoordMetric (I := I) Yl cl (Fkl z) -
          normalCoordMetric (I := I) Yl cl z‖ ≤ tau := by
    have hnormF : ‖Fkl z - z‖ ≤ jetTol alpha := by
      simpa only [dist_eq_norm] using hFclose
    have hjetScale : jetTol alpha ≤ tau / metricScale :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hfrac : inp.normalBounds.metricC 1 *
        (tau / metricScale) ≤ tau := by
      rw [show inp.normalBounds.metricC 1 * (tau / metricScale) =
        (inp.normalBounds.metricC 1 * tau) / metricScale by ring]
      apply (div_le_iff₀ hmetricScale).2
      dsimp only [metricScale]
      nlinarith [mul_nonneg (inp.normalBounds.metricC_nonneg 1) htau.le]
    exact hspatial.trans <|
      (mul_le_mul_of_nonneg_left (hnormF.trans hjetScale)
        (inp.normalBounds.metricC_nonneg 1)).trans hfrac
  have hmetricDiff :
      ‖normalCoordMetric (I := I) Yl cl (Fkl z) -
          normalCoordMetric (I := I) Yk ck z‖ ≤ 3 * tau := by
    calc
      ‖normalCoordMetric (I := I) Yl cl (Fkl z) -
          normalCoordMetric (I := I) Yk ck z‖ =
          ‖(normalCoordMetric (I := I) Yl cl (Fkl z) -
              normalCoordMetric (I := I) Yl cl z) +
            (normalCoordMetric (I := I) Yl cl z - gInf alpha z) +
            (gInf alpha z - normalCoordMetric (I := I) Yk ck z)‖ := by
              congr 1
              abel
      _ ≤ ‖normalCoordMetric (I := I) Yl cl (Fkl z) -
              normalCoordMetric (I := I) Yl cl z‖ +
            ‖normalCoordMetric (I := I) Yl cl z - gInf alpha z‖ +
            ‖gInf alpha z - normalCoordMetric (I := I) Yk ck z‖ := by
              calc
                ‖(normalCoordMetric (I := I) Yl cl (Fkl z) -
                      normalCoordMetric (I := I) Yl cl z) +
                    (normalCoordMetric (I := I) Yl cl z - gInf alpha z) +
                    (gInf alpha z - normalCoordMetric (I := I) Yk ck z)‖ ≤
                    ‖(normalCoordMetric (I := I) Yl cl (Fkl z) -
                        normalCoordMetric (I := I) Yl cl z) +
                      (normalCoordMetric (I := I) Yl cl z - gInf alpha z)‖ +
                    ‖gInf alpha z - normalCoordMetric (I := I) Yk ck z‖ :=
                      norm_add_le _ _
                _ ≤ (‖normalCoordMetric (I := I) Yl cl (Fkl z) -
                        normalCoordMetric (I := I) Yl cl z‖ +
                      ‖normalCoordMetric (I := I) Yl cl z - gInf alpha z‖) +
                    ‖gInf alpha z - normalCoordMetric (I := I) Yk ck z‖ :=
                      add_le_add (norm_add_le _ _) le_rfl
      _ ≤ tau + tau + tau := by
            exact add_le_add (add_le_add hspatial_tau htarget)
              (by simpa only [norm_sub_rev] using hsource)
      _ = 3 * tau := by ring
  have hEquiv : NormalCoordMetricEquivOn (I := I) Yl cl (U alpha) := by
    intro q hq v
    exact inp.normalBounds.metric_equiv (Lphi.φ l) cl q (hgeomL.1 hq) v
  have hFU : Fkl z ∈ U alpha := hC1U alpha hFC1
  have hmetricNorm :
      ‖normalCoordMetric (I := I) Yl cl (Fkl z)‖ ≤ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound₂ _ (by norm_num) fun v w ↦ ?_
    simpa only [Real.norm_eq_abs] using
      hEquiv.abs_apply_le hFU v w
  have hderiv :
      ‖fderiv Real Fkl z - ContinuousLinearMap.id Real E‖ ≤
        jetTol alpha := by
    have hnear := neumannOfDerivNorm (hjet.2.1.differentiableAt (by simp))
      (hjet.2.2 1 le_rfl)
    simpa only [norm_sub_rev] using hnear
  have hderiv_tau :
      ‖fderiv Real Fkl z - ContinuousLinearMap.id Real E‖ ≤ tau :=
    hderiv.trans (min_le_left _ _)
  have hfderivNorm : ‖fderiv Real Fkl z‖ ≤ 1 + tau := by
    calc
      ‖fderiv Real Fkl z‖ =
          ‖ContinuousLinearMap.id Real E +
            (fderiv Real Fkl z - ContinuousLinearMap.id Real E)‖ := by
              congr 1
              abel
      _ ≤ ‖ContinuousLinearMap.id Real E‖ +
          ‖fderiv Real Fkl z - ContinuousLinearMap.id Real E‖ := norm_add_le _ _
      _ ≤ 1 + tau := add_le_add ContinuousLinearMap.norm_id_le hderiv_tau
  calc
    ‖_root_.DifferentialGeometry.HCGCompactness.pullbackForm
          (normalCoordMetric (I := I) Yl cl (Fkl z), fderiv Real Fkl z) -
        normalCoordMetric (I := I) Yk ck z‖ ≤
        ‖normalCoordMetric (I := I) Yl cl (Fkl z)‖ *
            ‖fderiv Real Fkl z - ContinuousLinearMap.id Real E‖ *
              (1 + ‖fderiv Real Fkl z‖) +
          ‖normalCoordMetric (I := I) Yl cl (Fkl z) -
            normalCoordMetric (I := I) Yk ck z‖ :=
      pullback_sub_norm _ _ _
    _ ≤ 2 * tau * (2 + tau) + 3 * tau := by
      have hfactor : 1 + ‖fderiv Real Fkl z‖ ≤ 2 + tau := by
        linarith [hfderivNorm]
      have hprod :
          ‖normalCoordMetric (I := I) Yl cl (Fkl z)‖ *
              ‖fderiv Real Fkl z - ContinuousLinearMap.id Real E‖ *
                (1 + ‖fderiv Real Fkl z‖) ≤
            2 * tau * (2 + tau) := by
        gcongr
      exact add_le_add hprod hmetricDiff
    _ ≤ eps := by
      have htau_sq : tau ^ 2 ≤ tau := by nlinarith [sq_nonneg tau]
      nlinarith




theorem HasStageJetData.chart_conv
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    (R : Real) (hRr : R < r) (alpha : LiveSlot L inp.pack r)
    (V : Set E) (hVint : V ⊆ interior (C0 alpha))
    (kn ln : Nat → Nat)
    (hkn : Tendsto kn atTop atTop) (hln : Tendsto ln atTop atTop)
    (hsource : ∀ᶠ n in atTop,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ (kn n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      Set.MapsTo
        (NormalCoordinates.normalChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm
        V (Lphi.hatSourceBall inp.decay P R (kn n))) :
    MapCInfConvOnCompacts V
      (fun n z ↦
        let Lphi := L.subseq hphi
        let Yk := X.obj (Lphi.φ (kn n))
        let Yl := X.obj (Lphi.φ (ln n))
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : TopologicalSpace Yl.M := Yl.topology
        letI : ChartedSpace H Yl.M := Yl.charted
        letI : IsManifold I ∞ Yl.M := Yl.smooth
        letI : T2Space Yl.M := Yl.t2
        letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
        let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))
        let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
          (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
        chiL (stageComparisonMap inp P Lphi r hr hconn (kn n) (ln n)
          (chiK.symm z))) id := by
  rcases hstage with ⟨_hdata, _hmetric, hjets, _hbase⟩
  intro K hK hKV p eps heps
  obtain ⟨Njet, hNjet⟩ := hjets R hRr p eps heps
  obtain ⟨Nk, hNk⟩ := eventually_atTop.mp (hkn.eventually_ge_atTop Njet)
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp (hln.eventually_ge_atTop Njet)
  obtain ⟨Ns, hNs⟩ := eventually_atTop.mp hsource
  refine ⟨max (max Nk Nl) Ns, ?_⟩
  intro n hn j hj z hzK
  have hnK : Nk ≤ n := (le_max_left Nk Nl).trans
    ((le_max_left (max Nk Nl) Ns).trans hn)
  have hnL : Nl ≤ n := (le_max_right Nk Nl).trans
    ((le_max_left (max Nk Nl) Ns).trans hn)
  have hnS : Ns ≤ n := (le_max_right (max Nk Nl) Ns).trans hn
  have hzV : z ∈ V := hKV hzK
  have hzInt : z ∈ interior (C0 alpha) := hVint hzV
  have hjet := hNjet (kn n) (hNk n hnK) (ln n) (hNl n hnL)
    alpha z (interior_subset hzInt)
  have hsrc := hNs n hnS hzV
  exact (hjet hzInt hsrc).2.2 j hj





theorem HasStageJetData.pb_conv
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    (R : Real) (hRr : R < r) (alpha : LiveSlot L inp.pack r)
    (V W : Set E) (hVopen : IsOpen V) (hVcompact : IsCompact (closure V))
    (hVW : closure V ⊆ W) (hWint : W ⊆ interior (C0 alpha))
    (kn ln : Nat → Nat)
    (hkn : Tendsto kn atTop atTop) (hln : Tendsto ln atTop atTop)
    (hsource : ∀ᶠ n in atTop,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ (kn n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      Set.MapsTo
        (NormalCoordinates.normalChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm
        W (Lphi.hatSourceBall inp.decay P R (kn n))) :
    let Lphi := L.subseq hphi
    let A : Nat → E → E := fun n z ↦
      let Yk := X.obj (Lphi.φ (kn n))
      let Yl := X.obj (Lphi.φ (ln n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))
      let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
      chiL (stageComparisonMap inp P Lphi r hr hconn (kn n) (ln n)
        (chiK.symm z))
    let B : Nat → E → (E →L[Real] E →L[Real] Real) := fun n ↦
      normalCoordMetric (I := I) (X.obj (Lphi.φ (ln n)))
        (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
    MapCInfConvOnCompacts V
      (fun n z ↦ _root_.DifferentialGeometry.HCGCompactness.pullbackForm
        (B n (A n z), fderiv Real (A n) z))
      (gInf alpha) := by
  classical
  letI : NormedAddCommGroup (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedSpace
  dsimp only
  let Lphi := L.subseq hphi
  let A : Nat → E → E := fun n z ↦
    let Yk := X.obj (Lphi.φ (kn n))
    let Yl := X.obj (Lphi.φ (ln n))
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))
    let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
    chiL (stageComparisonMap inp P Lphi r hr hconn (kn n) (ln n)
      (chiK.symm z))
  let B : Nat → E → (E →L[Real] E →L[Real] Real) := fun n ↦
    normalCoordMetric (I := I) (X.obj (Lphi.φ (ln n)))
      (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
  change MapCInfConvOnCompacts V
    (fun n z ↦ _root_.DifferentialGeometry.HCGCompactness.pullbackForm
      (B n (A n z), fderiv Real (A n) z)) (gInf alpha)
  rcases hstage with ⟨hdata, hmetric, hjets, _hbase⟩
  have hshape := hdata
  dsimp only [HasSuppConvData] at hshape
  rcases hshape with
    ⟨_hopen, _hU8, _hC0compact, _hC1compact, hC01, _hC1U, _hrest⟩
  let Ralpha : Real := L.rInf (alpha.1 : Nat) + 1
  let D : Set E := Metric.ball (0 : E) (inp.normalRadius.phaseRadius Ralpha)
  rcases hmetric alpha with ⟨hC1D, hgInf, hBconv, _hgequiv⟩
  have hWD : W ⊆ D := by
    intro z hz
    exact hC1D (interior_subset (hC01 alpha (interior_subset (hWint hz))))
  have hVD : V ⊆ D :=
    subset_closure.trans (hVW.trans hWD)
  have hclosureD : closure V ⊆ D := hVW.trans hWD
  obtain ⟨rho, hrho, hthick⟩ :=
    hVcompact.exists_cthickening_subset_open Metric.isOpen_ball hclosureD
  have hAconvW : MapCInfConvOnCompacts W A id := by
    simpa only [A, Lphi] using
      HasStageJetData.chart_conv (I := I) inp P L hr phi hphi hconn
        U C0 C1 aInf Jinf Jbarinf gInf
        ⟨hdata, hmetric, hjets, _hbase⟩ R hRr alpha W hWint
        kn ln hkn hln hsource
  have hAconv : MapCInfConvOnCompacts V A id := by
    intro K hK hKV p
    exact hAconvW K hK (hKV.trans (subset_closure.trans hVW)) p
  obtain ⟨Nclose, hNclose⟩ :=
    hAconvW (closure V) hVcompact hVW 0 (rho / 2) (by positivity)
  obtain ⟨Njet, hNjet⟩ := hjets R hRr 0 1 (by norm_num)
  have hcenters : ∀ᶠ n in atTop,
      inp.decay.dist (Lphi.φ (ln n))
        (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
        (X.obj (Lphi.φ (ln n))).basepoint < Ralpha := by
    have hall := liveCenters_rInf inp.decay P inp.realizes Lphi inp.pack r
    filter_upwards [hln.eventually hall] with n hn
    simpa only [Ralpha, Lphi, NetLimitData.subseq] using hn alpha
  have hgood : ∀ᶠ n in atTop,
      ContDiffOn Real (∞ : WithTop ℕ∞) (A n) V ∧
      Set.MapsTo (A n) V D ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) (B n) D := by
    filter_upwards [hkn.eventually_ge_atTop Njet,
      hln.eventually_ge_atTop Njet, hsource, hcenters,
      eventually_atTop.2 ⟨Nclose, hNclose⟩] with n hnk hnl hsrc hcenter hclose
    have hAcd : ContDiffOn Real (∞ : WithTop ℕ∞) (A n) V := by
      intro z hzV
      have hzW : z ∈ W := hVW (subset_closure hzV)
      have hzInt : z ∈ interior (C0 alpha) := hWint hzW
      have hjet := hNjet (kn n) hnk (ln n) hnl alpha z
        (interior_subset hzInt)
      have hsrcz := hsrc hzW
      simpa only [A, Lphi] using (hjet hzInt hsrcz).2.1.contDiffWithinAt
    have hAmap : Set.MapsTo (A n) V D := by
      intro z hzV
      have hzClosure : z ∈ closure V := subset_closure hzV
      have hzero := hclose 0 le_rfl z hzClosure
      have hdist : dist (A n z) z ≤ rho / 2 := by
        simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, id_eq,
          dist_eq_norm, A, Lphi] using hzero
      have hdistRho : dist (A n z) z < rho := by linarith
      exact hthick (Metric.mem_cthickening_of_dist_le
        (A n z) z rho (closure V) hzClosure hdistRho.le)
    have hBcd : ContDiffOn Real (∞ : WithTop ℕ∞) (B n) D := by
      let Yl := X.obj (Lphi.φ (ln n))
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let cl := seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat)
      have hquarter := inp.normalRadius.phaseRadius_exp hcenter.le
      have hDexp : D ⊆ Metric.ball (0 : E)
          (expMapC2Radius (I := I) Yl.metric cl) := by
        have hquarter' : D ⊆ Metric.ball (0 : E)
            (expMapC2Radius (I := I) Yl.metric cl / 4) := by
          simpa only [D, Ralpha, Yl, cl, Lphi] using hquarter
        exact hquarter'.trans (Metric.ball_subset_ball (by
          nlinarith [expMapC2Radius_pos (I := I) Yl.metric cl]))
      simpa only [B, Yl, cl, Lphi] using
        (normalCoordMetric_contDiffOn_expBall (I := I) Yl cl).mono hDexp
    exact ⟨hAcd, hAmap, hBcd⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgood
  let Ap : Nat → E → E := fun n ↦ if N ≤ n then A n else id
  let Bp : Nat → E → (E →L[Real] E →L[Real] Real) := fun n ↦
    if N ≤ n then B n else gInf alpha
  have hApconv : MapCInfConvOnCompacts V Ap id := by
    apply hAconv.congr_eventually hVopen
    · filter_upwards [eventually_atTop.2 ⟨N, fun n hn ↦ hn⟩] with n hn
      intro z _hz
      simp only [Ap, if_pos hn]
    · exact Set.eqOn_refl id V
  have hBpconv : MapCInfConvOnCompacts D Bp (gInf alpha) := by
    have hBsub : MapCInfConvOnCompacts D B (gInf alpha) := by
      simpa only [B, D, Ralpha, Lphi] using
        hBconv.comp_tendsto_atTop hln
    apply hBsub.congr_eventually Metric.isOpen_ball
    · filter_upwards [eventually_atTop.2 ⟨N, fun n hn ↦ hn⟩] with n hn
      intro z _hz
      simp only [Bp, if_pos hn]
    · exact Set.eqOn_refl (gInf alpha) D
  have hApc : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (Ap n) V := by
    intro n
    by_cases hn : N ≤ n
    · simpa only [Ap, if_pos hn] using (hN n hn).1
    · simpa only [Ap, if_neg hn] using
        (contDiff_id : ContDiff Real (∞ : WithTop ℕ∞) (id : E → E)).contDiffOn
  have hBpc : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (Bp n) D := by
    intro n
    by_cases hn : N ≤ n
    · simpa only [Bp, if_pos hn] using (hN n hn).2.2
    · simpa only [Bp, if_neg hn] using hgInf
  have hApmap : ∀ n, Set.MapsTo (Ap n) V D := by
    intro n
    by_cases hn : N ≤ n
    · simpa only [Ap, if_pos hn] using (hN n hn).2.1
    · simpa only [Ap, if_neg hn] using hVD
  have hpb := MapCInfConvOnCompacts.pullbackAlong
    (V := E) (W := E) hVopen Metric.isOpen_ball
      hApconv hBpconv hApc
      (contDiff_id : ContDiff Real (∞ : WithTop ℕ∞) (id : E → E)).contDiffOn
      hBpc hgInf hVD hApmap
  apply hpb.congr_eventually hVopen
  · filter_upwards [eventually_atTop.2 ⟨N, fun n hn ↦ hn⟩] with n hn
    intro z _hz
    simp only [Ap, Bp, if_pos hn]
  · intro z _hz
    change gInf alpha z =
      _root_.DifferentialGeometry.HCGCompactness.pullbackForm
        (gInf alpha z, fderiv Real id z)
    rw [fderiv_id]
    ext v w
    rfl




theorem HasStageJetData.pb_jet_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    (R : Real) (hRr : R < r) (alpha : LiveSlot L inp.pack r)
    (V W K : Set E) (hVopen : IsOpen V)
    (hVcompact : IsCompact (closure V))
    (hVW : closure V ⊆ W) (hWint : W ⊆ interior (C0 alpha))
    (hK : IsCompact K) (hKV : K ⊆ V)
    (hsource : ∃ N : Nat, ∀ k ≥ N,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      Set.MapsTo
        (NormalCoordinates.normalChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm
        W (Lphi.hatSourceBall inp.decay P R k))
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    let Lphi := L.subseq hphi
    let A : Nat → Nat → E → E := fun k l z ↦
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
      chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z))
    let B : Nat → E → (E →L[Real] E →L[Real] Real) := fun l ↦
      normalCoordMetric (I := I) (X.obj (Lphi.φ l))
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    let Q : Nat → Nat → E → (E →L[Real] E →L[Real] Real) :=
      fun k l z ↦ _root_.DifferentialGeometry.HCGCompactness.pullbackForm
        (B l (A k l z), fderiv Real (A k l) z)
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ j ≤ p, ∀ z ∈ K,
      mapDerivNorm j (Q k l) (gInf alpha) z ≤ eps := by
  dsimp only
  let Lphi := L.subseq hphi
  let A : Nat → Nat → E → E := fun k l z ↦
    let Yk := X.obj (Lphi.φ k)
    let Yl := X.obj (Lphi.φ l)
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z))
  let B : Nat → E → (E →L[Real] E →L[Real] Real) := fun l ↦
    normalCoordMetric (I := I) (X.obj (Lphi.φ l))
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
  let Q : Nat → Nat → E → (E →L[Real] E →L[Real] Real) :=
    fun k l z ↦ _root_.DifferentialGeometry.HCGCompactness.pullbackForm
      (B l (A k l z), fderiv Real (A k l) z)
  change ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ j ≤ p, ∀ z ∈ K,
    mapDerivNorm j (Q k l) (gInf alpha) z ≤ eps
  apply mapCInf_pair_tail (U := V) (Φ := Q) (Φinf := gInf alpha)
    ?_ hK hKV p eps heps
  intro kn ln hkn hln
  obtain ⟨Ns, hNs⟩ := hsource
  have hsourceSeq : ∀ᶠ n in atTop,
      let Yk := X.obj (Lphi.φ (kn n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      Set.MapsTo
        (NormalCoordinates.normalChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm
        W (Lphi.hatSourceBall inp.decay P R (kn n)) := by
    filter_upwards [hkn.eventually_ge_atTop Ns] with n hn
    simpa only [Lphi] using hNs (kn n) hn
  simpa only [Q, A, B, Lphi] using
    HasStageJetData.pb_conv (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf hstage R hRr alpha V W
      hVopen hVcompact hVW hWint kn ln hkn hln hsourceSeq

end HCGCompactness
end DifferentialGeometry
