import DifferentialGeometry.Analysis.ODE.CInfConvergence
import DifferentialGeometry.Geometry.Metric.TensorInner.MetricGeodesicSpray

set_option autoImplicit false









noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [CompleteSpace E] [FiniteDimensional Real E]



omit [CompleteSpace E] in
theorem normalGeodesicSpray_conv
    {U : Set E} (hU : IsOpen U)
    {g : ℕ → E → E →L[Real] E →L[Real] Real}
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hg_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (g n) U)
    (hgInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    (hg_co : ∀ n x, x ∈ U → IsCoercive (g n x))
    (hgInf_co : ∀ x, x ∈ U → IsCoercive (gInf x))
    (hg_conv : MapCInfConvOnCompacts U g gInf) :
    MapCInfConvOnCompacts (U ×ˢ Set.univ)
      (fun n => MetricKoszul.metricSpray (g n))
      (MetricKoszul.metricSpray gInf) :=
  MetricKoszul.metricSpray_conv hU hg_cd hgInf_cd hg_co hgInf_co hg_conv

set_option maxHeartbeats 700000 in
omit [CompleteSpace E] in
private theorem normalSpray_time_conv
    {U : Set E} (hU : IsOpen U)
    {g : ℕ → E → E →L[Real] E →L[Real] Real}
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hg_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (g n) U)
    (hgInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    (hg_co : ∀ n x, x ∈ U → IsCoercive (g n x))
    (hgInf_co : ∀ x, x ∈ U → IsCoercive (gInf x))
    (hg_conv : MapCInfConvOnCompacts U g gInf) :
    MapCInfConvOnCompacts (Set.univ ×ˢ (U ×ˢ Set.univ))
      (fun (n : ℕ) (q : Real × (E × E)) => MetricKoszul.metricSpray (g n) q.2)
      (fun q : Real × (E × E) => MetricKoszul.metricSpray gInf q.2) := by
  letI : ProperSpace (E × E) := FiniteDimensional.proper Real _
  have hphaseU : IsOpen (U ×ˢ (Set.univ : Set E)) := hU.prod isOpen_univ
  have hspray_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (MetricKoszul.metricSpray (g n)) (U ×ˢ Set.univ) := fun n =>
    MetricKoszul.metricSpray_contDiffOn hU (hg_cd n) (hg_co n)
  have hsprayInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (MetricKoszul.metricSpray gInf) (U ×ˢ Set.univ) :=
    MetricKoszul.metricSpray_contDiffOn hU hgInf_cd hgInf_co
  exact MapCInfConvOnCompacts.comp (isOpen_univ.prod hphaseU) hphaseU
    (mapCInfConv_const (fun q : Real × (E × E) => q.2))
    (normalGeodesicSpray_conv hU hg_cd hgInf_cd hg_co hgInf_co hg_conv)
    (fun _ => contDiff_snd.contDiffOn) contDiff_snd.contDiffOn
    hspray_cd hsprayInf_cd (fun q hq => hq.2) (fun _ q hq => hq.2)

set_option maxHeartbeats 700000 in




omit [CompleteSpace E] in
theorem normalPhase_end_conv
    {U : Set E} (hU : IsOpen U)
    {Q : Set (E × E)} (hQ : IsOpen Q)
    {g : ℕ → E → E →L[Real] E →L[Real] Real}
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hg_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (g n) U)
    (hgInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    (hg_co : ∀ n x, x ∈ U → IsCoercive (g n x))
    (hgInf_co : ∀ x, x ∈ U → IsCoercive (gInf x))
    (hg_conv : MapCInfConvOnCompacts U g gInf)
    {γ : ℕ → (E × E) → Real → E × E}
    {γInf : (E × E) → Real → E × E}
    (hγ : ∀ n q, q ∈ Q →
      γ n q 0 = q ∧ IsIntegralCurveOn (γ n q)
        (fun _ => MetricKoszul.metricSpray (g n)) (Set.Icc 0 1))
    (hγInf : ∀ q, q ∈ Q →
      γInf q 0 = q ∧ IsIntegralCurveOn (γInf q)
        (fun _ => MetricKoszul.metricSpray gInf) (Set.Icc 0 1))
    (hstayInf : ∀ q ∈ Q, ∀ t ∈ Set.Icc (0 : Real) 1,
      (γInf q t).1 ∈ U) :
    MapCInfConvOnCompacts Q
      (fun n q => γ n q 1) (fun q => γInf q 1) := by
  let phaseU : Set (E × E) := U ×ˢ Set.univ
  have hphaseU : IsOpen phaseU := hU.prod isOpen_univ
  have hspray_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (MetricKoszul.metricSpray (g n)) phaseU := fun n =>
    MetricKoszul.metricSpray_contDiffOn hU (hg_cd n) (hg_co n)
  have hsprayInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (MetricKoszul.metricSpray gInf) phaseU :=
    MetricKoszul.metricSpray_contDiffOn hU hgInf_cd hgInf_co
  have hv_conv : MapCInfConvOnCompacts ((Set.univ : Set Real) ×ˢ phaseU)
      (fun (n : ℕ) (q : Real × (E × E)) => MetricKoszul.metricSpray (g n) q.2)
      (fun q : Real × (E × E) => MetricKoszul.metricSpray gInf q.2) := by
    simpa only [phaseU] using
      normalSpray_time_conv hU hg_cd hgInf_cd hg_co hgInf_co hg_conv
  exact MapCInfConvOnCompacts.ode_solutionAt
    (P := E × E) (X := E × E) (A := Q) (J := Set.univ) (V := phaseU)
    (v := fun n _ => MetricKoszul.metricSpray (g n))
    (vInf := fun _ => MetricKoszul.metricSpray gInf)
    (a := fun _ => id) (aInf := id) (γ := γ) (γInf := γInf)
    hQ isOpen_univ hphaseU (by norm_num) (Set.subset_univ _)
    (fun n => (hspray_cd n).comp contDiffOn_snd (fun q hq => hq.2))
    (hsprayInf_cd.comp contDiffOn_snd (fun q hq => hq.2)) hv_conv
    (fun _ => contDiff_id.contDiffOn) contDiff_id.contDiffOn
    (mapCInfConv_const id) hγ hγInf
    (fun q hq t ht => ⟨hstayInf q hq t ht, Set.mem_univ _⟩)

set_option maxHeartbeats 700000 in



theorem normalDiag_end_conv
    {U : Set E} (hU : IsOpen U)
    {Q : Set (E × E)} (hQ : IsOpen Q)
    {g : ℕ → E → E →L[Real] E →L[Real] Real}
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hg_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (g n) U)
    (hgInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    (hg_co : ∀ n x, x ∈ U → IsCoercive (g n x))
    (hgInf_co : ∀ x, x ∈ U → IsCoercive (gInf x))
    (hg_conv : MapCInfConvOnCompacts U g gInf)
    {γ : ℕ → (E × E) → Real → E × E}
    {γInf : (E × E) → Real → E × E}
    (hγ : ∀ n q, q ∈ Q →
      γ n q 0 = q ∧ IsIntegralCurveOn (γ n q)
        (fun _ => MetricKoszul.metricSpray (g n)) (Set.Icc 0 1))
    (hγInf : ∀ q, q ∈ Q →
      γInf q 0 = q ∧ IsIntegralCurveOn (γInf q)
        (fun _ => MetricKoszul.metricSpray gInf) (Set.Icc 0 1))
    (hstay : ∀ n q, q ∈ Q → ∀ t ∈ Set.Icc (0 : Real) 1,
      (γ n q t).1 ∈ U)
    (hstayInf : ∀ q ∈ Q, ∀ t ∈ Set.Icc (0 : Real) 1,
      (γInf q t).1 ∈ U) :
    MapCInfConvOnCompacts Q
      (fun n q => (q.1, (γ n q 1).1))
      (fun q => (q.1, (γInf q 1).1)) := by
  let phaseU : Set (E × E) := U ×ˢ Set.univ
  have hphaseU : IsOpen phaseU := hU.prod isOpen_univ
  have hspray_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (MetricKoszul.metricSpray (g n)) phaseU := fun n =>
    MetricKoszul.metricSpray_contDiffOn hU (hg_cd n) (hg_co n)
  have hsprayInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (MetricKoszul.metricSpray gInf) phaseU :=
    MetricKoszul.metricSpray_contDiffOn hU hgInf_cd hgInf_co
  have hphase := normalPhase_end_conv hU hQ hg_cd hgInf_cd hg_co hgInf_co
    hg_conv hγ hγInf hstayInf
  have hv_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : Real × (E × E) => MetricKoszul.metricSpray (g n) q.2)
      ((Set.univ : Set Real) ×ˢ phaseU) := fun n =>
    (hspray_cd n).comp contDiffOn_snd
      (fun (_q : Real × (E × E)) hq => hq.2)
  have hvInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : Real × (E × E) => MetricKoszul.metricSpray gInf q.2)
      ((Set.univ : Set Real) ×ˢ phaseU) :=
    hsprayInf_cd.comp contDiffOn_snd
      (fun (_q : Real × (E × E)) hq => hq.2)
  have hjoint : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (Function.uncurry (γ n)) (Q ×ˢ Set.Icc (0 : Real) 1) := fun n =>
    DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_solutionFamily_of_stays
      (P := E × E) (E := E × E) (J := Set.univ) (V := phaseU)
      (v := fun _ => MetricKoszul.metricSpray (g n)) (A := Q)
      (a := 0) (b := 1) (a₀ := id) (γ := γ n)
      isOpen_univ hphaseU (hv_cd n)
      hQ (Set.subset_univ _) contDiff_id.contDiffOn (hγ n)
      (fun q hq t ht => ⟨hstay n q hq t ht, Set.mem_univ _⟩)
  have hjointInf : ContDiffOn Real (∞ : WithTop ℕ∞)
      (Function.uncurry γInf) (Q ×ˢ Set.Icc (0 : Real) 1) :=
    DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_solutionFamily_of_stays
      (P := E × E) (E := E × E) (J := Set.univ) (V := phaseU)
      (v := fun _ => MetricKoszul.metricSpray gInf) (A := Q)
      (a := 0) (b := 1) (a₀ := id) (γ := γInf)
      isOpen_univ hphaseU hvInf_cd
      hQ (Set.subset_univ _) contDiff_id.contDiffOn hγInf
      (fun q hq t ht => ⟨hstayInf q hq t ht, Set.mem_univ _⟩)
  have hend_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (fun q => γ n q 1) Q :=
    fun n => (hjoint n).comp
      (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun q hq => ⟨hq, Set.right_mem_Icc.mpr (by norm_num)⟩)
  have hendInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) (fun q => γInf q 1) Q :=
    hjointInf.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun q hq => ⟨hq, Set.right_mem_Icc.mpr (by norm_num)⟩)
  have hpos : MapCInfConvOnCompacts Q
      (fun n q => (γ n q 1).1) (fun q => (γInf q 1).1) :=
    mapCInfConv_clm hQ (ContinuousLinearMap.fst Real E E) hphase
      hend_cd hendInf_cd
  exact mapCInfConv_prodMk hQ
    (mapCInfConv_const (fun q : E × E => q.1)) hpos
    (fun _ => contDiff_fst.contDiffOn) contDiff_fst.contDiffOn
    (fun n => (hend_cd n).fst) hendInf_cd.fst

end HCGCompactness
end DifferentialGeometry
