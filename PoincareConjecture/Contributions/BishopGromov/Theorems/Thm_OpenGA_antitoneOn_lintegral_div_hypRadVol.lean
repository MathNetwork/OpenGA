import Definitions.Def_DifferentialGeometry_ModelRadialVolume
import Definitions.Def_DifferentialGeometry_RadialCrossComparison

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

theorem OpenGA.antitoneOn_lintegral_div_hypRadVol {f : ℝ → ℝ≥0∞} {q R : ℝ} {d : ℕ}
    (hq : 0 ≤ q)
    (hf : AEMeasurable f (volume.restrict (Ioc (0 : ℝ) R)))
    (hcross : CrossAnti R f (fun t => ENNReal.ofReal (hypDensity q d t))) :
    AntitoneOn (fun r => (∫⁻ t in Ioc (0 : ℝ) r, f t) /
      ENNReal.ofReal (hypRadVol q d r)) (Ioc (0 : ℝ) R) := by sorry
