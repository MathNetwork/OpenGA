import OpenGALib.GeometricMeasureTheory

/-!
# OpenGA entry point for the Prove2Me varifold contributions

The source definitions and proofs are imported from the reusable library.
`Tools/export_varifolds.py` stages the platform's separate definition, theorem
and solution modules without changing their mathematical content.

The mass-energy result shares its integral comparison dependency with the
existing width route. Constructing the geometric CM inputs to that route is
still open; this file does not assert a proof of finite-time extinction.
-/

#check OpenGA.Varifold
#check OpenGA.Varifold.testIntegral_ofParametrization
#check OpenGA.Varifold.ofParametrization_independent_of_lift
#check OpenGA.Varifold.tendsto_weightMeasure_integral
#check OpenGA.Varifold.mass_ofParametrization_le_energy
