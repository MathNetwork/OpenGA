/-
Top-level entry point for the AltRegularity library — formalization
scaffolding for "Alternative Regularity via Non-Excessive Sweepouts."

# Layered structure (mirroring the paper's sections)

## Common foundation

  * `AltRegularity.Basic`                       — common imports and conventions

## Section 2 — GMT primitives

  * `AltRegularity.GMT.FinitePerimeter`         — finite-perimeter sets,
                                                    reduced boundary, perimOn,
                                                    trichotomy
  * `AltRegularity.GMT.Varifold`                — varifolds, mass, density, support
  * `AltRegularity.GMT.Stationary`              — stationary varifolds
  * `AltRegularity.GMT.Rectifiability`          — rectifiability theorem
                                                    (Allard 1972)

## Section 3 — ONVP and non-excessive sweepouts

  * `AltRegularity.Sweepout.Defs`               — sweepout structure, width
  * `AltRegularity.Sweepout.ONVP`               — Optimal Nested Volume-Parametrized
  * `AltRegularity.Sweepout.MassCancellation`   — cancellation / no-cancellation
  * `AltRegularity.Sweepout.MinMaxLimit`        — min-max varifold convergence
  * `AltRegularity.Sweepout.PullTight`          — Colding–De Lellis pull-tight
  * `AltRegularity.Sweepout.HomotopicMinimization`
                                                — one-sided homotopic minimizer
  * `AltRegularity.Sweepout.Interpolation`      — interpolation lemma (CLS22 1.12)
  * `AltRegularity.Sweepout.NonExcessive`       — Critical, ExcessiveAt,
                                                    IReplacementExists, NonExcessive

## Section 4 — Regularity tools

  * `AltRegularity.Regularity.AlphaStructural`  — S₁, S₂, S₃, the class 𝒮_α
  * `AltRegularity.Regularity.AlphaStructuralVerification`
                                                — Section 7.2 chord-beats-arc
                                                    chain proof: junction ⟹
                                                    I-replacement ⟹
                                                    contradiction
  * `AltRegularity.Regularity.StabilityVerification`
                                                — Section 7.1 chain proof:
                                                    finite hnm + one-sided
                                                    minimization + partition
                                                    of unity ⟹ stability
  * `AltRegularity.Regularity.SmoothRegularity` — smooth regularity for the
                                                    class 𝒮_α (Wickramasekera 2014)

## Section 5 — Density from one-sided minimality

  * `AltRegularity.OneSidedDensity.AlmostMinimizer`
                                                — one-sided ε-AM definitions
  * `AltRegularity.OneSidedDensity.Density`     — density from one-sided AM (Lemma 5.8)

## Section 6 — Integrality

  * `AltRegularity.Integrality.ReducedBoundary` — density ≥ 1 on ∂*Ω (Lemma 6.4)
  * `AltRegularity.Integrality.Theorem`         — Theorem 6.1 (a) (b)

## Section 5.1 — Main implication (formal proof)

  * `AltRegularity.PositiveDensity`             — SweepoutWideReplacement ⟹
                                                    PositiveDensityOnSupport

## Section 7 — Main theorem

  * `AltRegularity.MainTheorem`                 — Theorem 1.1 (a) (b)

## End-to-end existence corollary

  * `AltRegularity.MinMaxExistence`             — paper narrative
                                                    end-to-end: CLS22
                                                    Theorem 2.2 + paper
                                                    Theorem 1.1 ⟹ existence
                                                    of a smooth closed
                                                    embedded minimal
                                                    hypersurface (no-cancel
                                                    unconditional;
                                                    cancel conditional on
                                                    Conjecture 5.9)

The formalization is in progress. Definitions and structural facts that
require GMT infrastructure not yet in Mathlib are recorded as
`theorem ... := by sorry`. No `axiom` declarations are introduced.

Concepts present in the paper but not yet in this scaffold (deferred until
the corresponding primitives are available in Mathlib): the relative
isoperimetric inequality, the Lin-style mass-ratio lower bound, the
De Lellis–Tasnady perimeter-convergence criterion, the sheet decomposition
lemma. Each is a standalone module addition when ready.
-/

import AltRegularity.Basic

import GeometricMeasureTheory.FinitePerimeter
import GeometricMeasureTheory.FlatDistance
import GeometricMeasureTheory.Varifold
import GeometricMeasureTheory.Stationary
import GeometricMeasureTheory.SecondVariation
import GeometricMeasureTheory.TangentCone
import GeometricMeasureTheory.Rectifiability

import Sweepout.Defs
import Sweepout.ONVP
import Sweepout.MassCancellation
import Sweepout.MinMaxLimit
import Sweepout.PullTight
import Sweepout.HomotopicMinimization
import Sweepout.Interpolation
import Sweepout.NonExcessive

import MinimalSurfaceRegularity.AlphaStructural
import AltRegularity.Regularity.AlphaStructuralVerification
import AltRegularity.Regularity.ChordBeatsArc
import MinimalSurfaceRegularity.SmoothRegularity
import AltRegularity.Regularity.StabilityVerification

import AltRegularity.OneSidedDensity.AlmostMinimizer
import AltRegularity.OneSidedDensity.Density

import AltRegularity.Integrality.ReducedBoundary
import AltRegularity.Integrality.PerimeterConvergence
import AltRegularity.Integrality.Theorem

import AltRegularity.PositiveDensity
import AltRegularity.MainTheorem
import AltRegularity.MinMaxExistence
