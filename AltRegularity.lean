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
                                                — Section 7 chord-beats-arc
                                                    chain proof: junction ⟹
                                                    I-replacement ⟹
                                                    contradiction
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

import AltRegularity.GMT.FinitePerimeter
import AltRegularity.GMT.Varifold
import AltRegularity.GMT.Stationary
import AltRegularity.GMT.Rectifiability

import AltRegularity.Sweepout.Defs
import AltRegularity.Sweepout.ONVP
import AltRegularity.Sweepout.MassCancellation
import AltRegularity.Sweepout.MinMaxLimit
import AltRegularity.Sweepout.PullTight
import AltRegularity.Sweepout.HomotopicMinimization
import AltRegularity.Sweepout.Interpolation
import AltRegularity.Sweepout.NonExcessive

import AltRegularity.Regularity.AlphaStructural
import AltRegularity.Regularity.AlphaStructuralVerification
import AltRegularity.Regularity.ChordBeatsArc
import AltRegularity.Regularity.SmoothRegularity

import AltRegularity.OneSidedDensity.AlmostMinimizer
import AltRegularity.OneSidedDensity.Density

import AltRegularity.Integrality.ReducedBoundary
import AltRegularity.Integrality.PerimeterConvergence
import AltRegularity.Integrality.Theorem

import AltRegularity.PositiveDensity
import AltRegularity.MainTheorem
