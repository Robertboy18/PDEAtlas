/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.WeakSolution.Classical.MovingInterface.Integral
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import PDE.Hyperbolic.ConservationLaw.System.WeakSolution.Classical.Equivalence
import PDE.Hyperbolic.ConservationLaw.Scalar.Shock.Trace

/-!
# Weak and piecewise classical solutions across a C¹ graph

For a C¹ flux, two globally C¹ branches, and an arbitrary C¹ graph `x = s(t)`,
the joined field is a weak solution on all spacetime if and only if both
branches solve the classical PDE on their respective open sides and their
traces satisfy Rankine–Hugoniot with velocity `s'(t)` at every time.

The forward implication derives both bulk equations by restricting the
weak formulation, then derives the jump condition by testing on the graph and
applying the fundamental lemma. The converse uses the derived moving-graph integral. Continuity
gives all the local integrability needed.

This is an interior spacetime theorem for branches admitting global C¹
extensions. It has no initial boundary or entropy condition. The forward implication is the
derivation (14)-(20) of the Rankine–Hugoniot condition in Evans, §11.1.1, which parallels the
scalar calculation (5)-(12) of §3.4.1(a). Evans writes jumps left minus right,
`[[u]] = u_l - u_r`; we write them right minus left, which gives the same condition (20).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.1, equations (12)-(20); §3.4.1(a), equations (5)-(12).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions

attribute [local instance] Classical.propDecidable

namespace PDE.Hyperbolic.ConservationLaw.System.MovingInterface

open Scalar.Shock (interface rightRegion)

variable {m : ℕ} {flux : ℝ^m → ℝ^m} {s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ^m}

/-- Weakness of the joined field forces both C¹ branches to satisfy the
classical system on the open side where each branch is used. -/
theorem classical_on_sides_of_isWeakSolution (hflux : ContDiff ℝ 1 flux) (hs : Continuous s)
    (hL : ContDiff ℝ 1 uL) (hR : ContDiff ℝ 1 uR)
    (hw : IsWeakSolution flux ⊤ ((rightRegion s).piecewise uR uL)) :
    IsClassicalSolutionOn flux {p | p 1 < s (p 0)} uL ∧
      IsClassicalSolutionOn flux (rightRegion s) uR := by
  let left : Opens ℝ^2 := ⟨{p | p 1 < s (p 0)}, isOpen_lt (EuclideanSpace.proj 1).continuous
      (hs.comp (EuclideanSpace.proj 0).continuous)⟩
  let right : Opens ℝ^2 := ⟨rightRegion s, Scalar.Shock.isOpen_rightRegion hs⟩
  have hwL : IsWeakSolution flux left uL := by
    apply (hw.mono_domain (U := left) le_top).congr_ae_restrict
    filter_upwards [ae_restrict_mem left.isOpen.measurableSet] with p hp
    apply piecewise_eq_of_notMem
    change ¬ s (p 0) < p 1
    exact not_lt.mpr (le_of_lt (show p 1 < s (p 0) from hp))
  have hwR : IsWeakSolution flux right uR := by
    apply (hw.mono_domain (U := right) le_top).congr_ae_restrict
    filter_upwards [ae_restrict_mem right.isOpen.measurableSet] with p hp
    exact piecewise_eq_of_mem _ _ _ hp
  exact ⟨(isWeakSolution_iff_isClassicalSolutionOn hflux hL.contDiffOn).mp hwL,
    (isWeakSolution_iff_isClassicalSolutionOn hflux hR.contDiffOn).mp hwR⟩

/-- For C¹ extensions on both sides of any C¹ graph, the weak predicate
is equivalent to both classical bulk equations and the pointwise
Rankine–Hugoniot condition at the one-sided traces. -/
theorem isWeakSolution_piecewise_iff_classical_and_rankineHugoniot (hflux : ContDiff ℝ 1 flux)
    (hs : ContDiff ℝ 1 s) (hL : ContDiff ℝ 1 uL) (hR : ContDiff ℝ 1 uR) :
    IsWeakSolution flux ⊤ ((rightRegion s).piecewise uR uL) ↔
      IsClassicalSolutionOn flux {p | p 1 < s (p 0)} uL ∧
      IsClassicalSolutionOn flux (rightRegion s) uR ∧
      ∀ t, RankineHugoniot flux
        (uL (interface s t)) (uR (interface s t)) (deriv s t) := by
  constructor
  · intro hw
    obtain ⟨hPL, hPR⟩ := classical_on_sides_of_isWeakSolution hflux hs.continuous hL hR hw
    refine ⟨hPL, hPR, fun t ↦ jump_eq_zero_iff.mp ?_⟩
    apply PiLp.ext
    intro i
    have hc := (EuclideanSpace.proj i).continuous.comp
      (continuous_jump hflux.continuous hs hL.continuous hR.continuous)
    apply Scalar.Shock.eq_zero_of_integral_mul_trace_eq_zero hs hc _ t
    intro φ
    have hj := integrable_smul_jump hflux.continuous hs hL.continuous hR.continuous φ
    have hz : (∫ t, φ (interface s t) • jump flux s uL uR t) = 0 := by
      rw [← integral_weakIntegrand_piecewise hflux hs hL hR
        hPL.residual_eq_zero hPR.residual_eq_zero]
      exact hw.weak_eq φ
    have hi := congrArg (fun v : ℝ^m ↦ v i) hz
    rw [eval_integral_piLp (fun j ↦ hj.eval_piLp j) i] at hi
    simpa [mul_comm] using hi
  · rintro ⟨hPL, hPR, hRH⟩
    refine
      { u_locallyIntegrable :=
          (locallyIntegrable_piecewise hs.continuous hL.continuous.locallyIntegrable
            hR.continuous.locallyIntegrable).locallyIntegrableOn univ
        flux_locallyIntegrable := (locallyIntegrable_flux_piecewise hflux.continuous hs.continuous
            hL.continuous hR.continuous).locallyIntegrableOn univ
        weak_eq := fun φ ↦ ?_ }
    rw [integral_weakIntegrand_piecewise hflux hs hL hR hPL.residual_eq_zero hPR.residual_eq_zero]
    simp only [fun t ↦ jump_eq_zero_iff.mpr (hRH t), smul_zero, integral_zero]

/-- The raw scalar-test Bochner identity characterizes the two classical bulk
equations and the moving-interface jump condition. All local integrability
clauses of the weak predicate follow from the stated regularity. -/
theorem classical_and_rankineHugoniot_iff_integral_weakIntegrand_eq_zero (hflux : ContDiff ℝ 1 flux)
    (hs : ContDiff ℝ 1 s) (hL : ContDiff ℝ 1 uL) (hR : ContDiff ℝ 1 uR) :
    (IsClassicalSolutionOn flux {p | p 1 < s (p 0)} uL ∧
      IsClassicalSolutionOn flux (rightRegion s) uR ∧
      ∀ t, RankineHugoniot flux
        (uL (interface s t)) (uR (interface s t)) (deriv s t)) ↔
      ∀ φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ),
        (∫ p, weakIntegrand flux ((rightRegion s).piecewise uR uL) φ p) = 0 := by
  rw [← isWeakSolution_piecewise_iff_classical_and_rankineHugoniot hflux hs hL hR]
  constructor
  · exact fun hw ↦ hw.weak_eq
  · intro hweak
    exact
      { u_locallyIntegrable :=
          (locallyIntegrable_piecewise hs.continuous hL.continuous.locallyIntegrable
            hR.continuous.locallyIntegrable).locallyIntegrableOn univ
        flux_locallyIntegrable := (locallyIntegrable_flux_piecewise hflux.continuous hs.continuous
            hL.continuous hR.continuous).locallyIntegrableOn univ
        weak_eq := hweak }

end PDE.Hyperbolic.ConservationLaw.System.MovingInterface
