/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.MaximumPrinciple.FactoredOperator
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Parabolic maximum principle with a potential

This is Evans's §7.1.4(a), Theorem 9 (Weak maximum principle for `c ≥ 0`), for
`factoredParabolicOperator` plus a zeroth-order term `c u`. A subsolution is bounded on the closed
cylinder by every nonnegative upper bound `M` of its values on the parabolic boundary; taking for
`M` the maximum of `u⁺` there gives Evans's statement. As in the zero-potential case, the
coefficients need no continuity, and `c ≥ 0` is assumed only on `Ω × (0, T]`.

The proof follows Evans's. At a positive maximum of a strict subsolution the term `c u` is
nonnegative, so `strict_maximum_core` applies as before. Subtracting `εt` changes the residual by
`-ε - cεt ≤ -ε` (`factoredParabolicOperatorWithPotential_sub_time`), which makes a subsolution
strict.

## Main definitions

* `factoredParabolicOperatorWithPotential`: the operator `uₜ + Lu + cu`.

## Main results

* `subsolution_with_potential_le_of_boundary_le`: Evans's Theorem 9(i).
* `boundary_le_supersolution_with_potential`: Evans's Theorem 9(ii), for a nonpositive lower bound.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.4(a), Theorem 9 (Weak maximum principle for `c ≥ 0`) and
  its proof, (67), pp. 390-391.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace ParabolicMaximum

open Filter Function Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Add the zeroth-order term `c(x,t)u(x,t)` to the factored parabolic
operator. Evans's §7.1.4(a), Theorem 9 assumes `c ≥ 0`. -/
def factoredParabolicOperatorWithPotential {m : ℕ}
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E) (c : E → ℝ → ℝ)
    (u : E → ℝ → ℝ) (x : E) (t : ℝ) : ℝ :=
  factoredParabolicOperator σ b u x t + c x t * u x t

/-- The time perturbation `uε = u - εt` changes the operator with potential by
`-ε - cεt`. Under `c ≥ 0`, `ε > 0`, and `t ≥ 0`, this is at most `-ε`,
which is the strictification in step 2 of Evans's proof of §7.1.4(a), Theorem 9. -/
theorem factoredParabolicOperatorWithPotential_sub_time {m : ℕ}
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E) (c : E → ℝ → ℝ)
    (u : E → ℝ → ℝ) (ε : ℝ) (x : E) (t : ℝ)
    (hut : DifferentiableAt ℝ (u x) t) :
    factoredParabolicOperatorWithPotential σ b c
        (fun y s ↦ u y s - ε * s) x t =
      factoredParabolicOperatorWithPotential σ b c u x t -
        ε - c x t * (ε * t) := by
  rw [factoredParabolicOperatorWithPotential,
    factoredParabolicOperatorWithPotential,
    factoredParabolicOperator_sub_time σ b u ε x t hut]
  ring

/-- The operator with potential is linear under negation. -/
theorem factoredParabolicOperatorWithPotential_neg {m : ℕ}
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E) (c : E → ℝ → ℝ)
    (u : E → ℝ → ℝ) (x : E) (t : ℝ) :
    factoredParabolicOperatorWithPotential σ b c
        (fun y s ↦ -u y s) x t =
      -factoredParabolicOperatorWithPotential σ b c u x t := by
  rw [factoredParabolicOperatorWithPotential,
    factoredParabolicOperatorWithPotential,
    factoredParabolicOperator_neg]
  ring

/-- Strict positive-maximum form with a nonnegative zeroth-order
coefficient.  The proposed boundary bound is assumed nonnegative, so a
maximizer above it has positive value and contributes `c u ≥ 0`. -/
theorem strict_subsolution_with_potential_le_of_boundary_le {m : ℕ}
    {Ω : Set E} {T M : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hT : 0 < T) (hM : 0 ≤ M)
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E) (c : E → ℝ → ℝ)
    (hc : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, 0 ≤ c x t)
    (u : E → ℝ → ℝ)
    (hucont :
      ContinuousOn (fun p : E × ℝ ↦ u p.1 p.2) (closedCylinder Ω T))
    (huspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      DifferentiableAt ℝ (u x) t)
    (hsub : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      factoredParabolicOperatorWithPotential σ b c u x t < 0)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T, u p.1 p.2 ≤ M) :
    ∀ p ∈ closedCylinder Ω T, u p.1 p.2 ≤ M := by
  apply strict_maximum_core hΩopen hΩne hΩcompact hT
    (factoredParabolicOperatorWithPotential σ b c) u hucont
  · intro x hx t ht hspatialMax htimeMax hgap
    have hut_nonneg : 0 ≤ deriv (u x) t :=
      htimeMax.deriv_nonneg_of_left_lt ht.1 ht.2 (hutime x hx t ht)
    have hLu_nonneg : 0 ≤ factoredEllipticOperator σ b u x t :=
      factoredEllipticOperator_nonneg_at_localMax σ b hspatialMax
        (huspace x hx t ht)
    have hbase : 0 ≤ factoredParabolicOperator σ b u x t := by
      simpa [factoredParabolicOperator] using add_nonneg hut_nonneg hLu_nonneg
    have hu_pos : 0 < u x t := hM.trans_lt hgap
    exact add_nonneg hbase (mul_nonneg (hc x hx t ht) hu_pos.le)
  · exact hsub
  · exact hboundary

/-- Evans's §7.1.4(a), Theorem 9(i): weak maximum principle for `c ≥ 0`.

Any nonnegative parabolic-boundary bound controls a subsolution throughout
the closed cylinder.  Choosing the boundary bound to be the maximum of
`u⁺` gives Evans's displayed conclusion. -/
theorem subsolution_with_potential_le_of_boundary_le {m : ℕ}
    {Ω : Set E} {T M : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hT : 0 < T) (hM : 0 ≤ M)
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E) (c : E → ℝ → ℝ)
    (hc : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, 0 ≤ c x t)
    (u : E → ℝ → ℝ)
    (hucont :
      ContinuousOn (fun p : E × ℝ ↦ u p.1 p.2) (closedCylinder Ω T))
    (huspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      DifferentiableAt ℝ (u x) t)
    (hsub : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      factoredParabolicOperatorWithPotential σ b c u x t ≤ 0)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T, u p.1 p.2 ≤ M) :
    ∀ p ∈ closedCylinder Ω T, u p.1 p.2 ≤ M := by
  apply subsolution_le_of_strict_perturbation hT
    (factoredParabolicOperatorWithPotential σ b c)
    (strict_subsolution_with_potential_le_of_boundary_le
      hΩopen hΩne hΩcompact hT hM σ b c hc)
    u hucont huspace hutime ?_ hsub hboundary
  intro ε hε x hx t ht
  rw [factoredParabolicOperatorWithPotential_sub_time σ b c u ε x t
    (hutime x hx t ht)]
  exact sub_le_self _ (mul_nonneg (hc x hx t ht) (mul_nonneg hε.le ht.1.le))

/-- Evans's §7.1.4(a), Theorem 9(ii), the dual minimum principle for `c ≥ 0`. -/
theorem boundary_le_supersolution_with_potential {m : ℕ}
    {Ω : Set E} {T M : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hT : 0 < T) (hM : M ≤ 0)
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E) (c : E → ℝ → ℝ)
    (hc : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, 0 ≤ c x t)
    (u : E → ℝ → ℝ)
    (hucont :
      ContinuousOn (fun p : E × ℝ ↦ u p.1 p.2) (closedCylinder Ω T))
    (huspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      DifferentiableAt ℝ (u x) t)
    (hsuper : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      0 ≤ factoredParabolicOperatorWithPotential σ b c u x t)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T, M ≤ u p.1 p.2) :
    ∀ p ∈ closedCylinder Ω T, M ≤ u p.1 p.2 := by
  have hneg := subsolution_with_potential_le_of_boundary_le
    hΩopen hΩne hΩcompact hT (neg_nonneg.mpr hM)
    σ b c hc (fun x t ↦ -u x t) hucont.neg
    (fun x hx t ht ↦ (huspace x hx t ht).neg)
    (fun x hx t ht ↦ (hutime x hx t ht).neg)
    (fun x hx t ht ↦ by
      rw [factoredParabolicOperatorWithPotential_neg]
      exact neg_nonpos.mpr (hsuper x hx t ht))
    (fun p hp ↦ neg_le_neg (hboundary p hp))
  exact fun p hp ↦ neg_le_neg_iff.mp (hneg p hp)

end ParabolicMaximum
