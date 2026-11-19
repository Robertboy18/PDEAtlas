/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative

/-!
# Weak normal derivatives from bounded inward quotients

For `1 < p < ∞`, a uniform bound on positive normal difference quotients gives a weak
normal derivative on the upper half-space with the same norm bound. The quotients use
the zero extension only to represent translations in the ambient `Lp` space; the
derivative is a weak derivative on the half-space, with no zero-trace assumption.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open Filter MeasureTheory Set Rellich
open SobolevSpace.Extension.Lp
open scoped ENNReal Topology

variable {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniformly bounded inward normal quotients yield an `Lp` weak normal derivative
with the same bound. Positive reciprocal steps suffice for the domain-local converse. -/
theorem exists_normal_weakDerivative_of_bounded_inward_differenceQuotients
    (hp : 1 < p) (hp_top : p ≠ ∞) (u : DerivLp n p ℝ^n₊) (C : ℝ)
    (hbound : ∀ h : ℝ, 0 < h →
      ‖restrictDerivLp (subset_univ ℝ^n₊)
        (differenceQuotientLp p (PDE.Common.lastIndex (n := n)) h
          (zeroExtendLp (HalfSpace.measurableSet_upper n) u))‖ ≤ C) :
    ∃ g : DerivLp n p ℝ^n₊, ‖g‖ ≤ C ∧
      HasWeakDerivativeOn ℝ^n₊ [PDE.Common.lastIndex (n := n)]
        (u : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  let h : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hpos (k : ℕ) : 0 < h k := by
    dsimp [h]
    positivity
  exact exists_Lp_weakDerivativeOn_of_bounded_zeroExtensionDifferenceQuotients_with_norm
    hp hp_top ℝ^n₊ ℝ^n₊ (HalfSpace.measurableSet_upper n)
    (HalfSpace.measurableSet_upper n) Subset.rfl (PDE.Common.lastIndex (n := n))
    h tendsto_one_div_add_atTop_nhds_zero_nat (fun k ↦ (hpos k).ne') u C
    (fun k ↦ hbound (h k) (hpos k))

end SobolevSpace.GraphSpace.DifferenceQuotient
