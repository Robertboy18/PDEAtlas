/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SignedPower
public import PDE.Analysis.MeasureTheory.Lp.Superposition.PowerDifference
import Mathlib.Tactic.Positivity.Finset

/-!
# Odd-power superposition in Lp

For `r > 0`, the pointwise source `|u|^(r-1) u` sends `Lp` to `L(p/r)` on any
measure space. Its exact norm growth proves membership, including fractional
powers. When both Lebesgue exponents are at least one and the input exponent
is finite, the map is continuous.

For `r > 1`, the scalar two-point estimate and Hölder's inequality give an
explicit difference bound, hence Lipschitz bounds on bounded input balls.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A positive odd power maps `Lp` to the space with exponent divided by
that power. The norm-power identity proves membership on arbitrary measures. -/
theorem memLp_signedPower {p q : ℝ≥0∞} {r : ℝ}
    (hr : 0 < r) (hq : p / ENNReal.ofReal r = q) (u : Lp ℝ p μ) :
    MemLp (fun x ↦ Real.signedPower r (u x)) q μ := by
  have hpow : MemLp (fun x ↦ ‖u x‖ ^ r) q μ := by
    simpa only [ENNReal.toReal_ofReal hr.le, hq] using
      (Lp.memLp u).norm_rpow_div (ENNReal.ofReal r)
  exact hpow.mono'
    ((Real.continuous_signedPower hr).comp_aestronglyMeasurable
      (Lp.memLp u).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ (Real.norm_signedPower hr (u x)).le)

/-- The odd-power map has exactly the same norm as the corresponding norm
power. No finiteness of the underlying measure is needed. -/
theorem norm_superposition_signedPower {p q : ℝ≥0∞} {r : ℝ}
    (hr : 0 < r) (hq : p / ENNReal.ofReal r = q) (u : Lp ℝ p μ) :
    ‖superposition (fun _ ↦ Real.signedPower r) (memLp_signedPower hr hq) u‖ =
      ‖u‖ ^ r := by
  subst q
  have heq :
      ‖superposition (fun _ ↦ Real.signedPower r) (memLp_signedPower hr rfl) u‖ =
        ‖normRpow hr.le u‖ := by
    simp only [Lp.norm_def]
    apply congrArg ENNReal.toReal
    refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
      (Lp.aestronglyMeasurable _) ?_
    filter_upwards [coeFn_superposition (fun _ ↦ Real.signedPower r)
      (memLp_signedPower hr rfl) u, coeFn_normRpow hr.le u] with x hu hv
    rw [hu, hv, Real.norm_signedPower hr,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [heq, norm_normRpow hr]

/-- Positive odd powers define continuous maps between their natural finite
`Lp` spaces. Powers below one are included, so the inverse power is covered. -/
theorem continuous_superposition_signedPower {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] {r : ℝ}
    (hp : p ≠ ∞) (hr : 0 < r) (hq : p / ENNReal.ofReal r = q) :
    Continuous (superposition (fun _ ↦ Real.signedPower r)
      (memLp_signedPower (μ := μ) hr hq)) := by
  subst q
  apply continuous_superposition_of_rpow_growth (C := 1) hp hr
    (memLp_signedPower hr rfl)
    (Filter.Eventually.of_forall fun _ ↦ Real.continuous_signedPower hr)
    (MemLp.zero : MemLp (0 : α → ℝ) (p / ENNReal.ofReal r) μ)
  exact Filter.Eventually.of_forall fun x z ↦ by
    simpa only [Pi.zero_apply, zero_add, one_mul] using (Real.norm_signedPower hr z).le

/-- The odd-power superposition map `L^(2r) → L²`. -/
def signedPower {r : ℝ} (hr : 1 ≤ r)
    (u : Lp ℝ (ENNReal.ofReal (2 * r)) μ) : Lp ℝ 2 μ :=
  superposition (fun _ ↦ Real.signedPower r)
    (memLp_signedPower (zero_lt_one.trans_le hr) (by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        ENNReal.mul_div_cancel_right (by positivity) ENNReal.ofReal_ne_top])) u

/-- The bundled source agrees almost everywhere with its pointwise formula. -/
theorem coeFn_signedPower {r : ℝ} (hr : 1 ≤ r)
    (u : Lp ℝ (ENNReal.ofReal (2 * r)) μ) :
    signedPower hr u =ᵐ[μ] fun x ↦ Real.signedPower r (u x) :=
  coeFn_superposition _ _ _

/-- Quantitative continuity of the odd-power superposition map for every
real exponent strictly larger than one. -/
theorem norm_signedPower_sub_le {r : ℝ} (hr : 1 < r)
    (u v : Lp ℝ (ENNReal.ofReal (2 * r)) μ) :
    ‖signedPower hr.le u - signedPower hr.le v‖ ≤
      (2 * r) * (‖u‖ + ‖v‖) ^ (r - 1) * ‖u - v‖ := by
  have : Fact (1 ≤ ENNReal.ofReal (2 * r)) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  have hq : ENNReal.ofReal (2 * r) / ENNReal.ofReal r = 2 := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.mul_div_cancel_right (by positivity) ENNReal.ofReal_ne_top]
  exact norm_superposition_sub_le_of_twoPointGrowth ENNReal.ofReal_ne_top hr hq
    (by positivity) (memLp_signedPower (zero_lt_one.trans hr) hq)
    (Real.norm_signedPower_sub_le hr.le) u v

end MeasureTheory.Lp
