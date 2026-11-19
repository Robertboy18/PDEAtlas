/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# An inequality form of the fundamental theorem of calculus on a half-line

If `g` has the derivative `g'` on `(a, ∞)` and an integrable function `φ` satisfies `φ ≤ g'`
there, then `∫ x in Ioi a, φ x ≤ g (∞) - g (a⁺)`, where `g (a⁺)` and `g (∞)` are the limits of
`g` at `a` from the right and at infinity (`PDE.Analysis.integral_Ioi_le_sub_of_hasDerivAt_of_le`).
The derivative `g'` need not be integrable, and nothing is asked of `g` at `a` beyond the limit,
so `g` may be a product with a factor that is singular at `a`.

This is the half-line form of Mathlib's `intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le`.
Mathlib's `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` gives the equality
`∫ x in Ioi a, g' x = g (∞) - g (a)` and asks that `g'` be integrable. The result is standard and
follows no particular source.

## How it works

The sets `(p, q]` with `p → a⁺` and `q → ∞` exhaust `(a, ∞)`, so the integrals of `φ` over them
tend to the integral over `(a, ∞)`. On each of them Mathlib's inequality gives
`∫ x in p..q, φ x ≤ g q - g p`, and the right side tends to `g (∞) - g (a⁺)`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis

/-- An inequality form of the fundamental theorem of calculus on `(a, ∞)`. If `g` has the
derivative `g'` on `(a, ∞)`, `φ` is integrable on `(a, ∞)` with `φ ≤ g'` there, and `g` tends to
`ga` at `a` from the right and to `gb` at infinity, then `∫ x in Ioi a, φ x ≤ gb - ga`. The
derivative `g'` need not be integrable. -/
theorem integral_Ioi_le_sub_of_hasDerivAt_of_le {g g' φ : ℝ → ℝ} {a ga gb : ℝ}
    (hg : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x) (hφ : IntegrableOn φ (Ioi a))
    (hφg : ∀ x ∈ Ioi a, φ x ≤ g' x) (hga : Tendsto g (𝓝[>] a) (𝓝 ga))
    (hgb : Tendsto g atTop (𝓝 gb)) : ∫ x in Ioi a, φ x ≤ gb - ga := by
  have hcov : AECover (volume.restrict (Ioi a)) ((𝓝[>] a) ×ˢ (atTop : Filter ℝ))
      fun p : ℝ × ℝ ↦ Ioi p.1 ∩ Iic p.2 :=
    (aecover_Ioi_of_Ioi (tendsto_fst.mono_right nhdsWithin_le_nhds)).inter
      (aecover_Iic tendsto_snd)
  refine le_of_tendsto_of_tendsto (hcov.integral_tendsto_of_countably_generated hφ)
    ((hgb.comp tendsto_snd).sub (hga.comp tendsto_fst)) ?_
  filter_upwards [prod_mem_prod (Ioo_mem_nhdsGT (lt_add_one a)) (Ici_mem_atTop (a + 1))]
    with p hp
  have hp1 : a < p.1 := hp.1.1
  have hp2 : p.1 ≤ p.2 := hp.1.2.le.trans hp.2
  have hset : Ioi p.1 ∩ Iic p.2 ∩ Ioi a = Ioc p.1 p.2 := by
    rw [Ioi_inter_Iic]
    exact inter_eq_left.mpr fun t ht ↦ hp1.trans ht.1
  rw [Measure.restrict_restrict (measurableSet_Ioi.inter measurableSet_Iic), hset,
    ← intervalIntegral.integral_of_le hp2]
  exact intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hp2
    (fun t ht ↦ (hg t (hp1.trans_le ht.1)).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hg t (hp1.trans ht.1)).hasDerivWithinAt)
    (hφ.mono_set fun t ht ↦ hp1.trans_le ht.1) fun t ht ↦ hφg t (hp1.trans ht.1)

end PDE.Analysis
