/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The normed star structure on `Lp`

Mathlib defines pointwise `star` on `Lp`. It preserves addition and the norm, so
Mathlib's lemmas about normed star groups apply to these spaces. In particular, complex conjugation
is an isometry on complex `Lp`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α R : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

noncomputable instance instStarAddMonoid : StarAddMonoid (Lp R p μ) where
  star_add f g := by
    apply Lp.ext
    filter_upwards [coeFn_star (f + g), coeFn_add f g, coeFn_star f, coeFn_star g,
      coeFn_add (star f) (star g)] with x hfg hadd hf hg hstar
    simp_all only [Pi.star_apply, Pi.add_apply, star_add]

instance instNormedStarGroup [Fact (1 ≤ p)] : NormedStarGroup (Lp R p μ) where
  norm_star_le f := by
    apply le_of_eq
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    exact (eLpNorm_congr_ae (coeFn_star f)).trans (by simp)

end MeasureTheory.Lp
