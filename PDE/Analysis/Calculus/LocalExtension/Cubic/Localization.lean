/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.Cubic.Construction

/-!
# Small cubic corrections inside a prescribed coordinate strip

Fix the coordinate `m`, the amplitude `A`, a positive cap for the scale, and a
positive derivative tolerance. A single cutoff realizes the cubic product where
`|m| ≤ ε` and has topological support inside both `tsupport A` and `|m| ≤ 2ε`.
Choosing `ε` below the cap leaves the exact cubic core and zero jets intact.

The uniform derivative estimate comes from Mathlib's bounds for the two fixed
compactly supported inputs and the existing rescaled cubic cutoff estimate.
The stronger zero-preserving constructor owns this proof; the statements below
retain their original interfaces by projection.
-/

@[expose] public noncomputable section

open Function Set
open scoped ContDiff

namespace PDE.Analysis

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A fixed cubic product has a smooth compactly supported realization at a
positive scale below any prescribed positive cap. Its derivatives through order
two are uniformly small, and all three jets vanish exactly where `m = 0`.

The topological support lies in `tsupport A ∩ {x | |m x| ≤ 2 * ε}`, while the
formula is exactly cubic on the inner strip `|m x| ≤ ε`. Both input functions and
`εcap` are fixed before `ε` is chosen. -/
theorem exists_localized_small_compact_cubic_correction
    {m : E → ℝ} {A : E → V}
    (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (εcap : ℝ) (hcap : 0 < εcap)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ε : ℝ) (P : E → V),
      0 < ε ∧ ε < εcap ∧ ε ≤ 1 ∧ ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
      tsupport P ⊆ tsupport A ∩ {x | |m x| ≤ 2 * ε} ∧
      (∀ x, |m x| ≤ ε → P x = (m x) ^ 3 • A x) ∧
      (∀ n ≤ 2, ∀ x, ‖iteratedFDeriv ℝ n P x‖ < η) ∧
      ∀ x, m x = 0 → ∀ n ≤ 2, iteratedFDeriv ℝ n P x = 0 := by
  obtain ⟨ε, P, hε, hεcap, hεone, hP, hPc, hsupport, hexact, _, hsmall, hzero⟩ :=
    exists_localized_small_compact_cubic_correction_preserving_zeros
      hm hmc hA hAc εcap hcap hη
  exact ⟨ε, P, hε, hεcap, hεone, hP, hPc, hsupport, hexact, hsmall, hzero⟩

/-- A cubic correction with uniformly small derivatives through order two.
This follows from the localized constructor with cap `1`. -/
theorem exists_small_compact_cubic_correction
    {m : E → ℝ} {A : E → V}
    (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ε : ℝ) (P : E → V),
      0 < ε ∧ ε ≤ 1 ∧ ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
      tsupport P ⊆ tsupport A ∧
      (∀ x, |m x| ≤ ε → P x = (m x) ^ 3 • A x) ∧
      (∀ n ≤ 2, ∀ x, ‖iteratedFDeriv ℝ n P x‖ < η) ∧
      ∀ x, m x = 0 → ∀ n ≤ 2, iteratedFDeriv ℝ n P x = 0 := by
  obtain ⟨ε, P, hε, _, hεone, hP, hPc, hsupport, hexact, hsmall, hzero⟩ :=
    exists_localized_small_compact_cubic_correction hm hmc hA hAc 1 zero_lt_one hη
  exact ⟨ε, P, hε, hεone, hP, hPc, fun _ hx ↦ (hsupport hx).1,
    hexact, hsmall, hzero⟩

end PDE.Analysis
