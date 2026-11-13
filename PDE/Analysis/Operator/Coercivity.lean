/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Coercivity and lower bounds

A bilinear form with a positive quadratic lower bound, in particular a form satisfying
Mathlib's `IsCoercive`, is nonnegative on the diagonal.

For nonlinear energies, a positive power lower bound with exponent greater than one
eventually dominates every linear function of the norm. An additive offset does not
affect this conclusion.
-/

@[expose] public section

namespace IsCoercive

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A positive quadratic lower bound makes a bilinear form nonnegative on
the diagonal. -/
theorem self_nonneg_of_bound
    {B : V →L[ℝ] V →L[ℝ] ℝ} {c : ℝ} (hc : 0 < c)
    (hBcoercive : ∀ v, c * ‖v‖ * ‖v‖ ≤ B v v) (v : V) :
    0 ≤ B v v := by
  exact
    (mul_nonneg (mul_nonneg hc.le (norm_nonneg v)) (norm_nonneg v)).trans
      (hBcoercive v)

/-- A coercive continuous bilinear form is nonnegative on the diagonal. -/
theorem self_nonneg
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hBcoercive : IsCoercive B) (v : V) :
    0 ≤ B v v := by
  rcases hBcoercive with ⟨c, hc, hbound⟩
  exact self_nonneg_of_bound hc hbound v

end IsCoercive

open Filter

namespace PDE.Analysis

/-- A positive lower bound of power greater than one eventually
dominates every prescribed multiple of the norm. The integral offset
in coercive energy estimates can have either sign. -/
theorem exists_radius_mul_norm_le_of_rpow_lower_bound
    {X : Type*} [SeminormedAddCommGroup X] {F : X → ℝ}
    {r K B : ℝ} (hr : 1 < r) (hK : 0 < K)
    (hlower : ∀ u, K * ‖u‖ ^ r - B ≤ F u) (M : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : X, R ≤ ‖u‖ → M * ‖u‖ ≤ F u := by
  obtain ⟨R₀, hR₀⟩ :=
    tendsto_atTop_atTop.mp (tendsto_rpow_atTop (sub_pos.mpr hr)) ((M + |B|) / K)
  refine ⟨max 1 R₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu
  have huone : 1 ≤ ‖u‖ := (le_max_left _ _).trans hu
  have hupos : 0 < ‖u‖ := zero_lt_one.trans_le huone
  have hpower : M + |B| ≤ K * ‖u‖ ^ (r - 1) := by
    have hquot := (div_le_iff₀ hK).mp (hR₀ ‖u‖ ((le_max_right _ _).trans hu))
    simpa only [mul_comm] using hquot
  have htimes := mul_le_mul_of_nonneg_right hpower (norm_nonneg u)
  have hpow : ‖u‖ ^ (r - 1) * ‖u‖ = ‖u‖ ^ r := by
    rw [Real.rpow_sub_one hupos.ne', div_mul_cancel₀ _ hupos.ne']
  have hbig : (M + |B|) * ‖u‖ ≤ K * ‖u‖ ^ r := by
    simpa only [mul_assoc, hpow] using htimes
  have habs := mul_le_mul_of_nonneg_left huone (abs_nonneg B)
  have hlow := hlower u
  nlinarith [le_abs_self B]

end PDE.Analysis
