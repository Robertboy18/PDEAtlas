/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
import CAS.ExactTactic

/-!
# Similarity exponents for the porous-medium equation

For `u_t = Δ(u^m)` with `m > 1`, the ansatz `u(t, x) = t^(-α) F(t^(-β) x)` conserves mass when
`α = nβ` (`similarity_mass_balance`) and balances the time derivative against the diffusion term
when `α(m-1) + 2β = 1` (`similarity_diffusion_balance`). The two equations determine
`α = n/(n(m-1)+2)` and `β = 1/(n(m-1)+2)` (`similarity_exponents_unique`). The Barenblatt profile is
`(C - k |y|²)₊^(1/(m-1))` with `k = (m-1)β/(2m)` (`profileExponent`, `profileCoefficient`), and
`profile_coefficient_balance` is the identity behind its flux `∇(F^m)(y) = -β y F(y)`. SymLean's
`cas` tactic checks the exponent algebra.

These are the exponents (30), (33) and (36) and the profile (34) of Evans's §4.2.2, with `γ = m` and
`b = C`. Evans obtains `α = nβ`, his (33), as the choice that simplifies the radial equation (32);
it is also the condition for the ansatz to conserve mass.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.2.2, Example (A scaling invariant solution), (27)-(36),
  pp. 185-186.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PorousMedium

/-- The spatial similarity exponent. -/
def similarityBeta (n : ℕ) (m : ℝ) : ℝ := 1 / ((n : ℝ) * (m - 1) + 2)

/-- The amplitude decay exponent dictated by conserved mass. -/
def similarityAlpha (n : ℕ) (m : ℝ) : ℝ := (n : ℝ) * similarityBeta n m

/-- The power of the positive part in the Barenblatt profile. -/
def profileExponent (m : ℝ) : ℝ := 1 / (m - 1)

/-- The quadratic coefficient in the Barenblatt profile. -/
def profileCoefficient (n : ℕ) (m : ℝ) : ℝ :=
  (m - 1) * similarityBeta n m / (2 * m)

/-- The similarity denominator is positive for slow diffusion. -/
theorem similarity_denominator_pos (n : ℕ) {m : ℝ} (hm : 1 < m) :
    0 < (n : ℝ) * (m - 1) + 2 := by
  positivity

/-- Slow diffusion gives a strictly expanding spatial scale. -/
theorem similarityBeta_pos (n : ℕ) {m : ℝ} (hm : 1 < m) :
    0 < similarityBeta n m :=
  div_pos zero_lt_one (similarity_denominator_pos n hm)

/-- In positive dimension the amplitude strictly decreases with time. -/
theorem similarityAlpha_pos {n : ℕ} (hn : 0 < n) {m : ℝ} (hm : 1 < m) :
    0 < similarityAlpha n m :=
  mul_pos (by exact_mod_cast hn) (similarityBeta_pos n hm)

/-- The profile exponent is positive for every `m > 1`. -/
theorem profileExponent_pos {m : ℝ} (hm : 1 < m) : 0 < profileExponent m :=
  div_pos zero_lt_one (sub_pos.mpr hm)

/-- The positive quadratic coefficient gives a bounded positivity region. -/
theorem profileCoefficient_pos (n : ℕ) {m : ℝ} (hm : 1 < m) :
    0 < profileCoefficient n m :=
  div_pos (mul_pos (sub_pos.mpr hm) (similarityBeta_pos n hm))
    (mul_pos (by norm_num) (lt_trans zero_lt_one hm))

/-- The amplitude exponent is the dimension times the spatial exponent. -/
theorem similarity_mass_balance (n : ℕ) (m : ℝ) :
    similarityAlpha n m = (n : ℝ) * similarityBeta n m := rfl

/-- The similarity powers in the porous-medium equation match. -/
theorem similarity_diffusion_balance (n : ℕ) {m : ℝ} (hm : 1 < m) :
    similarityAlpha n m * (m - 1) + 2 * similarityBeta n m = 1 := by
  have hd := ne_of_gt (similarity_denominator_pos n hm)
  unfold similarityAlpha similarityBeta
  cas

/-- The mass and diffusion balances uniquely determine both exponents. -/
theorem similarity_exponents_unique (n : ℕ) {m α β : ℝ} (hm : 1 < m)
    (hmass : α = (n : ℝ) * β) (hscale : α * (m - 1) + 2 * β = 1) :
    α = similarityAlpha n m ∧ β = similarityBeta n m := by
  have hd := ne_of_gt (similarity_denominator_pos n hm)
  unfold similarityAlpha similarityBeta
  constructor <;> cas using [hmass, hscale]

/-- The diffusion potential has a power strictly greater than one. -/
theorem potential_exponent_gt_one {m : ℝ} (hm : 1 < m) :
    1 < profileExponent m * m := by
  unfold profileExponent
  have hpos := sub_pos.mpr hm
  have heq : 1 / (m - 1) * m = 1 + 1 / (m - 1) := by cas
  rw [heq]
  linarith [div_pos zero_lt_one hpos]

/-- The exponent in the derivative of the potential is the density exponent. -/
theorem potential_exponent_sub_one {m : ℝ} (hm : 1 < m) :
    profileExponent m * m - 1 = profileExponent m := by
  have hne := ne_of_gt (sub_pos.mpr hm)
  unfold profileExponent
  cas

/-- The chosen coefficient makes the profile flux equal to `-β y F(y)`. -/
theorem profile_coefficient_balance (n : ℕ) {m : ℝ} (hm : 1 < m) :
    2 * (profileExponent m * m) * profileCoefficient n m = similarityBeta n m := by
  have hm0 := ne_of_gt (lt_trans zero_lt_one hm)
  have hm1 := ne_of_gt (sub_pos.mpr hm)
  unfold profileExponent profileCoefficient
  cas

end PorousMedium
