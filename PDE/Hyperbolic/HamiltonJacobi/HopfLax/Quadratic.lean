/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Variational
import CAS.ExactTactic

/-!
# The normalized quadratic Hopf–Lax cost

The cost `‖q‖²/2` is superlinear and self-dual. In finite dimension, continuous
bounded data therefore attain the usual quadratic footpoint formula. The
distance estimate for a minimizing footpoint is uniform in the base point:
`‖x-y‖² ≤ 4Mt` when `|g| ≤ M`.

This is the cost of Evans, §3.3.3(b), Example (i): `H(p) = |p|²/2` and `L(v) = |v|²/2`
(`hamiltonian_norm_sq_div_two`), so the Hopf–Lax formula (21) of §3.3.2(b) reads
`u(x, t) = min_y {|x - y|²/(2t) + g(y)}` (`value_norm_sq_div_two_eq`), as in (50) for
`g(y) = |y|`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), equation (21); §3.3.3(b), Example (i),
  equations (49)-(50).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi.HopfLax

open Set

/-- The normalized squared norm dominates every affine function of the norm. -/
theorem superlinear_norm_sq_div_two {E : Type*} [NormedAddCommGroup E] :
    Superlinear (fun q : E ↦ ‖q‖ ^ 2 / 2) := by
  intro A
  refine ⟨A ^ 2 / 2, fun q ↦ ?_⟩
  linarith [sq_nonneg (‖q‖ - A)]

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Legendre transform of `‖q‖²/2` is `‖p‖²/2`, with maximizer `q = p`. -/
theorem hamiltonian_norm_sq_div_two (p : E) :
    hamiltonian (fun q : E ↦ ‖q‖ ^ 2 / 2) p = ‖p‖ ^ 2 / 2 := by
  refine le_antisymm (csSup_le (Set.range_nonempty _) (Set.forall_mem_range.2 fun q ↦ ?_)) ?_
  · linarith [real_inner_le_norm p q, sq_nonneg (‖p‖ - ‖q‖)]
  · have h := le_hamiltonian (E := E) superlinear_norm_sq_div_two p p
    simp only [real_inner_self_eq_norm_sq] at h
    linarith only [h]

end Hilbert

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The velocity and footpoint formulas agree at nonzero time, with the normalization
`‖x-y‖²/(2t)`. This algebraic identity does not require positive time. -/
theorem value_norm_sq_div_two_eq {g : E → ℝ} {t : ℝ} (ht : t ≠ 0) (x : E) :
    value (fun q : E ↦ ‖q‖ ^ 2 / 2) g t x =
      sInf (Set.range fun y : E ↦ g y + ‖x - y‖ ^ 2 / (2 * t)) := by
  rw [value_eq_inf_footpoints _ _ ht]
  apply congrArg sInf
  apply congrArg Set.range
  funext y
  congr 1
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
  cas using ht

/-- Bounded data retain their range under the quadratic Hopf–Lax formula. -/
theorem value_norm_sq_div_two_bounds {g : E → ℝ} {M t : ℝ}
    (hg : ∀ y, |g y| ≤ M) (ht : 0 ≤ t) (x : E) :
    -M ≤ value (fun q : E ↦ ‖q‖ ^ 2 / 2) g t x ∧ value (fun q : E ↦ ‖q‖ ^ 2 / 2) g t x ≤ M := by
  have hlower : ∀ y, -M - ((0 : NNReal) : ℝ) * ‖y‖ ≤ g y := by
    intro y
    simpa only [NNReal.coe_zero, zero_mul, sub_zero] using (abs_le.mp (hg y)).1
  constructor
  · have h := norm_lower_bound_value (L := fun q : E ↦ ‖q‖ ^ 2 / 2)
      (K := (0 : NNReal)) (B := 0) hlower
      (fun q ↦ by simp only [NNReal.coe_zero, zero_mul, sub_zero]; positivity) ht x
    simpa only [NNReal.coe_zero, mul_zero, zero_mul, add_zero, sub_zero] using h
  · have h := csInf_le (bddBelow_cost_of_norm_lower_bound superlinear_norm_sq_div_two hlower ht x)
      (show cost (fun q : E ↦ ‖q‖ ^ 2 / 2) g t x 0 ∈
        Set.range (cost (fun q : E ↦ ‖q‖ ^ 2 / 2) g t x) from ⟨0, rfl⟩)
    have hz : cost (fun q : E ↦ ‖q‖ ^ 2 / 2) g t x 0 = g x := by simp [cost]
    exact (h.trans_eq hz).trans (abs_le.mp (hg x)).2

/-- Positive-time quadratic costs for bounded continuous data attain their infimum.
The minimizing footpoint lies within distance `2√(Mt)` of the base point. -/
theorem exists_quadratic_footpoint [ProperSpace E] {g : E → ℝ} {M t : ℝ}
    (hg : Continuous g) (hgb : ∀ y, |g y| ≤ M) (ht : 0 < t) (x : E) :
    ∃ y, value (fun q : E ↦ ‖q‖ ^ 2 / 2) g t x = g y + ‖x - y‖ ^ 2 / (2 * t) ∧
      (∀ z, g y + ‖x - y‖ ^ 2 / (2 * t) ≤ g z + ‖x - z‖ ^ 2 / (2 * t)) ∧
      ‖x - y‖ ^ 2 ≤ 4 * M * t := by
  have hlower : ∀ y, -M - ((0 : NNReal) : ℝ) * ‖y‖ ≤ g y := by
    intro y
    simpa only [NNReal.coe_zero, zero_mul, sub_zero] using (abs_le.mp (hgb y)).1
  obtain ⟨q, hq, hmin⟩ := exists_minimizer_of_norm_lower_bound
    ((continuous_norm.pow 2).div_const 2) superlinear_norm_sq_div_two hg hlower ht x
  let y := x - t • q
  have hcost (z : E) : cost (fun q : E ↦ ‖q‖ ^ 2 / 2) g t x (t⁻¹ • (x - z)) =
        g z + ‖x - z‖ ^ 2 / (2 * t) := by
    simp only [cost, smul_smul, mul_inv_cancel₀ ht.ne', one_smul, sub_sub_cancel,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    cas using ht.ne'
  have hqback : t⁻¹ • (x - y) = q := by
    simp [y, smul_smul, ht.ne']
  have hy : value (fun q : E ↦ ‖q‖ ^ 2 / 2) g t x = g y + ‖x - y‖ ^ 2 / (2 * t) :=
    hq.trans ((congrArg (cost (fun q : E ↦ ‖q‖ ^ 2 / 2) g t x) hqback.symm).trans (hcost y))
  refine ⟨y, hy, fun z ↦ ?_, ?_⟩
  · have h := hmin (t⁻¹ • (x - z))
    have heq := hcost y
    rw [hqback] at heq
    rwa [hcost z, heq] at h
  · have hval := (value_norm_sq_div_two_bounds hgb ht.le x).2
    rw [hy] at hval
    have hfrac : ‖x - y‖ ^ 2 / (2 * t) ≤ 2 * M := by
      linarith [(abs_le.mp (hgb y)).1]
    linarith only [(div_le_iff₀ (show 0 < 2 * t by positivity)).mp hfrac]

/-- Positive parabolic rescaling reduces the quadratic value at time `r²`
to time one, with the datum translated and dilated. No continuity is needed. -/
theorem value_norm_sq_div_two_parabolic_rescale (g : E → ℝ) (x : E) {r : ℝ} (hr : 0 < r) :
    value (fun q : E ↦ ‖q‖ ^ 2 / 2) g (r ^ 2) x =
      value (fun q : E ↦ ‖q‖ ^ 2 / 2) (fun y ↦ g (x + r • y)) 1 0 := by
  have hcost (q : E) : cost (fun q : E ↦ ‖q‖ ^ 2 / 2) g (r ^ 2) x q =
        cost (fun q : E ↦ ‖q‖ ^ 2 / 2) (fun y ↦ g (x + r • y)) 1 0 (r • q) := by
    have hspace : x + r • (0 - (1 : ℝ) • (r • q)) = x - r ^ 2 • q := by
      rw [one_smul, zero_sub, smul_neg, smul_smul, pow_two, sub_eq_add_neg]
    simp only [cost, hspace, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow]
    cas
  unfold value
  congr 1
  ext z
  exact ⟨fun ⟨q, hq⟩ ↦ ⟨r • q, (hcost q).symm.trans hq⟩, fun ⟨q, hq⟩ ↦ ⟨r⁻¹ • q, by
    rw [hcost, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, hq]⟩⟩

end Normed

end HamiltonJacobi.HopfLax
