/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Comparing positive perturbed eigenvectors in `Lᵖ`

Suppose a positive linear map satisfies `w ≤ M A w` for a nonzero nonnegative `w`.
Every nonnegative solution of `u = η A (u + ε w)`, with `ε > 0`, has `η < M`.
Indeed, `η ≥ M` would give `u ≥ k ε w` for every natural `k`, contradicting the norm
bound. Compactness and continuity of the operator are not needed for this comparison.

Evans's (27), in step 3 of the proof of §6.5.2, Theorem 3, is the weaker bound `η ≤ μ` for
`w ≤ μ A w`; he iterates to `u ≥ (η / μ)ᵏ ε w`, and the additive iteration above gives the
strict bound.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.5.2, Theorem 3, p. 361, step 3 of its proof,
  (25)-(27), pp. 361-362. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal

namespace LinearMap

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A positive subeigenvector bounds the parameter of every nonnegative perturbed
eigenvector. The order hypotheses concern the `Lp` representatives. -/
theorem parameter_lt_of_nonneg_perturbed_eigenvector
    (A : Lp ℝ p μ →ₗ[ℝ] Lp ℝ p μ)
    (hA : ∀ v : Lp ℝ p μ, (∀ᵐ x ∂μ, 0 ≤ v x) → ∀ᵐ x ∂μ, 0 ≤ A v x)
    {w u : Lp ℝ p μ} {M ε η : ℝ}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (hw0 : w ≠ 0)
    (hM : 0 < M) (hsub : ∀ᵐ x ∂μ, w x ≤ M * A w x)
    (hε : 0 < ε) (hu : ∀ᵐ x ∂μ, 0 ≤ u x)
    (heq : u = η • A (u + ε • w)) :
    η < M := by
  by_contra hnot
  have hηM : M ≤ η := le_of_not_gt hnot
  have hη : 0 ≤ η := hM.le.trans hηM
  have hAw := hA w hw
  have hiter (k : ℕ) : ∀ᵐ x ∂μ, (k : ℝ) * ε * w x ≤ u x := by
    induction k with
    | zero => simpa using hu
    | succ k ih =>
      let d := ((k : ℝ) + 1) * ε
      have hd : 0 ≤ d :=
        mul_nonneg (add_nonneg (Nat.cast_nonneg k) zero_le_one) hε.le
      have hnonneg : ∀ᵐ x ∂μ, 0 ≤ (u + ε • w - d • w) x := by
        filter_upwards [ih, Lp.coeFn_sub (u + ε • w) (d • w),
          Lp.coeFn_add u (ε • w), Lp.coeFn_smul ε w, Lp.coeFn_smul d w]
          with x hx hdiff hadd hscale hscale'
        simp only [hdiff, hadd, hscale, hscale', Pi.sub_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        dsimp [d]
        nlinarith
      have himage : ∀ᵐ x ∂μ, d * A w x ≤ A (u + ε • w) x := by
        have hpos := hA (u + ε • w - d • w) hnonneg
        rw [map_sub, map_smul] at hpos
        filter_upwards [hpos, Lp.coeFn_sub (A (u + ε • w)) (d • A w),
          Lp.coeFn_smul d (A w)] with x hx hdiff hscale
        simpa only [hdiff, hscale, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          sub_nonneg] using hx
      have huval : ∀ᵐ x ∂μ, u x = η * A (u + ε • w) x := by
        filter_upwards [Lp.coeFn_smul η (A (u + ε • w))] with x hx
        exact (congrArg (fun v : Lp ℝ p μ ↦ v x) heq).trans hx
      filter_upwards [himage, hsub, hAw, huval] with x hx hsubx hAwx hux
      have h₁ := mul_le_mul_of_nonneg_left hsubx hd
      have h₂ := mul_le_mul_of_nonneg_right hηM (mul_nonneg hd hAwx)
      have h₃ := mul_le_mul_of_nonneg_left hx hη
      simp only [Nat.cast_add, Nat.cast_one]
      dsimp [d] at *
      nlinarith
  have hnorm (k : ℕ) : (k : ℝ) * (ε * ‖w‖) ≤ ‖u‖ := by
    have h : ‖((k : ℝ) * ε) • w‖ ≤ ‖u‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hiter k, hw, hu, Lp.coeFn_smul ((k : ℝ) * ε) w]
        with x hx hwx hux hscale
      simpa only [hscale, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hε.le) hwx),
        abs_of_nonneg hux] using hx
    simpa only [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) hε.le), mul_assoc] using h
  have hpos : 0 < ε * ‖w‖ := mul_pos hε (norm_pos_iff.mpr hw0)
  obtain ⟨k, hk⟩ := exists_nat_gt (‖u‖ / (ε * ‖w‖))
  exact (not_lt_of_ge (hnorm k)) ((div_lt_iff₀ hpos).mp hk)

end LinearMap
