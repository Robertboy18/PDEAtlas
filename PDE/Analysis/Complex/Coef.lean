/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Complex.Circle
public import PDE.Analysis.Complex.Definitions
public import PDE.Analysis.Normed.PiLp.CompareExp

set_option linter.style.header false

/-!
# The space `ℂ³`: norms, inner products and scalar multiples

The lemmas are stated for `PDE.Analysis.Coef = EuclideanSpace ℂ (Fin 3)`: bounds of the norm and of
the extended norm of sums and differences, the relation between the real and the complex inner
product and between real and complex scalar multiples, a bound for a combination of three vectors,
and a Lipschitz bound for the inner product. The proofs use the lemmas of Mathlib on
`EuclideanSpace`, the Cauchy–Schwarz inequality and `nlinarith`.

## Main results

* `PDE.Analysis.enorm_le_sum_enorm_apply_coef`: For `v` in `ℂ³`, the extended norm of `v` is at most
  the sum of the extended norms of its three coordinates.
* `PDE.Analysis.norm_two_pi_I_mul_smul_sq_coef`: For a real `t` and `z` in `ℂ³`,
  `‖((2 π i) * t) • z‖ ^ 2 = (2 π) ^ 2 * t ^ 2 * ‖z‖ ^ 2`.
* `PDE.Analysis.enorm_sub_sq_le_coef`: For `x`, `y` in `ℂ³`,
  `‖x - y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2` in `ℝ≥0∞`. The inequality for the real norms follows
  from `‖x - y‖ ≤ ‖x‖ + ‖y‖` and `(‖x‖ - ‖y‖) ^ 2 ≥ 0`.
* `PDE.Analysis.ofReal_mul_enorm_sq_coef`: For a real `r ≥ 0` and `v` in `ℂ³`,
  `ENNReal.ofReal r * ‖v‖ₑ ^ 2 = ENNReal.ofReal (r * ‖v‖ ^ 2)`.
* `PDE.Analysis.enorm_add_sq_le_coef`: For `x`, `y` in `ℂ³`,
  `‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2` in `ℝ≥0∞`. The inequality for the real norms follows
  from the triangle inequality and `(‖x‖ - ‖y‖) ^ 2 ≥ 0`.
* `PDE.Analysis.enorm_ofReal_smul_coef`: For a real `r` and `v` in `ℂ³`,
  `‖(r : ℂ) • v‖ₑ = ENNReal.ofReal |r| * ‖v‖ₑ`.
* `PDE.Analysis.fourierChar_smul_eq_exp_smul_coef`: For a real `t` and `v` in `ℂ³`, the character
  `𝐞 t` acts on `v` as the complex number `exp (2 π i t)`.
* `PDE.Analysis.inner_self_eq_ofReal_norm_sq_coef`: For `v` in `ℂ³`, the complex inner product of
  `v` with itself is `‖v‖ ^ 2` as a complex number.

There are 5 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Real
open scoped FourierTransform

namespace PDE.Analysis

/-- For `x`, `y` in `ℂ³`, `‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2` in `ℝ≥0∞`. The inequality for
the real norms follows from the triangle inequality and `(‖x‖ - ‖y‖) ^ 2 ≥ 0`. -/
theorem enorm_add_sq_le_coef (x y : Coef) : ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _)]
  have key : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    have := norm_add_le x y
    nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x + y), sq_nonneg (‖x‖ - ‖y‖)]
  calc ENNReal.ofReal (‖x + y‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal key
    _ = 2 * ENNReal.ofReal (‖x‖ ^ 2) + 2 * ENNReal.ofReal (‖y‖ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        simp

/-- For `v` in `ℂ³`, the extended norm of `v` is at most the sum of the extended norms of its three
coordinates. -/
theorem enorm_le_sum_enorm_apply_coef (v : Coef) : ‖v‖ₑ ≤ ∑ i, ‖v i‖ₑ := by
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (PiLp.norm_le_sum_norm v)

/-- For a real `r` and `v` in `ℂ³`, `‖(r : ℂ) • v‖ₑ = ENNReal.ofReal |r| * ‖v‖ₑ`. -/
theorem enorm_ofReal_smul_coef (r : ℝ) (v : Coef) :
    ‖((r : ℝ) : ℂ) • v‖ₑ = ENNReal.ofReal |r| * ‖v‖ₑ := by
  rw [← ofReal_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    ENNReal.ofReal_mul (abs_nonneg _), ofReal_norm]

/-- For `x`, `y` in `ℂ³`, `‖x - y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2` in `ℝ≥0∞`. The inequality for
the real norms follows from `‖x - y‖ ≤ ‖x‖ + ‖y‖` and `(‖x‖ - ‖y‖) ^ 2 ≥ 0`. -/
theorem enorm_sub_sq_le_coef (x y : Coef) : ‖x - y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have e : ∀ z : Coef, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z ↦ by
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e, e, e]
  have key : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg (x - y), norm_sub_le x y]
  calc ENNReal.ofReal (‖x - y‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal key
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- For a real `t` and `v` in `ℂ³`, the character `𝐞 t` acts on `v` as the complex number
`exp (2 π i t)`. -/
theorem fourierChar_smul_eq_exp_smul_coef (t : ℝ) (v : Coef) :
    𝐞 t • v = Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I) • v := rfl

/-- For `v` in `ℂ³`, the complex inner product of `v` with itself is `‖v‖ ^ 2` as a complex number.
-/
theorem inner_self_eq_ofReal_norm_sq_coef (v : Coef) : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_pow]
  exact inner_self_eq_norm_sq_to_K v

/-- A Lipschitz bound for the complex inner product on `ℂ³`: if `‖a'‖ ≤ M₁`, `‖c‖ ≤ M₂`,
`‖a - a'‖ ≤ L₁ * d` and `‖c - c'‖ ≤ L₂ * d`, then `‖⟪a, c⟫ - ⟪a', c'⟫‖ ≤ (L₁ * M₂ + M₁ * L₂) * d`.
-/
theorem norm_inner_sub_inner_le_coef {a a' c c' : Coef} {M₁ M₂ L₁ L₂ d : ℝ} (ha' : ‖a'‖ ≤ M₁)
    (hc : ‖c‖ ≤ M₂)
    (hda : ‖a - a'‖ ≤ L₁ * d) (hdc : ‖c - c'‖ ≤ L₂ * d) :
    ‖inner ℂ a c - inner ℂ a' c'‖ ≤ (L₁ * M₂ + M₁ * L₂) * d := by
  have h0 : inner ℂ a c - inner ℂ a' c' = inner ℂ (a - a') c + inner ℂ a' (c - c') := by
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [h0]
  refine (norm_add_le _ _).trans ?_
  calc ‖inner ℂ (a - a') c‖ + ‖inner ℂ a' (c - c')‖ ≤ ‖a - a'‖ * ‖c‖ + ‖a'‖ * ‖c - c'‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ L₁ * d * M₂ + M₁ * (L₂ * d) :=
        add_le_add (mul_le_mul hda hc (norm_nonneg _) ((norm_nonneg _).trans hda))
          (mul_le_mul ha' hdc (norm_nonneg _) ((norm_nonneg _).trans ha'))
    _ = _ := by ring

/-- For `a`, `b` in `ℂ³`, `‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2`. -/
theorem norm_sub_sq_le_coef (a b : Coef) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hab := norm_nonneg (a - b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- For `U` in `ℂ³` and three vectors `D i` in `ℂ³`, `‖∑ i, U i • D i‖ ≤ ‖U‖ * √(∑ i, ‖D i‖ ^ 2)`.
-/
theorem norm_sum_smul_le_coef (U : Coef) (D : Fin 3 → Coef) :
    ‖∑ i, U i • D i‖ ≤ ‖U‖ * √(∑ i, ‖D i‖ ^ 2) := by
  calc ‖∑ i, U i • D i‖ ≤ ∑ i, ‖U i‖ * ‖D i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp [norm_smul]
    _ ≤ √(∑ i, ‖U i‖ ^ 2) * √(∑ i, ‖D i‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by rw [EuclideanSpace.norm_eq]

/-- For a real `t` and `z` in `ℂ³`, `‖((2 π i) * t) • z‖ ^ 2 = (2 π) ^ 2 * t ^ 2 * ‖z‖ ^ 2`. -/
theorem norm_two_pi_I_mul_smul_sq_coef (t : ℝ) (z : Coef) :
    ‖((2 * π * Complex.I) * ((t : ℝ) : ℂ)) • z‖ ^ 2 = (2 * π) ^ 2 * t ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_smul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos pi_pos]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, show (2 * π * 1 * |t| * ‖z‖) ^ 2 = (2 * π) ^ 2 * |t| ^ 2 * ‖z‖ ^ 2 by ring, sq_abs]

/-- For a real `r ≥ 0` and `v` in `ℂ³`,
`ENNReal.ofReal r * ‖v‖ₑ ^ 2 = ENNReal.ofReal (r * ‖v‖ ^ 2)`. -/
theorem ofReal_mul_enorm_sq_coef {r : ℝ} (hr : 0 ≤ r) (v : Coef) :
    ENNReal.ofReal r * ‖v‖ₑ ^ 2 = ENNReal.ofReal (r * ‖v‖ ^ 2) := by
  rw [ENNReal.ofReal_mul hr, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- For `x`, `y` in `ℂ³`, the real inner product is the real part of the complex inner product. -/
theorem real_inner_eq_re_inner_coef (x y : Coef) : inner ℝ x y = RCLike.re (inner ℂ x y) := rfl

/-- For a real `r` and `x` in `ℂ³`, the real multiple `r • x` is the complex multiple `(r : ℂ) • x`.
-/
theorem real_smul_eq_ofReal_smul_coef (r : ℝ) (x : Coef) : r • x = (r : ℂ) • x :=
  RCLike.real_smul_eq_coe_smul (K := ℂ) r x

end PDE.Analysis
