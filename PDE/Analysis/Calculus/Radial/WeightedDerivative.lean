/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Iterated weighted radial differentiation

Evans's odd-dimensional representation repeatedly applies the radial operator

`Dᵣ f(r) = f'(r) / r`.

We define its finite iterate using Mathlib's `Function.iterate` and
prove the second-derivative intertwining identity used to reduce the radial
Euler-Poisson-Darboux equation to the one-dimensional wave equation. These identities come
from Lemma 2 of Evans, §2.4.1(d), whose proof he leaves as an exercise, and from the proof of
his Lemma 3.

## Main results

* `oddRadialTransform_second_deriv`: Lemma 2(i) at positive radii, with `k = m + 1`.
* `deriv_oddRadialTransform_pow_mul_zero`: the derivative at the origin of
  `(r⁻¹ d/dr)^m (r^(2m+1) φ)` is `(2m+1)‼ φ(0)`. This is the consequence of Lemma 2(ii)
  and (iii) that Evans uses after (30) to recover `u(x, t)`.
* `oddRadialTransform_eulerPoissonDarboux`: if `φ'' + (2m+2) φ' / r = ψ` for `r > 0`, then
  the second derivative of `(r⁻¹ d/dr)^m (r^(2m+1) φ)` is `(r⁻¹ d/dr)^m (r^(2m+1) ψ)` there.
  With `ψ = U_tt` this is the computation in the proof of Lemma 3 for `n = 2m + 3`.

## Implementation notes

The operator is analytically meaningful away from the origin.  At `r = 0`,
Lean's totalized division makes `evansRadialDerivative f 0 = 0`; this value is
not a substitute for the regular extension and center-limit theorems needed
for the initial traces in the full odd-dimensional representation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(d), Lemma 2, p. 74, the notation (28) and
  Lemma 3 with its proof, p. 75, and the limit after (30), p. 76.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Filter Set

/-- The radial differentiation operator `f ↦ r⁻¹ f'`.

Its point value at the origin uses totalized division; applications of the
Evans transform should therefore use this operator on positive radii. -/
noncomputable def evansRadialDerivative (f : ℝ → ℝ) : ℝ → ℝ :=
  fun r ↦ deriv f r / r

/-- The `k`-fold Evans radial transform `(r⁻¹ d/dr)^k`. -/
noncomputable def oddRadialTransform (k : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (evansRadialDerivative^[k]) f

/-- The zeroth radial transform is the original profile. -/
@[simp]
theorem oddRadialTransform_zero (f : ℝ → ℝ) :
    oddRadialTransform 0 f = f := by
  rfl

/-- Peel off the innermost radial differentiation. -/
@[simp]
theorem oddRadialTransform_succ (k : ℕ) (f : ℝ → ℝ) :
    oddRadialTransform k.succ f =
      oddRadialTransform k (evansRadialDerivative f) := by
  simpa only [oddRadialTransform] using
    Function.iterate_succ_apply evansRadialDerivative k f

/-- Peel off the outermost radial differentiation. -/
theorem oddRadialTransform_succ' (k : ℕ) (f : ℝ → ℝ) :
    oddRadialTransform k.succ f =
      evansRadialDerivative (oddRadialTransform k f) := by
  simpa only [oddRadialTransform] using
    Function.iterate_succ_apply' evansRadialDerivative k f

/-- Evans's radial derivative preserves odd functions. -/
theorem evansRadialDerivative_odd
    {f : ℝ → ℝ} (hf : Function.Odd f) :
    Function.Odd (evansRadialDerivative f) := by
  intro r
  have hderiv := congrFun (congrArg deriv (funext hf : (fun r ↦ f (-r)) = -f)) r
  rw [deriv_comp_neg, deriv.neg, neg_inj] at hderiv
  simp only [evansRadialDerivative, hderiv, div_neg]

/-- Every finite Evans radial transform preserves oddness. -/
theorem oddRadialTransform_odd
    (k : ℕ) {f : ℝ → ℝ} (hf : Function.Odd f) :
    Function.Odd (oddRadialTransform k f) := by
  induction k generalizing f with
  | zero => exact hf
  | succ k ih => exact ih (evansRadialDerivative_odd hf)

/-- Equality on positive radii is preserved by every finite radial transform. -/
theorem oddRadialTransform_congr_Ioi
    (k : ℕ) {f g : ℝ → ℝ}
    (hfg : EqOn f g (Ioi 0)) :
    EqOn (oddRadialTransform k f) (oddRadialTransform k g) (Ioi 0) := by
  induction k with
  | zero => exact hfg
  | succ k ih =>
    intro r hr
    simp only [oddRadialTransform_succ', evansRadialDerivative,
      (eventuallyEq_of_mem (Ioi_mem_nhds hr) ih).deriv_eq]

/-- A radial EPD expression in divergence form.

If `φ'' + q φ' / r = ψ` at a positive radius, then differentiating
`r^q φ'` and dividing by `r` gives `r^(q-1) ψ`. -/
theorem evansRadialDerivative_weighted_deriv
    (q : ℕ) (hq : 1 ≤ q) {φ ψ : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hregular : DifferentiableAt ℝ (deriv φ) r)
    (hEPD :
      deriv (deriv φ) r +
          ((q : ℝ) / r) * deriv φ r =
        ψ r) :
    evansRadialDerivative
        (fun s ↦ s ^ q * deriv φ s) r =
      r ^ (q - 1) * ψ r := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  unfold evansRadialDerivative
  rw [((hasDerivAt_pow (k + 1) r).fun_mul hregular.hasDerivAt).deriv, ← hEPD, Nat.add_sub_cancel,
    pow_succ]
  field_simp
  ring

/-- The divergence-form EPD reduction survives any number of outer radial
iterations. -/
theorem oddRadialTransform_divergence_reduction
    (k q : ℕ) (hq : 1 ≤ q) {φ ψ : ℝ → ℝ}
    (hregular :
      ∀ r, 0 < r → DifferentiableAt ℝ (deriv φ) r)
    (hEPD :
      ∀ r, 0 < r →
        deriv (deriv φ) r +
            ((q : ℝ) / r) * deriv φ r =
          ψ r) :
    EqOn
      (oddRadialTransform k.succ
        (fun r ↦ r ^ q * deriv φ r))
      (oddRadialTransform k
        (fun r ↦ r ^ (q - 1) * ψ r))
      (Ioi 0) := by
  have hone : EqOn (evansRadialDerivative fun r ↦ r ^ q * deriv φ r)
      (fun r ↦ r ^ (q - 1) * ψ r) (Ioi 0) := fun r hr ↦
    evansRadialDerivative_weighted_deriv q hq hr (hregular r hr) (hEPD r hr)
  simpa only [oddRadialTransform_succ] using oddRadialTransform_congr_Ioi k hone

/-- Differentiating a profile with a cubic or higher radial weight removes the
apparent division at the origin. The identity holds at every signed radius. -/
theorem evansRadialDerivative_pow_mul
    (q : ℕ) (hq : 3 ≤ q) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) :
    evansRadialDerivative (fun r ↦ r ^ q * φ r) =
      fun r ↦
        (q : ℝ) * r ^ (q - 2) * φ r +
          r ^ (q - 1) * deriv φ r := by
  funext r
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 3 := ⟨q - 3, by omega⟩
  simp only [evansRadialDerivative, ((hasDerivAt_pow (k + 3) r).fun_mul
      ((hφ.differentiable one_ne_zero) r).hasDerivAt).deriv,
    show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · field_simp
    ring

/-- Lowering the transform order replaces the profile by
`(2m+3) φ + r φ'`. The weight makes this identity valid also at zero. -/
theorem oddRadialTransform_step
    (m : ℕ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    oddRadialTransform (m + 1)
        (fun r ↦ r ^ (2 * m + 3) * φ r) =
      oddRadialTransform m
        (fun r ↦
          r ^ (2 * m + 1) *
            ((2 * m + 3 : ℝ) * φ r + r * deriv φ r)) := by
  rw [oddRadialTransform_succ, evansRadialDerivative_pow_mul (2 * m + 3) (by omega) hφ]
  congr 1 with r
  rw [show 2 * m + 3 - 2 = 2 * m + 1 by omega, show 2 * m + 3 - 1 = 2 * m + 1 + 1 by omega,
    pow_succ]
  push_cast
  ring

/-- The center derivative of Evans's radial transform.

For a sufficiently regular scalar profile `φ`, applying
`(r⁻¹ d/dr)^m` to `r^(2m+1) φ(r)` and then differentiating at the origin
extracts `(2m+1)‼ φ(0)`.  This is the algebraic center-trace identity behind
the normalization in the odd-dimensional wave formula. -/
theorem deriv_oddRadialTransform_pow_mul_zero
    (m : ℕ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (m + 1) φ) :
    deriv
        (oddRadialTransform m
          (fun r ↦ r ^ (2 * m + 1) * φ r)) 0 =
      (Nat.doubleFactorial (2 * m + 1) : ℝ) * φ 0 := by
  induction m generalizing φ with
  | zero =>
    simpa [Nat.doubleFactorial] using
      ((hasDerivAt_id' 0).fun_mul (hφ.differentiable (by norm_num) 0).hasDerivAt).deriv
  | succ m ih =>
    have hψ : ContDiff ℝ (m + 1) fun r ↦ (2 * m + 3 : ℝ) * φ r + r * deriv φ r :=
      (contDiff_const.mul (hφ.of_le (by exact_mod_cast (show m + 1 ≤ m + 1 + 1 by omega)))).add
        (contDiff_id.mul (contDiff_succ_iff_deriv.mp hφ).2.2)
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega,
      oddRadialTransform_step m (hφ.of_le (by exact_mod_cast (show 1 ≤ m + 1 + 1 by omega))),
      ih hψ, show 2 * m + 3 = 2 * m + 1 + 2 by omega, Nat.doubleFactorial_add_two]
    push_cast
    ring

private theorem deriv_oddRadialProfile
    (m : ℕ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    deriv (fun r ↦ (2 * m + 3 : ℝ) * φ r + r * deriv φ r) =
      fun r ↦
        (2 * m + 4 : ℝ) * deriv φ r +
          r * deriv (deriv φ) r := by
  funext r
  rw [(((hφ.differentiable (by norm_num) r).hasDerivAt.const_mul _).fun_add
    ((hasDerivAt_id' r).fun_mul (hφ.differentiable_deriv_two r).hasDerivAt)).deriv]
  ring

/-- Two ordinary derivatives of the `m`-fold Evans transform equal one
additional radial transform applied to the differentiated profile. -/
theorem oddRadialTransform_second_deriv
    (m : ℕ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (m + 2) φ)
    {r : ℝ} (hr : 0 < r) :
    deriv
        (deriv
          (oddRadialTransform m
            (fun s ↦ s ^ (2 * m + 1) * φ s))) r =
      oddRadialTransform (m + 1)
        (fun s ↦ s ^ (2 * m + 2) * deriv φ s) r := by
  induction m generalizing φ r with
  | zero =>
    have hφ₁ : Differentiable ℝ φ := hφ.differentiable (by norm_num)
    have hφ₂ : Differentiable ℝ (deriv φ) := hφ.differentiable_deriv_two
    have hfirst : deriv (fun s ↦ s * φ s) = fun s ↦ φ s + s * deriv φ s := funext fun s ↦ by
      simpa using ((hasDerivAt_id' s).fun_mul (hφ₁ s).hasDerivAt).deriv
    rw [show 2 * 0 + 1 = 1 by omega, show 2 * 0 + 2 = 2 by omega, oddRadialTransform_zero,
      oddRadialTransform_succ 0, oddRadialTransform_zero]
    simp only [pow_one, evansRadialDerivative, hfirst, ((hφ₁ r).hasDerivAt.fun_add
      ((hasDerivAt_id' r).fun_mul (hφ₂ r).hasDerivAt)).deriv,
      ((hasDerivAt_pow 2 r).fun_mul (hφ₂ r).hasDerivAt).deriv]
    field_simp
    ring
  | succ m ih =>
    have hφd : ContDiff ℝ (m + 2) (deriv φ) := (contDiff_succ_iff_deriv.mp hφ).2.2
    have hprofile : ContDiff ℝ (m + 2) fun s ↦ (2 * m + 3 : ℝ) * φ s + s * deriv φ s :=
      (contDiff_const.mul (hφ.of_le (by exact_mod_cast (show m + 2 ≤ m + 1 + 2 by omega)))).add
        (contDiff_id.mul hφd)
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega, show 2 * (m + 1) + 2 = 2 * m + 4 by omega,
      oddRadialTransform_step m (hφ.of_le (by exact_mod_cast (show 1 ≤ m + 1 + 2 by omega))),
      ih hprofile hr,
      deriv_oddRadialProfile m (hφ.of_le (by exact_mod_cast (show 2 ≤ m + 1 + 2 by omega))),
      oddRadialTransform_succ (m + 1), evansRadialDerivative_pow_mul (2 * m + 4) (by omega)
        (hφd.of_le (by exact_mod_cast (show 1 ≤ m + 2 by omega)))]
    congr 2 with s
    rw [show 2 * m + 4 - 2 = 2 * m + 2 by omega, show 2 * m + 4 - 1 = 2 * m + 2 + 1 by omega,
      pow_succ]
    push_cast
    ring

/-- The Evans reduction for dimension `2 * m + 3`.

An EPD profile with coefficient `(2m+2)/r` becomes a one-dimensional wave
profile after multiplying by `r^(2m+1)` and applying the radial transform
`m` times. -/
theorem oddRadialTransform_eulerPoissonDarboux
    (m : ℕ) {φ ψ : ℝ → ℝ}
    (hφ : ContDiff ℝ (m + 2) φ)
    (hEPD :
      ∀ r, 0 < r →
        deriv (deriv φ) r +
            (((2 * m + 2 : ℕ) : ℝ) / r) * deriv φ r =
          ψ r)
    {r : ℝ} (hr : 0 < r) :
    deriv
        (deriv
          (oddRadialTransform m
            (fun s ↦ s ^ (2 * m + 1) * φ s))) r =
      oddRadialTransform m
        (fun s ↦ s ^ (2 * m + 1) * ψ s) r := by
  rw [oddRadialTransform_second_deriv m hφ hr, oddRadialTransform_succ]
  exact oddRadialTransform_congr_Ioi m (fun s hs ↦ by
    simpa only [show 2 * m + 2 - 1 = 2 * m + 1 by omega] using
      evansRadialDerivative_weighted_deriv (2 * m + 2) (by omega) hs
        ((hφ.of_le (by exact_mod_cast (show 2 ≤ m + 2 by omega))).differentiable_deriv_two s)
        (hEPD s hs)) hr

end PDE.Analysis
