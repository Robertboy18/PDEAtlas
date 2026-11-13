/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import CAS.ExactTactic

/-!
# Radial differential operators

The dimension-dependent radial part of the Euclidean Laplacian and elementary calculations for
logarithmic and power profiles, together with a radial completion operator in the
compactified coordinate `β`. Its action on trigonometric modes is an exact three-term
frequency recurrence.

For a profile `f : ℝ → ℝ`, the expression
`f''(r) + (n - 1) / r * f'(r)` represents the Laplacian of `x ↦ f ‖x‖` away from the origin.
Division on `ℝ` is total, so `radialLaplacian` also has a value at `r = 0`. The identities below
assume `r > 0` where they need it. The dimension `n` may be zero, but the expression is the
Laplacian of a radial function only in positive dimension.

For `u(x) = v(|x|)` this is the formula `Δu = v'' + (n - 1)/r v'` of Evans, §2.2.1(a), whose
vanishing is (5) there. With `radialLaplacian_log` and `radialLaplacian_rpow` for `p = 2 - n`, it
gives the radial solutions `log r` (`n = 2`) and `r^(2-n)` (`n ≥ 3`) found there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(a), (5), pp. 21-22.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.CoordinateSystems

open Real
open scoped BigOperators

/-- The dimension-`n` radial Laplacian of a one-variable profile.

Away from `r = 0`, this is `f''(r) + (n - 1) / r * f'(r)`. -/
def radialLaplacian (n : ℕ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv f) r + ((n : ℝ) - 1) / r * deriv f r

/-- The logarithmic profile has zero two-dimensional radial Laplacian at positive radii. -/
theorem radialLaplacian_log (r : ℝ) (hr : 0 < r) :
    radialLaplacian 2 log r = 0 := by
  unfold radialLaplacian
  cas

/-- Radial Laplacian of a real power at positive radii. -/
theorem radialLaplacian_rpow (n : ℕ) (r : ℝ) (hr : 0 < r) (p : ℝ) :
    radialLaplacian n (fun s ↦ s ^ p) r =
      p * (p + (n : ℝ) - 2) * r ^ (p - 2) := by
  unfold radialLaplacian
  have hfirst : deriv (fun s : ℝ ↦ s ^ p) r = p * r ^ (p - 1) := by
    cas
  have hsecond :
      deriv (deriv (fun s : ℝ ↦ s ^ p)) r = p * (p - 1) * r ^ (p - 2) := by
    simpa [Function.iterate_succ_apply, descPochhammer_succ_right] using
      (Real.iter_deriv_rpow_const p r 2)
  rw [hsecond, hfirst]
  have hpow : r ^ (p - 1) = r ^ (p - 2) * r := by
    simpa only [show (p - 2) + 1 = p - 1 by ring] using
      (Real.rpow_add_one (x := r) (hx := ne_of_gt hr) (y := p - 2))
  rw [hpow]
  field_simp [ne_of_gt hr]
  ring

/-- Multiplication by a constant commutes with the radial Laplacian. -/
theorem radialLaplacian_const_mul (n : ℕ) (c : ℝ) (f : ℝ → ℝ) (r : ℝ) :
    radialLaplacian n (fun s ↦ c * f s) r = c * radialLaplacian n f r := by
  simp only [radialLaplacian, deriv_const_mul_field']
  ring

/-- Product rule for the radial Laplacian at a point where both factors are twice
differentiable. -/
theorem radialLaplacian_mul (n : ℕ) (f g : ℝ → ℝ) (r : ℝ)
    (hf : ContDiffAt ℝ 2 f r) (hg : ContDiffAt ℝ 2 g r) :
    radialLaplacian n (fun s ↦ f s * g s) r =
      f r * radialLaplacian n g r + g r * radialLaplacian n f r +
        2 * deriv f r * deriv g r := by
  have hfirst :
      deriv (fun s ↦ f s * g s) r =
        deriv f r * g r + f r * deriv g r :=
    deriv_fun_mul (hf.differentiableAt (by norm_num))
      (hg.differentiableAt (by norm_num))
  have hsecond :
      deriv (deriv (fun s ↦ f s * g s)) r =
        deriv (deriv f) r * g r + 2 * deriv f r * deriv g r +
          f r * deriv (deriv g) r := by
    change deriv (deriv (f * g)) r = _
    have h := iteratedDeriv_mul (n := 2) hf hg
    norm_num [iteratedDeriv_succ', Finset.sum_range_succ, Pi.mul_apply] at h
    simpa [add_assoc, add_comm, add_left_comm] using h
  rw [radialLaplacian, radialLaplacian, radialLaplacian, hfirst, hsecond]
  ring

/-- Every constant profile has zero radial Laplacian. -/
@[simp] theorem radialLaplacian_const (n : ℕ) (c r : ℝ) :
    radialLaplacian n (fun _ ↦ c) r = 0 := by
  simp [radialLaplacian]

/-- In dimension three, dividing a profile by the radius removes the first-order term of the
radial Laplacian: `Δ(f(r)/r) = f''(r)/r` away from the origin. -/
theorem radialLaplacian_three_div {f : ℝ → ℝ} {r : ℝ}
    (hf : ContDiffAt ℝ 2 f r) (hr : r ≠ 0) :
    radialLaplacian 3 (fun s ↦ f s / s) r = deriv (deriv f) r / r := by
  have hi : ContDiffAt ℝ 2 (fun s : ℝ ↦ s⁻¹) r := contDiffAt_id.inv hr
  have hd : deriv (fun s : ℝ ↦ s⁻¹) r = -(r ^ 2)⁻¹ := by cas using hr
  have hl : radialLaplacian 3 (fun s : ℝ ↦ s⁻¹) r = 0 := by
    unfold radialLaplacian
    cas using hr
  simp only [div_eq_mul_inv]
  rw [radialLaplacian_mul 3 f _ r hf hi, hl, hd]
  unfold radialLaplacian
  cas using hr

/-- First-order radial expression in the compactified coordinate `β`.

This operator is designed for profiles with cosine decay and the change of radius
`ρ = s * tan β`, where `s ≠ 0` and `cos β ≠ 0`. The factorization theorem below is
stated directly in `β`; identification of the physical radial derivative requires
the coordinate-change rule. -/
def compactifiedRadialCompletion (f : ℝ → ℝ) (β : ℝ) : ℝ :=
  (1 + Real.cos β ^ 2) * f β + Real.sin β * Real.cos β * deriv f β

/-- The cosine decay factor separates from the radial first-order expression. -/
theorem cos_mul_compactifiedRadialCompletion {f : ℝ → ℝ} {β : ℝ}
    (hf : DifferentiableAt ℝ f β) :
    Real.cos β * compactifiedRadialCompletion f β =
      Real.sin β * Real.cos β * deriv (fun x ↦ Real.cos x * f x) β +
        2 * (Real.cos β * f β) := by
  rw [deriv_fun_mul Real.differentiableAt_cos hf, Real.deriv_cos]
  unfold compactifiedRadialCompletion
  have hs := Real.sin_sq_add_cos_sq β
  linear_combination Real.cos β * f β * hs

/-- Completion distributes over a finite sum of locally differentiable functions. -/
theorem compactifiedRadialCompletion_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (β : ℝ)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) β) :
    compactifiedRadialCompletion (fun x ↦ ∑ i ∈ s, f i x) β =
      ∑ i ∈ s, compactifiedRadialCompletion (f i) β := by
  unfold compactifiedRadialCompletion
  rw [deriv_fun_sum hf, Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]

/-- Constant scaling commutes with radial completion, including the zero scalar. -/
theorem compactifiedRadialCompletion_const_mul (c : ℝ) (f : ℝ → ℝ) (β : ℝ) :
    compactifiedRadialCompletion (fun x ↦ c * f x) β = c * compactifiedRadialCompletion f β := by
  unfold compactifiedRadialCompletion
  rw [deriv_const_mul_field]
  ring

/-- A sine mode is shifted only to the two neighboring frequencies. -/
theorem compactifiedRadialCompletion_sin (k β : ℝ) :
    compactifiedRadialCompletion (fun x ↦ Real.sin (k * x)) β =
      (3 / 2 : ℝ) * Real.sin (k * β) +
        ((k + 1) / 4) * Real.sin ((k + 2) * β) +
        ((1 - k) / 4) * Real.sin ((k - 2) * β) := by
  have hd : deriv (fun x : ℝ ↦ Real.sin (k * x)) β =
      k * Real.cos (k * β) := by cas
  unfold compactifiedRadialCompletion
  rw [hd, show (k + 2) * β = k * β + 2 * β by ring,
    show (k - 2) * β = k * β - 2 * β by ring,
    Real.sin_add, Real.sin_sub, Real.sin_two_mul, Real.cos_two_mul]
  ring

/-- Cosine modes have the same frequency-shift coefficients as sine modes. -/
theorem compactifiedRadialCompletion_cos (k β : ℝ) :
    compactifiedRadialCompletion (fun x ↦ Real.cos (k * x)) β =
      (3 / 2 : ℝ) * Real.cos (k * β) +
        ((k + 1) / 4) * Real.cos ((k + 2) * β) +
        ((1 - k) / 4) * Real.cos ((k - 2) * β) := by
  have hd : deriv (fun x : ℝ ↦ Real.cos (k * x)) β =
      -k * Real.sin (k * β) := by cas
  unfold compactifiedRadialCompletion
  rw [hd, show (k + 2) * β = k * β + 2 * β by ring,
    show (k - 2) * β = k * β - 2 * β by ring,
    Real.cos_add, Real.cos_sub, Real.sin_two_mul, Real.cos_two_mul]
  ring

/-- Completion of an arbitrary finite sine expansion is an exact neighboring-mode sum. -/
theorem compactifiedRadialCompletion_sum_sin {ι : Type*} (s : Finset ι) (a k : ι → ℝ) (β : ℝ) :
    compactifiedRadialCompletion (fun x ↦ ∑ i ∈ s, a i * Real.sin (k i * x)) β =
      ∑ i ∈ s, a i * ((3 / 2 : ℝ) * Real.sin (k i * β) +
        ((k i + 1) / 4) * Real.sin ((k i + 2) * β) +
        ((1 - k i) / 4) * Real.sin ((k i - 2) * β)) := by
  rw [compactifiedRadialCompletion_sum s (fun i x ↦ a i * Real.sin (k i * x)) β
    (fun i _ ↦ ((hasDerivAt_const_mul (k i)).sin.const_mul (a i)).differentiableAt)]
  apply Finset.sum_congr rfl
  intro i _
  rw [compactifiedRadialCompletion_const_mul, compactifiedRadialCompletion_sin]

/-- Completion of a finite cosine expansion uses the same three-term mode stencil. -/
theorem compactifiedRadialCompletion_sum_cos {ι : Type*} (s : Finset ι) (a k : ι → ℝ) (β : ℝ) :
    compactifiedRadialCompletion (fun x ↦ ∑ i ∈ s, a i * Real.cos (k i * x)) β =
      ∑ i ∈ s, a i * ((3 / 2 : ℝ) * Real.cos (k i * β) +
        ((k i + 1) / 4) * Real.cos ((k i + 2) * β) +
        ((1 - k i) / 4) * Real.cos ((k i - 2) * β)) := by
  rw [compactifiedRadialCompletion_sum s (fun i x ↦ a i * Real.cos (k i * x)) β
    (fun i _ ↦ ((hasDerivAt_const_mul (k i)).cos.const_mul (a i)).differentiableAt)]
  apply Finset.sum_congr rfl
  intro i _
  rw [compactifiedRadialCompletion_const_mul, compactifiedRadialCompletion_cos]

end PDE.CoordinateSystems

end
