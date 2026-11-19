/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import CAS.ExactTactic

/-!
# A finite optical interval for a variable-coefficient wave

The change of coordinate `y = arctan x`, with the multiplier `sqrt (1 + x²)`,
conjugates `(1 + x²)² d²/dx²` to `d²/dy² + 1`. Thus a one-dimensional wave with
this principal coefficient corresponds to `v_tt - v_yy - v = 0`, rather than
the free wave equation. These identities apply to arbitrary differentiable profiles.

The identities concern the nondivergence operator.
-/

@[expose] public noncomputable section

namespace WaveEquation.OpticalConjugation

/-- The first derivative of a weighted pullback under the arctangent coordinate. -/
theorem hasDerivAt_sqrt_mul_comp_arctan {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' (Real.arctan x)) :
    HasDerivAt (fun z ↦ Real.sqrt (1 + z ^ 2) * f (Real.arctan z))
      ((x * f (Real.arctan x) + f') / Real.sqrt (1 + x ^ 2)) x := by
  have hs : HasDerivAt (fun z : ℝ ↦ Real.sqrt (1 + z ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
    cas
  have h := hs.fun_mul (hf.comp x (Real.hasDerivAt_arctan x))
  apply h.congr_deriv
  simp only [Function.comp_apply]
  generalize f (Real.arctan x) = F
  cas

/-- The quartic principal coefficient becomes a constant second derivative plus a potential. -/
theorem coefficient_mul_secondDeriv_sqrt_comp_arctan {f : ℝ → ℝ} (hf : Differentiable ℝ f) {x : ℝ}
    (hf' : DifferentiableAt ℝ (deriv f) (Real.arctan x)) :
    (1 + x ^ 2) ^ 2 * deriv (deriv (fun z ↦ Real.sqrt (1 + z ^ 2) * f (Real.arctan z))) x =
      Real.sqrt (1 + x ^ 2) * (deriv (deriv f) (Real.arctan x) + f (Real.arctan x)) := by
  have hfirst : deriv (fun z ↦ Real.sqrt (1 + z ^ 2) * f (Real.arctan z)) =
        fun z ↦ (z * f (Real.arctan z) + deriv f (Real.arctan z)) /
          Real.sqrt (1 + z ^ 2) := by
    funext z
    exact (hasDerivAt_sqrt_mul_comp_arctan (hf _).hasDerivAt).deriv
  have hs : HasDerivAt (fun z : ℝ ↦ Real.sqrt (1 + z ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
    simpa only [mul_one, add_zero] using
      hasDerivAt_sqrt_mul_comp_arctan (hasDerivAt_const (Real.arctan x) (1 : ℝ))
  have hne : Real.sqrt (1 + x ^ 2) ≠ 0 := by positivity
  have hn := ((hasDerivAt_id x).fun_mul ((hf _).hasDerivAt.comp x (Real.hasDerivAt_arctan x))).add
      (hf'.hasDerivAt.comp x (Real.hasDerivAt_arctan x))
  simp only [Function.comp_def, id_eq, Pi.add_def] at hn
  rw [hfirst, (hn.fun_div hs hne).deriv]
  generalize f (Real.arctan x) = F
  generalize deriv f (Real.arctan x) = D
  generalize deriv (deriv f) (Real.arctan x) = D₂
  clear hf hf' hfirst hs hn
  have hsquare := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  generalize Real.sqrt (1 + x ^ 2) = s at hne hsquare ⊢
  cas using [hne, hsquare]

/-- The exact wave residual after spatial pullback and multiplication.
The time derivatives need no extra hypotheses because multiplication is by a nonzero scalar. -/
theorem wave_residual_sqrt_comp_arctan (v : ℝ → ℝ → ℝ) (t x : ℝ) (hv : Differentiable ℝ (v t))
    (hv' : DifferentiableAt ℝ (deriv (v t)) (Real.arctan x)) :
    deriv (deriv (fun s ↦ Real.sqrt (1 + x ^ 2) * v s (Real.arctan x))) t -
        (1 + x ^ 2) ^ 2 *
          deriv (deriv (fun z ↦ Real.sqrt (1 + z ^ 2) * v t (Real.arctan z))) x =
      Real.sqrt (1 + x ^ 2) *
        (deriv (deriv (fun s ↦ v s (Real.arctan x))) t -
          deriv (deriv (v t)) (Real.arctan x) - v t (Real.arctan x)) := by
  rw [deriv_const_mul_field', deriv_const_mul_field,
    coefficient_mul_secondDeriv_sqrt_comp_arctan hv hv']
  ring

/-- A solution of the transformed equation gives the original nondivergence wave equation. -/
theorem wave_residual_sqrt_comp_arctan_eq_zero (v : ℝ → ℝ → ℝ) (t x : ℝ)
    (hv : Differentiable ℝ (v t)) (hv' : DifferentiableAt ℝ (deriv (v t)) (Real.arctan x))
    (hpde : deriv (deriv (fun s ↦ v s (Real.arctan x))) t - deriv (deriv (v t)) (Real.arctan x) -
      v t (Real.arctan x) = 0) :
    deriv (deriv (fun s ↦ Real.sqrt (1 + x ^ 2) * v s (Real.arctan x))) t - (1 + x ^ 2) ^ 2 *
      deriv (deriv (fun z ↦ Real.sqrt (1 + z ^ 2) * v t (Real.arctan z))) x = 0 := by
  rw [wave_residual_sqrt_comp_arctan v t x hv hv', hpde, mul_zero]

end WaveEquation.OpticalConjugation
