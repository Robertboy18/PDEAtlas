/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.EnergyMethods.Dirichlet.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Cauchy–Schwarz estimate for the Dirichlet integral

`|∫_U ∇u · ∇v| ≤ (∫_U ‖∇u‖²)^(1/2) (∫_U ‖∇v‖²)^(1/2)`, the integral pairing of two gradients
bounded by the geometric mean of their Dirichlet integrals. The hypotheses are `L²` membership
of the two gradient fields.
-/

open scoped Gradient

@[expose] public section

namespace Energy

variable {n : ℕ}

/-- Cauchy–Schwarz for the gradient L² inner product. -/
theorem cauchy_schwarz_gradient_integral {U : Set (ℝ^n)}
    {u v : ℝ^n → ℝ}
    (hu : MeasureTheory.MemLp (fun x ↦ ∇ u x) 2 (MeasureTheory.volume.restrict U))
    (hv : MeasureTheory.MemLp (fun x ↦ ∇ v x) 2
      (MeasureTheory.volume.restrict U)) :
    |gradientL2InnerProduct U u v| ≤
      √(dirichletEnergy U u) * √(dirichletEnergy U v) := by
  have hinner {f g : ℝ^n → ℝ^n}
      (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict U))
      (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict U)) :
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x in U, inner ℝ (f x) (g x) := by
    rw [MeasureTheory.L2.inner_def]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
  have h := abs_real_inner_le_norm (hu.toLp (∇ u)) (hv.toLp (∇ v))
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    hinner hu hv, hinner hu hu, hinner hv hv] at h
  simpa only [real_inner_self_eq_norm_sq, gradientL2InnerProduct, dirichletEnergy] using h

end Energy
