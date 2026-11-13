/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Polar.Laplacian
public import PDE.FDeriv.Polar.Homogeneous
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Higher regularity of the radial cutoff commutator

The commutator `Δ(χ(r) r^m f(β)) - χ(r) Δ(r^m f(β))` of a radial cutoff is
`R(r) f(β)` with `R = r^m (χ'' + χ'/r) + 2m r^(m-1) χ'` (`polarCutoffRadialFactor`). When `χ` is
locally constant at the origin, `R` vanishes there, so a `C^(n+2)` cutoff gives a `Cⁿ` factor `R`
and, with a `Cⁿ` angular factor, a commutator that is `Cⁿ` within the closed upper half-plane.

## Main results

* `contDiff_polarCutoffRadialFactor_of_contDiff`: a `C^(n+2)` cutoff locally constant at the
  origin gives a `Cⁿ` factor `R`.
* `contDiffOn_polarCutoffCommutator_of_contDiff`: with a `Cⁿ` angular factor the commutator is
  `Cⁿ` within the closed upper half-plane.
-/

@[expose] public noncomputable section

open Filter PDE.CoordinateSystems
open scoped Topology

namespace EuclideanLaplacian

/-- A `C^(n+2)` cutoff locally constant at the origin gives a `Cⁿ` radial commutator factor. -/
theorem contDiff_polarCutoffRadialFactor_of_contDiff {χ : ℝ → ℝ} {n : ℕ}
    (hχ : ContDiff ℝ (n + 2 : ℕ) χ) {c : ℝ} (hflat : χ =ᶠ[𝓝 0] fun _ ↦ c) (m : ℝ) :
    ContDiff ℝ n (polarCutoffRadialFactor χ m) := by
  have hfirst : ContDiff ℝ (n + 1 : ℕ) (deriv χ) := by
    have h : ContDiff ℝ ((n + 1 : ℕ) + 1) χ := by exact_mod_cast hχ
    exact h.deriv'
  have hsecond : ContDiff ℝ n (deriv (deriv χ)) := by
    have h : ContDiff ℝ (n + 1) (deriv χ) := by exact_mod_cast hfirst
    exact h.deriv'
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : r = 0
  · subst r
    exact contDiffAt_const.congr_of_eventuallyEq (polarCutoffRadialFactor_zero_near_zero hflat m)
  · have hlap : ContDiffAt ℝ n (radialLaplacian 2 χ) r :=
      hsecond.contDiffAt.add ((contDiffAt_const.div contDiffAt_id hr).mul
        (hfirst.of_le (by norm_cast; omega)).contDiffAt)
    have hpow : ContDiffAt ℝ n (fun s : ℝ ↦ s ^ m) r := Real.contDiffAt_rpow_const_of_ne hr
    have hpow' : ContDiffAt ℝ n (fun s : ℝ ↦ s ^ (m - 1)) r := Real.contDiffAt_rpow_const_of_ne hr
    exact (hpow.mul hlap).add
      ((contDiffAt_const.mul hpow').mul (hfirst.of_le (by norm_cast; omega)).contDiffAt)

/-- With a `C^(n+2)` cutoff locally constant at the origin and a `Cⁿ` angular factor, the cutoff
commutator is `Cⁿ` within the closed upper half-plane. -/
theorem contDiffOn_polarCutoffCommutator_of_contDiff {χ f : ℝ → ℝ} {n : ℕ}
    (hχ : ContDiff ℝ (n + 2 : ℕ) χ) (hf : ContDiff ℝ n f) {c : ℝ}
    (hflat : χ =ᶠ[𝓝 0] fun _ ↦ c) (m : ℝ) :
    ContDiffOn ℝ n (polarCutoffCommutator χ f m) {x : ℝ^2 | 0 ≤ x 1} := by
  have heq : polarCutoffCommutator χ f m = PDE.FDeriv.profileFromPolar
      (fun r β ↦ polarCutoffRadialFactor χ m r * (r ^ (0 : ℝ) * f β)) := by
    rw [polarCutoffCommutator_eq_radial_mul]
    simp only [Real.rpow_zero, one_mul]
  obtain ⟨U, -, hsub, h, hh, hEq⟩ :=
    PDE.FDeriv.exists_contDiffOn_extension_profileFromPolar_cutoff_rpow_mul
      (contDiff_polarCutoffRadialFactor_of_contDiff hχ hflat m) hf
      (polarCutoffRadialFactor_zero_near_zero hflat m) 0
  rw [heq]
  exact (hh.mono hsub).congr fun x hx ↦ (hEq hx).symm

end EuclideanLaplacian
