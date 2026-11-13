/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.Pohozaev
import CAS.ExactTactic

/-!
# The cubic Pohozaev obstruction

A compactly supported `C²` solution of `-Δu = u³` on `ℝ^n` is zero when `n ≠ 4`.
Testing the equation against `u` gives `∫ |Du|² = ∫ u⁴`, whereas Pohozaev's identity gives
`(n - 2) ∫ |Du|² = n / 2 * ∫ u⁴`. Thus `(n - 4) ∫ u⁴ = 0`.

For `n > 4`, the cubic exponent is supercritical in the sense of Evans, §9.4.2, (13), and the
identity above is the Derrick–Pohozaev identity (18) there, whose boundary term vanishes for compact
support. Compact support in all of `ℝ^n` also makes the argument work below dimension four. At
dimension four the two identities agree and give no information.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.2, (11)-(13), Theorem 3 and the Derrick–Pohozaev
  identity (18), pp. 551-554.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

open MeasureTheory PDE.DistributionTheory PDE.Elliptic.Semilinear

namespace PDE.Examples.PohozaevCubic

/-- A compactly supported classical solution of `-Δu = u³` vanishes outside the critical
scaling dimension four. The conclusion is pointwise equality, obtained from continuity after
the nonnegative, integrable fourth power has integral zero. -/
theorem eq_zero_of_compactSupport_cubic {n : ℕ} (hn : n ≠ 4) {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ 2 u) (hcompact : HasCompactSupport u)
    (heq : ∀ x, -laplacian u x = u x ^ 3) : u = 0 := by
  have hF : ContDiff ℝ 1 (fun s : ℝ ↦ s ^ 4 / 4) := (contDiff_id.pow 4).div_const 4
  have hderiv (s : ℝ) : deriv (fun a : ℝ ↦ a ^ 4 / 4) s = s ^ 3 := by
    cas
  have hpde (x : ℝ^n) : -laplacian u x = deriv (fun a : ℝ ↦ a ^ 4 / 4) (u x) := by
    rw [hderiv]
    exact heq x
  have hp := integral_pohozaev_eq hu hcompact hF (by norm_num) hpde
  rw [integral_div] at hp
  have hi := integral_mul_laplacian_self_eq hu hcompact
  have henergyIntegrand : (fun x ↦ u x * laplacian u x) = fun x ↦ -(u x ^ 4) := by
    funext x
    have hx : laplacian u x = -(u x ^ 3) := by linarith [heq x]
    rw [hx]
    ring
  rw [henergyIntegrand, integral_neg] at hi
  have he : (∫ x, ‖∇ u x‖ ^ 2) = ∫ x, u x ^ 4 := by linarith
  rw [he] at hp
  have hnreal : (n : ℝ) - 4 ≠ 0 := by
    intro h
    apply hn
    exact_mod_cast (show (n : ℝ) = 4 by linarith)
  have hproduct : ((n : ℝ) - 4) * (∫ x, u x ^ 4) = 0 := by nlinarith [hp]
  have hzero : (∫ x, u x ^ 4) = 0 := (mul_eq_zero.mp hproduct).resolve_left hnreal
  have hfour : Integrable (fun x ↦ u x ^ 4) := by
    have hc : Continuous (fun x : ℝ^n ↦ u x ^ 4) := by
      have hbase : Continuous (fun x : ℝ^n ↦ u x) := hu.continuous
      exact (continuous_pow 4).comp hbase
    have hsupport : HasCompactSupport (fun x : ℝ^n ↦ u x ^ 4) :=
      hcompact.comp_left (g := fun s : ℝ ↦ s ^ 4) (by norm_num)
    exact hc.integrable_of_hasCompactSupport hsupport
  have hae : (fun x ↦ u x ^ 4) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x ↦ by positivity) hfour).mp hzero
  have hau : u =ᵐ[volume] 0 := by
    filter_upwards [hae] with x hx
    change u x ^ 4 = 0 at hx
    change u x = 0
    exact eq_zero_of_pow_eq_zero hx
  exact Measure.eq_of_ae_eq hau hu.continuous continuous_const

end PDE.Examples.PohozaevCubic

end
