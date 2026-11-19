/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.LaxOrientation
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The two orientations of a genuinely nonlinear shock curve

The half-speed derivative and a nonzero characteristic derivative exclude equality
with either endpoint speed at every sufficiently small nonzero strength.

This is the dichotomy between (40) and (41) of Evans, §11.2.3(b), which Evans derives from
(38)-(39) and Theorem 2(iii) for `u_r ∈ S_k(u_l)` close to `u_l`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.3, Theorem 2(iii) and equations (35)-(41).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter
open scoped Topology

/-- A small nonzero strength gives either both strict Lax inequalities or both
strict reverse inequalities. -/
theorem eventually_lax_or_reverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {q v : E}
    {eig : E → ℝ} {S : ℝ → E} {speed : ℝ → ℝ} (heig : DifferentiableAt ℝ eig q) (hS₀ : S 0 = q)
    (hspeed₀ : speed 0 = eig q) (hS : HasDerivAt S v 0)
    (hhalf : HasDerivAt speed ((1 / 2 : ℝ) * fderiv ℝ eig q v) 0) (hc : fderiv ℝ eig q v ≠ 0) :
    ∀ᶠ s in 𝓝 0, s ≠ 0 → (eig (S s) < speed s ∧ speed s < eig q) ∨
      (eig q < speed s ∧ speed s < eig (S s)) := by
  have hnegD : fderiv ℝ (fun x ↦ -eig x) q v = -fderiv ℝ eig q v := by
    simp only [fderiv_fun_neg, neg_apply]
  have hnegHalf : HasDerivAt (fun s ↦ -speed s)
      ((1 / 2 : ℝ) * fderiv ℝ (fun x ↦ -eig x) q v) 0 := by
    simpa only [hnegD, mul_neg] using hhalf.fun_neg
  have hneg := eventually_lax_iff_mul_neg
    (eig := fun x ↦ -eig x) (speed := fun s ↦ -speed s) heig.fun_neg hS₀
    (congrArg Neg.neg hspeed₀) hS hnegHalf (by simpa only [hnegD, neg_ne_zero] using hc)
  filter_upwards [eventually_lax_iff_mul_neg heig hS₀ hspeed₀ hS hhalf hc, hneg] with s hs hns hsne
  rcases lt_or_gt_of_ne (mul_ne_zero hc hsne) with hlt | hgt
  · exact Or.inl (hs.mpr hlt)
  · have hn : fderiv ℝ (fun x ↦ -eig x) q v * s < 0 := by
      simpa only [hnegD, neg_mul, neg_lt_zero] using hgt
    have hreverse := hns.mpr hn
    exact Or.inr ⟨neg_lt_neg_iff.mp hreverse.2, neg_lt_neg_iff.mp hreverse.1⟩

end PDE.Hyperbolic.ConservationLaw.System
