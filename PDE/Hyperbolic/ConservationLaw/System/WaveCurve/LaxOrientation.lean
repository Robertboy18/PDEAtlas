/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Signed Lax orientation at zero wave strength

The shock-speed derivative is half the characteristic-speed derivative along
the shock curve. Consequently, both differences in the strict Lax inequalities
have the same first-order sign. The equivalence permits either orientation
of the curve and uses only derivatives at zero, not regularity on a neighborhood.
The full neighborhood includes zero strength, where both sides are false.

The half-speed hypothesis is the derivative at zero strength of the expansion
`σ(z, z₀) = (λ_k(z) + λ_k(z₀))/2 + O(|z - z₀|²)` of Evans, §11.2.3, Theorem 2(iii). The strict
Lax inequalities are the Lax entropy condition (42) of §11.2.3(b), so the equivalence tells
which sign of the strength gives (40) rather than (41), that is, which branch of the shock
curve is `S_k^-(z₀)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.3, Theorem 2(iii), equations (40)-(42) and the
  definitions of `S_k^±(z₀)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter
open scoped Topology

/-- The strict Lax inequalities hold locally exactly when the wave strength
has opposite sign to the characteristic-speed derivative along the curve.
The half-factor is a derivative hypothesis, and zero strength is included. -/
theorem eventually_lax_iff_mul_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {q v : E}
    {eig : E → ℝ} {S : ℝ → E} {speed : ℝ → ℝ} (heig : DifferentiableAt ℝ eig q) (hS₀ : S 0 = q)
    (hspeed₀ : speed 0 = eig q) (hS : HasDerivAt S v 0)
    (hhalf : HasDerivAt speed ((1 / 2 : ℝ) * fderiv ℝ eig q v) 0) (hc : fderiv ℝ eig q v ≠ 0) :
    ∀ᶠ s in 𝓝 0, (eig (S s) < speed s ∧ speed s < eig q) ↔ fderiv ℝ eig q v * s < 0 := by
  let c := fderiv ℝ eig q v
  have hsign {f : ℝ → ℝ} (hf : HasDerivAt f ((1 / 2 : ℝ) * c) 0) (hf₀ : f 0 = 0) :
      ∀ᶠ s in 𝓝 0, f s < 0 ↔ c * s < 0 := by
    rcases lt_or_gt_of_ne (show c ≠ 0 from hc) with hneg | hpos
    · have hd : deriv f 0 < 0 := by
        rw [hf.deriv]
        exact mul_neg_of_pos_of_neg (by norm_num) hneg
      filter_upwards [eventually_nhdsWithin_sign_eq_of_deriv_neg hd hf₀] with s hs
      rw [← sign_eq_neg_one_iff, hs, sign_eq_neg_one_iff, zero_sub, neg_lt_zero]
      simp only [mul_neg_iff, hneg, not_lt_of_ge hneg.le, false_and, true_and, false_or]
    · have hd : 0 < deriv f 0 := by
        rw [hf.deriv]
        exact mul_pos (by norm_num) hpos
      filter_upwards [eventually_nhdsWithin_sign_eq_of_deriv_pos hd hf₀] with s hs
      rw [← sign_eq_neg_one_iff, hs, sign_eq_neg_one_iff, sub_zero]
      simp only [mul_neg_iff, hpos, not_lt_of_ge hpos.le, false_and, true_and, or_false]
  have hd : HasFDerivAt eig (fderiv ℝ eig q) (S 0) := hS₀.symm ▸ heig.hasFDerivAt
  have hright : HasDerivAt (fun s ↦ eig (S s) - speed s) ((1 / 2 : ℝ) * c) 0 := by
    convert (hd.comp_hasDerivAt (0 : ℝ) hS).sub hhalf using 1
    · rfl
    · dsimp [c]
      ring
  filter_upwards [hsign hright (by simp only [hS₀, hspeed₀, sub_self]),
    hsign (hhalf.sub_const (eig q)) (by simp only [hspeed₀, sub_self])] with s hs ht
  simpa only [sub_lt_zero, and_self] using hs.and ht

end PDE.Hyperbolic.ConservationLaw.System
