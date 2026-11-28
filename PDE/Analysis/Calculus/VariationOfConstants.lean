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

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import PDE.Analysis.Complex.Definitions

set_option linter.style.header false

/-!
# The formula of variation of constants for a linear equation in `ℂ³`

For `c` and `B` continuous on a closed interval and `c` differentiable inside with `c' = -l c - B`,
the function `s ↦ exp (l s) c s` has the derivative `-exp (l s) B s`, so the fundamental theorem of
calculus gives `c t = exp (-l (t - a)) c a - ∫ exp (-l (t - s)) B s`. The module states the formula
from a general initial time and from the time zero.

## Main results

* `PDE.Analysis.variation_of_constants_coef`: The formula of variation of constants in `ℂ³`. Let
  `a ≤ t` and let `c`, `B : ℝ → ℂ³` be continuous on `[a, t]` with `c' s = -l • c s - B s` for `s`
  in `(a, t)`. Then `c t = exp (-l (t - a)) • c a + ∫ s in a..t, -exp (-l (t - s)) • B s`.
* `PDE.Analysis.variation_of_constants_coef_zero`: The formula of variation of constants in `ℂ³`
  from the time zero. Let `0 ≤ t` and let `c`, `B : ℝ → ℂ³` be continuous on `[0, t]` with
  `c' s = -l • c s - B s` for `s` in `(0, t)`. Then
  `c t = exp (-l t) • c 0 + ∫ s in 0..t, -exp (-l (t - s)) • B s`. A case of
  `PDE.Analysis.variation_of_constants_coef`.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis

/-- The formula of variation of constants in `ℂ³`. Let `a ≤ t` and let `c`, `B : ℝ → ℂ³` be
continuous on `[a, t]` with `c' s = -l • c s - B s` for `s` in `(a, t)`. Then
`c t = exp (-l (t - a)) • c a + ∫ s in a..t, -exp (-l (t - s)) • B s`. -/
theorem variation_of_constants_coef {c B : ℝ → Coef} {l a t : ℝ} (ht : a ≤ t)
    (hc : ContinuousOn c (Icc a t)) (hB : ContinuousOn B (Icc a t))
    (hd : ∀ s ∈ Ioo a t, HasDerivAt c ((-l) • c s - B s) s) :
    c t = Real.exp (-(l * (t - a))) • c a + ∫ s in a..t, (-Real.exp (-(l * (t - s)))) • B s := by
  have hg : ∀ s ∈ Ioo a t, HasDerivAt (fun s ↦ Real.exp (l * s) • c s)
      (-(Real.exp (l * s) • B s)) s := by
    intro s hs
    have he : HasDerivAt (fun s ↦ Real.exp (l * s)) (Real.exp (l * s) * l) s := by
      simpa using ((hasDerivAt_id s).const_mul l).exp
    refine (he.smul (hd s hs)).congr_deriv ?_
    rw [smul_sub, smul_smul, mul_neg, neg_smul]
    abel
  have hexp : Continuous (fun s : ℝ ↦ Real.exp (l * s)) := by fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun s ↦ Real.exp (l * s) • c s) (f' := fun s ↦ -(Real.exp (l * s) • B s)) ht
    (hexp.continuousOn.smul hc) hg
    ((hexp.continuousOn.smul hB).neg.intervalIntegrable_of_Icc ht)
  have e1 : (fun s ↦ (-Real.exp (-(l * (t - s)))) • B s) =
      fun s ↦ Real.exp (-(l * t)) • (-(Real.exp (l * s) • B s)) := by
    funext s
    rw [show -(l * (t - s)) = -(l * t) + l * s by ring, smul_neg, smul_smul, ← Real.exp_add,
      neg_smul]
  rw [e1, intervalIntegral.integral_smul, hint, smul_sub, smul_smul, smul_smul, ← Real.exp_add,
    ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul,
    show -(l * t) + l * a = -(l * (t - a)) by ring]
  abel

/-- The formula of variation of constants in `ℂ³` from the time zero. Let `0 ≤ t` and let `c`,
`B : ℝ → ℂ³` be continuous on `[0, t]` with `c' s = -l • c s - B s` for `s` in `(0, t)`. Then
`c t = exp (-l t) • c 0 + ∫ s in 0..t, -exp (-l (t - s)) • B s`. A case of
`PDE.Analysis.variation_of_constants_coef`. -/
theorem variation_of_constants_coef_zero {c B : ℝ → Coef} {l t : ℝ} (ht : 0 ≤ t)
    (hc : ContinuousOn c (Icc 0 t)) (hB : ContinuousOn B (Icc 0 t))
    (hd : ∀ s ∈ Ioo 0 t, HasDerivAt c ((-l) • c s - B s) s) :
    c t = Real.exp (-(l * t)) • c 0 + ∫ s in (0 : ℝ)..t, (-Real.exp (-(l * (t - s)))) • B s := by
  simpa using variation_of_constants_coef (a := 0) ht hc hB hd

end PDE.Analysis
