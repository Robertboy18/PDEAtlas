/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.MulAction
import Mathlib.Tactic.Positivity.Finset

/-!
# A Lipschitz cutoff on an energy band

The cutoff equals one on a closed inner band and zero outside an open outer band.
Its definition uses only real energies, so it remains meaningful when either of
the corresponding state-space level sets is empty. Lipschitz continuity of the
cutoff suffices for the deformation ODE. Composed with the energy, the cutoff replaces the
function `g(u) = dist(u, A) / (dist(u, A) + dist(u, B))` in step 2 of the proof of Evans,
§8.5.1, Theorem 1: `energyBandCutoff_nonneg`, `energyBandCutoff_le_one`,
`energyBandCutoff_eq_zero` and `energyBandCutoff_eq_one` are his properties (8),
`0 ≤ g ≤ 1`, `g = 0` on `A = {|I - c| ≥ ε}` and `g = 1` on `B = {|I - c| ≤ δ}`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.1(a), step 2 of the proof of Theorem 1
  (Deformation Theorem), (8), pp. 503-504. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Variational

/-- The piecewise linear cutoff between the energy bands of widths `δ` and `ε`
around the level `c`. Its useful plateau properties require `δ < ε`. -/
def energyBandCutoff (c δ ε s : ℝ) : ℝ :=
  max 0 (min 1 ((ε - |s - c|) / (ε - δ)))

/-- The energy-band cutoff is nonnegative, including at the transition points. -/
theorem energyBandCutoff_nonneg (c δ ε s : ℝ) : 0 ≤ energyBandCutoff c δ ε s :=
  le_max_left _ _

/-- The energy-band cutoff never exceeds one. -/
theorem energyBandCutoff_le_one (c δ ε s : ℝ) : energyBandCutoff c δ ε s ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The entire closed inner band is a plateau. -/
theorem energyBandCutoff_eq_one {c δ ε s : ℝ} (hδε : δ < ε) (hs : |s - c| ≤ δ) :
    energyBandCutoff c δ ε s = 1 := by
  have h : 1 ≤ (ε - |s - c|) / (ε - δ) :=
    (le_div_iff₀ (sub_pos.mpr hδε)).mpr (by linarith)
  simp only [energyBandCutoff, min_eq_left h, max_eq_right zero_le_one]

/-- The cutoff vanishes outside the open outer band, including its boundary. -/
theorem energyBandCutoff_eq_zero {c δ ε s : ℝ} (hδε : δ < ε) (hs : ε ≤ |s - c|) :
    energyBandCutoff c δ ε s = 0 := by
  have h : (ε - |s - c|) / (ε - δ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sub_pos.mpr hδε).le
  exact max_eq_left ((min_le_right _ _).trans h)

/-- The cutoff is globally Lipschitz; the norm formulation also covers degenerate
choices of the two band widths, with no nonzero-denominator hypothesis. -/
theorem lipschitzWith_energyBandCutoff (c δ ε : ℝ) :
    LipschitzWith ‖(ε - δ)⁻¹‖₊ (energyBandCutoff c δ ε) := by
  unfold energyBandCutoff
  have h : LipschitzWith 1 (fun s : ℝ ↦ ε - dist s c) := by
    simpa only [zero_add] using (LipschitzWith.const ε).sub (LipschitzWith.dist_left c)
  have hdiv := (lipschitzWith_smul (β := ℝ) (ε - δ)⁻¹).comp h
  simpa only [Function.comp_def, Real.dist_eq, smul_eq_mul,
    mul_comm, ← div_eq_mul_inv, mul_one] using (hdiv.const_min 1).const_max 0

end PDE.Analysis.Variational
