/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Energy.Difference.Bounds
public import PDE.Fluid.DeGregorio.Energy.Difference.Rate

/-!
# The difference estimate for frozen transport iterates

In a transport iteration the output difference and the vorticity difference
generating the velocities are distinct. Integration by parts controls the
output energy by itself and by the input L² difference. Hilbert isometry and
normalization at zero supply both velocity-difference bounds.

The equations and Hilbert pairs are hypotheses on the two transport iterates.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology

namespace DeGregorio

/-- Subtracting the two frozen transport equations and differentiating the
output energy yields an estimate involving the input difference. -/
theorem norm_deriv_frozen_differenceEnergy_le
    {fields other : Fields} {times : Set ℝ} {f g : ℝ → ℝ} {L C t : ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry fields.vorticity))
    (hg : ContDiff ℝ 1 (Function.uncurry other.vorticity))
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hv : ContDiff ℝ 1 (Function.uncurry other.velocity))
    (hpde : SatisfiesTransportEquationOn 1 fields times)
    (hother : SatisfiesTransportEquationOn 1 other times) (ht : t ∈ times)
    (hpair : IsHilbertPair f (deriv (fun x ↦ fields.velocity x t)))
    (hpairOther : IsHilbertPair g (deriv (fun x ↦ other.velocity x t)))
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hleft : fields.vorticity (-L) t = other.vorticity (-L) t)
    (hright : fields.vorticity L t = other.vorticity L t)
    (hzero : fields.velocity 0 t = other.velocity 0 t)
    (hbound : ∀ x ∈ Icc (-L) L,
      |deriv (fun y ↦ fields.velocity y t) x| ≤ C ∧
        |other.vorticity x t| ≤ C ∧
          |deriv (fun y ↦ other.vorticity y t) x| ≤ C) :
    ‖deriv (differenceEnergy fields other L) t‖ ≤
      C * (5 * differenceEnergy fields other L t +
        (1 + 2 * L ^ 2) * ∫ x, (f x - g x) ^ 2) := by
  let d := fun x ↦ fields.vorticity x t - other.vorticity x t
  let u := fun x ↦ fields.velocity x t
  let v := fun x ↦ fields.velocity x t - other.velocity x t
  let w := fun x ↦ other.vorticity x t
  have hfs := hf.comp (contDiff_id.prodMk (contDiff_const (c := t)))
  have hgs := hg.comp (contDiff_id.prodMk (contDiff_const (c := t)))
  have hus := hu.comp (contDiff_id.prodMk (contDiff_const (c := t)))
  have hvs := hv.comp (contDiff_id.prodMk (contDiff_const (c := t)))
  have hd : ContDiff ℝ 1 d := hfs.sub hgs
  have hpairDiff : IsHilbertPair (f - g) (deriv v) :=
    isHilbertPair_sub_of_differentiable (hus.differentiable (by simp))
      (hvs.differentiable (by simp)) hpair hpairOther
  have hrate : deriv (differenceEnergy fields other L) t =
      ∫ x in Icc (-L) L, 3 * deriv u x * d x ^ 2 + 2 * d x * deriv v x * w x -
        2 * d x * v x * deriv w x := by
    simpa only [zero_mul, mul_zero, zero_add, add_zero] using
      deriv_differenceEnergy_eq (cl := 0) (cw := 0) hfs hgs hus hvs
      (fun x ↦ (hf.comp (contDiff_const (c := x) |>.prodMk contDiff_id)).differentiable (by simp) t)
        (fun x ↦ (hg.comp (contDiff_const (c := x) |>.prodMk contDiff_id)).differentiable (by simp)
        t)
      (hasDerivAt_differenceEnergy hf hg L t)
      (fun x ↦ by simpa only [one_mul, zero_mul, zero_add] using hpde (x := x) ht)
      (fun x ↦ by simpa only [one_mul, zero_mul, zero_add] using hother (x := x) ht)
      hleft hright
  rw [hrate]
  exact norm_integral_frozen_terms_le hd hus (hus.sub hvs) hgs hL hC hpairDiff
    (sub_eq_zero.mpr hzero) hbound

end DeGregorio
