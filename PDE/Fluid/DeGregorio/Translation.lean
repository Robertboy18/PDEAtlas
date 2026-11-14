/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Model
public import PDE.Analysis.Fourier.HilbertTransform.PrincipalValue
import PDE.Analysis.Fourier.HilbertTransform.RealPair.Translation
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Translated classical De Gregorio solutions

The Hilbert transform commutes with translations. So the generalized De Gregorio equation
`ω_t + a u ω_x = u_x ω`, `u_x = Hω` is invariant under translations in space, for every `a`:
the transformation `(ω, u) (x, t) ↦ (ω, u) (x - x₀, t)` preserves both the transport equation
and the concrete spectral Biot–Savart relation. The pointwise form of `u_x = Hω`, the principal
value at a point, translates with the fields. These statements hold for arbitrary fields.

## Main results

* `DeGregorio.Fields.translate`: the fields `ω (x - x₀, t)`, `u (x - x₀, t)`.
* `DeGregorio.IsClassicalSolutionOn.translate`: for every `a`, every classical solution on a set
  of times and every real `x₀`, the translated fields are a classical solution on the same
  times.
* `DeGregorio.Fields.hasHilbertPV_translate`: for all fields and all real `x₀`, `x`, `t`, if
  `u_x (x - x₀, t)` is the Hilbert principal value of `ω (·, t)` at `x - x₀`, then the velocity
  gradient of the translated fields at `x` is the principal value of their vorticity at `x`.

## References

* P. M. Lushnikov, D. A. Silantyev, and M. Siegel, "Collapse versus blow-up and global existence
  in the generalized Constantin–Lax–Majda equation", *J. Nonlinear Sci.* 31 (2021), no. 5,
  article 82; numbering of arXiv:2010.01201v2, (1), (2) and the shift of the origin by an
  arbitrary real constant `x₀` in (32) and (33), pp. 2 and 10.
  <https://doi.org/10.1007/s00332-021-09737-x> <https://arxiv.org/abs/2010.01201v2>
-/

@[expose] public section

noncomputable section

open PDE.Analysis

namespace DeGregorio

/-- The fields translated in space by `x₀`: the vorticity `ω (x - x₀, t)` and the velocity
`u (x - x₀, t)`. -/
def Fields.translate (fields : Fields) (x₀ : ℝ) : Fields :=
  ⟨fun x t ↦ fields.vorticity (x - x₀) t, fun x t ↦ fields.velocity (x - x₀) t⟩

/-- **The generalized De Gregorio equation is invariant under translations in space.** For every
`a`, every classical solution on a set of times and every real `x₀`, the translated fields
`ω (x - x₀, t)`, `u (x - x₀, t)` are a classical solution on the same times. -/
theorem IsClassicalSolutionOn.translate {a : ℝ} {fields : Fields} {times : Set ℝ}
    (h : IsClassicalSolutionOn a fields times) (x₀ : ℝ) :
    IsClassicalSolutionOn a (fields.translate x₀) times where
  regularity := {
    vorticity_differentiableAt := fun {x t} ht ↦
      (h.regularity.vorticity_differentiableAt (x := x - x₀) ht).comp (x, t)
        (f := fun q : ℝ × ℝ ↦ (q.1 - x₀, q.2)) (by fun_prop)
    velocity_differentiableAt := fun {x t} ht ↦
      (h.regularity.velocity_differentiableAt (x := x - x₀) ht).comp x
        (f := fun y : ℝ ↦ y - x₀) (by fun_prop) }
  transport := fun x t ht ↦ by
    have hω : deriv (fun y ↦ fields.vorticity (y - x₀) t) x =
        deriv (fun y ↦ fields.vorticity y t) (x - x₀) :=
      deriv_comp_sub_const (fun y ↦ fields.vorticity y t) x₀ x
    have hu : deriv (fun y ↦ fields.velocity (y - x₀) t) x =
        deriv (fun y ↦ fields.velocity y t) (x - x₀) :=
      deriv_comp_sub_const (fun y ↦ fields.velocity y t) x₀ x
    change deriv (fields.vorticity (x - x₀)) t +
        a * fields.velocity (x - x₀) t * deriv (fun y ↦ fields.vorticity (y - x₀) t) x =
      deriv (fun y ↦ fields.velocity (y - x₀) t) x * fields.vorticity (x - x₀) t
    rw [hω, hu]
    exact h.transport ht
  biotSavart := fun t ht ↦ by
    have hu : deriv (fun x ↦ fields.velocity (x - x₀) t) =
        fun x ↦ deriv (fun y ↦ fields.velocity y t) (x - x₀) :=
      funext fun x ↦ deriv_comp_sub_const (fun y ↦ fields.velocity y t) x₀ x
    change IsHilbertPair (fun x ↦ fields.vorticity (x - x₀) t)
      (deriv fun x ↦ fields.velocity (x - x₀) t)
    rw [hu]
    exact (h.biotSavart ht).translate x₀

/-- **Translation of the pointwise Hilbert relation.** If at the time `t` the velocity gradient
`u_x (x - x₀, t)` of the fields is the Hilbert principal value of their vorticity `ω (·, t)` at
`x - x₀`, then the velocity gradient of the fields translated by `x₀` at `x` is the principal
value of the translated vorticity at `x`. -/
theorem Fields.hasHilbertPV_translate {fields : Fields} {x₀ x t : ℝ}
    (h : HasHilbertPV (fun y ↦ fields.vorticity y t) (x - x₀)
      (deriv (fun y ↦ fields.velocity y t) (x - x₀))) :
    HasHilbertPV (fun y ↦ (fields.translate x₀).vorticity y t) x
      (deriv (fun y ↦ (fields.translate x₀).velocity y t) x) := by
  have hu : deriv (fun y ↦ fields.velocity (y - x₀) t) x =
      deriv (fun y ↦ fields.velocity y t) (x - x₀) :=
    deriv_comp_sub_const (fun y ↦ fields.velocity y t) x₀ x
  change HasHilbertPV (fun y ↦ fields.vorticity (y - x₀) t) x
    (deriv (fun y ↦ fields.velocity (y - x₀) t) x)
  rw [hu]
  simp only [sub_eq_add_neg] at h ⊢
  exact h.translate

end DeGregorio
