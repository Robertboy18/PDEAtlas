/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Order duality between viscosity subsolutions and supersolutions

Negation exchanges the two kinds of contact: `φ` touches `u` from below at `z` exactly when `-φ`
touches `-u` from above there, and the time derivative and the spatial gradient of `-φ` are the
negatives of those of `φ`. So `u` is a supersolution of `u_t + H(Dₓu, x) = 0` exactly when `-u`
is a subsolution of the equation with the reflected Hamiltonian `(p, x) ↦ -H(-p, x)`.

## Main results

* `isSpatialViscositySupersolution_iff_neg`: the equivalence above, for every Hamiltonian, every
  set and every function.
* `gradient_spaceSlice_neg`: the spatial gradient of a time slice of `-φ`.

A theorem about subsolutions that holds for a class of Hamiltonians closed under the reflection,
for example the jointly continuous ones, gives the same theorem for supersolutions. The limit
theorems of `Stability` and `VanishingViscosity.Limit` and the pointwise inequality of
`Consistency` are obtained this way.
-/

open scoped Gradient

@[expose] public section

namespace HamiltonJacobi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Negating a function on space × time negates the spatial gradient of each time slice. No
differentiability is assumed: both sides vanish where the slice is not differentiable. -/
theorem gradient_spaceSlice_neg (φ : E × ℝ → ℝ) (z : E × ℝ) :
    ∇ (fun x ↦ (-φ) (x, z.2)) z.1 = -∇ (fun x ↦ φ (x, z.2)) z.1 := by
  simp only [gradient, Pi.neg_apply, fderiv_fun_neg, map_neg]

/-- **Order duality.** A function `u` is a supersolution of `u_t + H(Dₓu, x) = 0` on `U` exactly
when `-u` is a subsolution on `U` of the equation with the reflected Hamiltonian
`(p, x) ↦ -H(-p, x)`: the lower tests of `u` are the negatives of the upper tests of `-u`. -/
theorem isSpatialViscositySupersolution_iff_neg {H : E → E → ℝ} {U : Set (E × ℝ)}
    {u : E × ℝ → ℝ} :
    IsSpatialViscositySupersolution H U u ↔
      IsSpatialViscositySubsolution (fun p x ↦ -H (-p) x) U (-u) := by
  simp only [IsSpatialViscositySupersolution, IsSpatialViscositySubsolution]
  refine and_congr_right fun _ ↦ forall₂_congr fun z _ ↦ ⟨fun h φ hφ hc ↦ ?_, fun h φ hφ hc ↦ ?_⟩
  · have h' := h (-φ) hφ.neg
      (by simpa only [Pi.neg_apply, neg_sub', neg_neg, sub_neg_eq_add] using hc.neg)
    rw [fderiv_neg, neg_apply, gradient_spaceSlice_neg] at h'
    linarith only [h']
  · have h' := h (-φ) hφ.neg
      (by simpa only [Pi.neg_apply, neg_sub', neg_neg, sub_neg_eq_add] using hc.neg)
    rw [fderiv_neg, neg_apply, gradient_spaceSlice_neg, neg_neg] at h'
    linarith only [h']

end HamiltonJacobi
