/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.Profiles
public import PDE.Hyperbolic.ConservationLaw.PlanarShock
public import PDE.Hyperbolic.ConservationLaw.Scalar.Weak
import PDE.Hyperbolic.ConservationLaw.Scalar.PlanarShock

/-!
# Burgers shock profiles as weak solutions

The Burgers Riemann shock is the scalar planar shock with speed
`(uL + uR) / 2`. The general planar-shock calculation supplies local
integrability and the distributional conservation law; the only
Burgers-specific input is its Rankine–Hugoniot identity.

The profile is the shock (54) of Evans, §3.4.4, Theorem 4(i); for the Burgers flux `u²/2` the
speed (55) is `(uL + uR) / 2`. Step 1 of Evans's proof notes that (54) is an integral solution
because the Rankine–Hugoniot condition holds. `shockProfile_isWeakSolution` is the distributional
form of that remark on all of spacetime, for any two states.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.4, Theorem 4(i), equations (54)-(55), and step 1 of
  its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace BurgersEquation.Riemann

noncomputable section

open PDE.Hyperbolic.ConservationLaw.Scalar
open MeasureTheory
open PDE.Common
open PDE.Hyperbolic.ConservationLaw
open TopologicalSpace

/-- The explicit Burgers shock profile is the corresponding scalar planar shock. -/
theorem shockProfile_eq_planarShock (uL uR : ℝ) :
    shockProfile uL uR = planarShock uL uR (shockSpeed uL uR) := by
  funext p
  by_cases hp : p ∈ AffineInterface.leftHalfSpace (shockSpeed uL uR)
  · rw [planarShock_apply_of_mem hp]
    have hleft : p 1 < shockSpeed uL uR * p 0 := hp
    simp [shockProfile, hleft]
  · rw [planarShock_apply_of_not_mem hp]
    have hright : ¬p 1 < shockSpeed uL uR * p 0 := hp
    simp [shockProfile, hright]

/-- Every scalar composition with a Burgers shock profile is locally integrable.

The outer function may be arbitrary, since the composition takes only the two values `g uL` and
`g uR`. -/
theorem shockComposition_locallyIntegrable (g : ℝ → ℝ) (uL uR : ℝ) :
    LocallyIntegrable (fun p : ℝ^2 ↦ g (shockProfile uL uR p)) volume := by
  rw [shockProfile_eq_planarShock]
  exact locallyIntegrable_comp_planarShock g uL uR (shockSpeed uL uR)

/-- Every Burgers shock profile satisfies the global weak conservation law. -/
theorem shockProfile_isWeakSolution (uL uR : ℝ) :
    IsWeakSolution flux (⊤ : Opens ℝ^2) (shockProfile uL uR) := by
  rw [shockProfile_eq_planarShock]
  exact (rankineHugoniot_shockSpeed uL uR).isWeakSolution_planarShock

end

end BurgersEquation.Riemann
