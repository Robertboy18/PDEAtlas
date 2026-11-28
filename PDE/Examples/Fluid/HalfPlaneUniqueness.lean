/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.BoussinesqInstance

/-!
# Uniqueness for the Boussinesq system from the general half-plane theory

`PDE/Fluid/Boussinesq/HalfPlane` proves uniqueness of classical solutions of the Boussinesq system
on the half-plane, and `PDE/Fluid/HalfPlaneSystem` proves it for the system with any velocity law
and forcing coefficient. The example below states
`Boussinesq.HalfPlane.IsSolutionOn.eq_of_hasDataAt` word for word and proves it from
`HalfPlaneSystem.IsSolutionOn.eq_of_hasDataAt`. On the compact interval `[0, t]` the supports of two
Boussinesq solutions lie in one disc, so both are solutions of the general class for the Biot-Savart
law and the coefficient `1` (`HalfPlaneSystem.isSolutionOn_of_boussinesq`), and the general theorem
applies to them.

The proof of the general theorem names no theorem on solutions of the Boussinesq class, so the
derivation is not circular. The library keeps the direct proof of the special theorem
(`PDE/Fluid/Boussinesq/HalfPlane/Uniqueness.lean`), because the modules of the general theory import
that folder. The other theorems of the Boussinesq folder (existence, the a priori estimate,
persistence, continuation) are not derived from the general ones here.
-/

set_option linter.privateModule false

open Set IncompressibleFlow HalfPlaneSystem

namespace PDE.Examples.HalfPlaneUniqueness

/-- The uniqueness theorem of the Boussinesq folder, from the general uniqueness theorem: two
solutions of the class `Boussinesq.HalfPlane.IsSolutionOn` on an order-connected set of times
`I ∋ 0` with the same vorticity and temperature at time `0` on the closed half-plane agree there
at every time `t ∈ I` with `0 ≤ t`. -/
example {sol sol' : Boussinesq.VorticityStreamFields} {I : Set ℝ}
    (h : Boussinesq.HalfPlane.IsSolutionOn sol I) (h' : Boussinesq.HalfPlane.IsSolutionOn sol' I)
    (hI : I.OrdConnected) (h0 : (0 : ℝ) ∈ I)
    (hdata : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x 0 = sol'.vorticity x 0 ∧ sol.temperature x 0 = sol'.temperature x 0)
    {t : ℝ} (ht : t ∈ I) (ht0 : 0 ≤ t) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t := by
  have hsub : Icc 0 t ⊆ I := hI.out h0 ht
  -- a disc that holds the supports of both solutions on `[0, t]`
  obtain ⟨R, hR⟩ := h.support 0 t hsub
  obtain ⟨R', hR'⟩ := h'.support 0 t hsub
  -- both are solutions of the general class on `[0, t]`
  have hs := isSolutionOn_of_boussinesq (R₀ := max R R' + 1) (h.mono hsub) fun a b hab ↦
    ⟨R, (le_max_left R R').trans_lt (lt_add_one _), fun s hs ↦ hR s (hab hs)⟩
  have hs' := isSolutionOn_of_boussinesq (R₀ := max R R' + 1) (h'.mono hsub) fun a b hab ↦
    ⟨R', (le_max_right R R').trans_lt (lt_add_one _), fun s hs ↦ hR' s (hab hs)⟩
  -- the general uniqueness theorem, for the Biot-Savart law and the coefficient `1`
  exact hs.eq_of_hasDataAt (isVelocityLaw_halfPlaneVelocity _) (isForcingCoefficient_const 1) hs'
    ordConnected_Icc ⟨le_rfl, ht0⟩ hdata ⟨ht0, le_rfl⟩ ht0 hx

end PDE.Examples.HalfPlaneUniqueness
