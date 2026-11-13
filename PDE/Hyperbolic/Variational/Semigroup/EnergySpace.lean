/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.CoerciveHilbertSpace
public import PDE.Hyperbolic.Variational.WaveEnergy

/-!
# The wave energy Hilbert space

The displacement and velocity space carries the inner product
`B(u,φ) + ⟪v,ψ⟫`. Its norm is the square root of the full wave energy.
Coercivity makes this a complete space with the same vectors and topology as
the ordinary product of the energy and pivot spaces.
-/

@[expose] public section

noncomputable section

namespace Hyperbolic.Variational

open PDE.Analysis.Variational
open scoped InnerProductSpace

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A coercive spatial form gives a coercive form on displacement and velocity. -/
theorem isCoercive_waveEnergyForm (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) :
    IsCoercive (waveEnergyForm (H := H) B) := by
  obtain ⟨c, hc, hbound⟩ := hB
  refine ⟨min c 1, lt_min hc zero_lt_one, fun x ↦ ?_⟩
  have h := min_mul_norm_sq_le_autonomousWaveEnergy B hc
    (fun v ↦ by simpa only [pow_two, mul_assoc] using hbound v) x
  simpa only [waveEnergyForm_apply, real_inner_self_eq_norm_sq,
    autonomousWaveEnergy, pow_two, mul_assoc] using h

/-- Symmetry of the spatial form gives symmetry of the wave energy pairing. -/
theorem symmetric_waveEnergyForm (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ u v, B u v = B v u) (x y : V × H) :
    waveEnergyForm B x y = waveEnergyForm B y x := by
  simp only [waveEnergyForm_apply, hsymm x.1 y.1, real_inner_comm x.2 y.2]

/-- Displacements and velocities with their wave energy norm. -/
abbrev WaveEnergySpace (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) :=
  WithCoerciveForm (waveEnergyForm (H := H) B) (isCoercive_waveEnergyForm B hB)
    (symmetric_waveEnergyForm B hsymm)

namespace WaveEnergySpace

variable (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
  (hsymm : ∀ u v, B u v = B v u)

/-- The displacement and velocity coordinates preserve the underlying topology. -/
def coordinates : WaveEnergySpace (H := H) B hB hsymm ≃L[ℝ] V × H :=
  WithCoerciveForm.continuousLinearEquiv _ _ _

/-- The energy inner product pairs displacement through the full spatial form. -/
theorem inner_eq (x y : WaveEnergySpace (H := H) B hB hsymm) :
    ⟪x, y⟫_ℝ = B (coordinates B hB hsymm x).1 (coordinates B hB hsymm y).1 +
      ⟪(coordinates B hB hsymm x).2, (coordinates B hB hsymm y).2⟫_ℝ := rfl

/-- The norm is exactly the full wave energy, including any potential in the form. -/
theorem norm_sq_eq (x : WaveEnergySpace (H := H) B hB hsymm) :
    ‖x‖ ^ 2 = B (coordinates B hB hsymm x).1 (coordinates B hB hsymm x).1 +
      ‖(coordinates B hB hsymm x).2‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq, real_inner_self_eq_norm_sq]

end WaveEnergySpace

end Hyperbolic.Variational
