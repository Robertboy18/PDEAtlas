/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.PersistenceMaximal
public import PDE.Fluid.HalfPlaneSystem.BiotSavartLaw

/-!
# The Boussinesq system as an instance of the half-plane systems

The half-plane Biot-Savart law satisfies both classes of velocity laws, `IsVelocityLaw` and
`IsHolderVelocityLaw`, and a constant is a forcing coefficient: it is smooth, and its derivatives of
positive order vanish. With the Biot-Savart law and the coefficient `1` the system is the
two-dimensional Boussinesq system in vorticity form, `θ_t + u · ∇θ = 0`, `ω_t + u · ∇ω = ∂₀θ`. So
the hypotheses of the theorem on maximal solutions hold together, and the theorems of the folder are
not empty. The other instance, the velocity law of the wall of a cylinder with the coefficient
`r⁻⁴`, is proved in BlowupZoo.

The module also links `PDE/Fluid/Boussinesq/HalfPlane` to this folder. That folder proves the local
theory of the Boussinesq system for its own classes of solutions,
`Boussinesq.HalfPlane.IsSolutionOn` and `Boussinesq.HalfPlane.IsRegularSolutionOn`, which carry a
stream function and have no radius `R₀` that bounds the supports. The link gives the hypothesis
`IsSolutionOn` or `IsRegularSolutionOn` of a theorem of this folder for a solution of those classes;
the other hypotheses of that theorem stay to be proved.
`PDE/Examples/Fluid/HalfPlaneUniqueness.lean` derives in this way the statement of
`Boussinesq.HalfPlane.IsSolutionOn.eq_of_hasDataAt` from `IsSolutionOn.eq_of_hasDataAt`, whose only
hypotheses on the solutions are the class `IsSolutionOn` and the data.

The converse is not proved: a solution of the class of this folder for the Biot-Savart law and the
coefficient `1` has no stream function, and no theorem builds one with the regularity that
`Boussinesq.HalfPlane.IsSolutionOn` asks for. `PDE/Fluid/Boussinesq/HalfPlane` proves its main
theorems itself, with the same lemmas on data and flows: the modules of this folder import that
folder, so its theorems are not corollaries of the general ones in the library.

## Main results

* `isForcingCoefficient_const`: a constant `c` is a forcing coefficient with the bound `|c|` at
  order `0` and the bound `0` at every positive order.
* `exists_maximalSolutionOf_halfPlaneVelocity`: for data `ω₀ ∈ C^{k,α}`, `θ₀ ∈ C^{k+1,α}` with
  `k ≥ 2` and `0 < α < 1` that vanish outside a disc of radius `R < R₀`, the system with the
  Biot-Savart law and the coefficient `1` has a regular solution of order `k` with these data on an
  interval `[0, T)`, `T > 0`. It is `exists_maximalSolutionOf` (`PersistenceMaximal.lean`) at the
  instances `isVelocityLaw_halfPlaneVelocity`, `isHolderVelocityLaw_halfPlaneVelocity` and
  `isForcingCoefficient_const`, with the first three of its conclusions.
* `isSolutionOn_of_boussinesq`: a solution of the class `Boussinesq.HalfPlane.IsSolutionOn` whose
  vorticity and temperature vanish on the closed half-plane outside discs about the origin of radius
  less than `R₀`, one disc for all times of each compact interval of times (`HasBoundedSupportOn`),
  is, with its vorticity and its temperature, a solution of the class `IsSolutionOn` of this folder
  for the Biot-Savart law and the coefficient `1`.
* `isRegularSolutionOn_of_boussinesq`: the same for the regular classes: a solution of the class
  `Boussinesq.HalfPlane.IsRegularSolutionOn` with such supports is a solution of the class
  `IsRegularSolutionOn` of this folder.
* `exists_isSolutionOn_of_boussinesq`, `exists_isRegularSolutionOn_of_boussinesq`: on every compact
  interval `[a, b]` inside the times of the solution there is a radius `R₀` for which the solution
  is in the class of this folder on `[a, b]`.
-/

@[expose] public section

noncomputable section

open Set IncompressibleFlow Boussinesq.HalfPlane
open scoped ENNReal

namespace HalfPlaneSystem

set_option linter.missingDocs true

/-- **A constant is a forcing coefficient.** The constant function `c` on the plane is smooth, its
value has the bound `|c|` and its derivatives of positive order are zero. This gives the class
`IsForcingCoefficient` an instance; the Boussinesq system has `c = 1`. Proof: the iterated
derivative of a constant of positive order vanishes. -/
theorem isForcingCoefficient_const (c : ℝ) :
    IsForcingCoefficient (fun _ : ℝ^2 ↦ c) fun k ↦ if k = 0 then |c| else 0 where
  contDiff := contDiff_const
  norm_iteratedFDeriv_le k x := by
    rcases eq_or_ne k 0 with rfl | hk
    · simp [norm_iteratedFDeriv_zero]
    · simp [iteratedFDeriv_const_of_ne hk, hk]

/-- **Local existence for the Biot-Savart law and the coefficient `1`.** For data
`ω₀ ∈ C^{k,α}`, `θ₀ ∈ C^{k+1,α}` on the closed half-plane, `k ≥ 2`, `0 < α < 1`, that vanish
outside a disc of radius `R < R₀`, there are a time `T > 0` and a regular solution of order `k` of
the system with the half-plane Biot-Savart law and the coefficient `1` on `[0, T)` with these
data. These are the first three conclusions of `exists_maximalSolutionOf` for one law and one
coefficient; the statement shows that the hypotheses of that theorem hold together. Its other
conclusions (the two blow-up alternatives, maximality, uniqueness, the regularity of the slices)
are not restated here: apply `exists_maximalSolutionOf` to the same three instances. Proof: the
Biot-Savart law is a velocity law with the Schauder estimate, and the constant `1` is a forcing
coefficient. -/
theorem exists_maximalSolutionOf_halfPlaneVelocity {k : ℕ} {ω₀ θ₀ : ℝ^2 → ℝ} {R₀ R N α : ℝ}
    (hk : 2 ≤ k) (hα : 0 < α) (hα1 : α < 1) (hR : R < R₀)
    (hdata : IsHolderDataOf k ω₀ θ₀ α R N) :
    ∃ (T : ℝ≥0∞) (sol : Fields), 0 < T ∧
      IsRegularSolutionOfOn halfPlaneVelocity (fun _ ↦ 1) R₀ k sol (lifeSpan T) α ∧
      HasDataAt sol 0 ω₀ θ₀ := by
  obtain ⟨T, sol, hT, hsol, h0, -⟩ := exists_maximalSolutionOf
    (isVelocityLaw_halfPlaneVelocity R₀) (isHolderVelocityLaw_halfPlaneVelocity R₀)
    (isForcingCoefficient_const 1) hk hα hα1 hR hdata
  exact ⟨T, sol, hT, hsol, h0⟩

/-! ### Solutions of the Boussinesq class are solutions of the general class -/

/-- The vorticity and the temperature of fields of the Boussinesq system, without the stream
function. -/
def fieldsOfBoussinesq (sol : Boussinesq.VorticityStreamFields) : Fields :=
  ⟨sol.vorticity, sol.temperature⟩

/-- **A Boussinesq solution is a solution of the half-plane system with the Biot-Savart law and
the coefficient `1`.** Let `sol` be a solution of the class `Boussinesq.HalfPlane.IsSolutionOn` on
the times `I` whose vorticity and temperature vanish on the closed half-plane outside discs about
the origin of radius less than `R₀`, one disc for all times of each compact interval in `I`
(`HasBoundedSupportOn`). Then its vorticity and temperature form a solution of the class
`IsSolutionOn` of this folder on `I`. This is the hypothesis on the solution of the uniqueness
theorems of this folder (`IsSolutionOn.eq_of_hasDataAt`); a theorem with further hypotheses, such
as the class of regular solutions or a maximal time, needs those as well. Proof: the
regularity is the same in both classes, and on the closed half-plane the velocity of the stream
function is the Biot-Savart velocity of the vorticity
(`Boussinesq.HalfPlane.IsSolutionOn.velocity_eq`), so the two transport equations are those of the
general class with `κ = 1`. -/
theorem isSolutionOn_of_boussinesq {sol : Boussinesq.VorticityStreamFields} {I : Set ℝ} {R₀ : ℝ}
    (h : Boussinesq.HalfPlane.IsSolutionOn sol I)
    (hR₀ : HasBoundedSupportOn R₀ (fieldsOfBoussinesq sol) I) :
    IsSolutionOn halfPlaneVelocity (fun _ ↦ 1) R₀ (fieldsOfBoussinesq sol) I where
  vorticity_contDiffOn := h.classical.regularity.vorticity_contDiffOn
  temperature_contDiffOn := h.classical.regularity.temperature_contDiffOn
  vorticity_differentiableAt_time ht := h.classical.regularity.vorticity_differentiableAt_time ht
  temperature_differentiableAt_time ht :=
    h.classical.regularity.temperature_differentiableAt_time ht
  vorticity_equation {x t} hx ht := by
    have heq := h.classical.vorticity_equation (show x ∈ Boussinesq.upperHalfPlane from hx) ht
    -- at a point of the half-plane the velocity of the stream function is the Biot-Savart velocity
    simp only [PDE.advectiveDerivative, h.velocity_eq ht hx.le] at heq
    simpa only [PDE.advectiveDerivative, fieldsOfBoussinesq, one_mul] using heq
  temperature_equation {x t} hx ht := by
    have heq := h.classical.temperature_equation (show x ∈ Boussinesq.upperHalfPlane from hx) ht
    simp only [PDE.advectiveDerivative, h.velocity_eq ht hx.le] at heq
    simpa only [PDE.advectiveDerivative, fieldsOfBoussinesq] using heq
  support := hR₀

/-- **A regular Boussinesq solution is a regular solution of the general class.** Let `sol` be a
solution of the class `Boussinesq.HalfPlane.IsRegularSolutionOn` on the times `I` with the Hölder
exponent `α`, whose vorticity and temperature vanish on the closed half-plane outside discs about
the origin of radius less than `R₀`, one disc for all times of each compact interval in `I`
(`HasBoundedSupportOn`). Then its vorticity and temperature form a solution of the class
`IsRegularSolutionOn` of this folder on `I` with the same exponent, for the Biot-Savart law and
the coefficient `1`. Proof: `isSolutionOn_of_boussinesq`, and the Hölder bounds of the slices are
the same condition in both classes. -/
theorem isRegularSolutionOn_of_boussinesq {sol : Boussinesq.VorticityStreamFields} {I : Set ℝ}
    {R₀ α : ℝ} (h : Boussinesq.HalfPlane.IsRegularSolutionOn sol I α)
    (hR₀ : HasBoundedSupportOn R₀ (fieldsOfBoussinesq sol) I) :
    IsRegularSolutionOn halfPlaneVelocity (fun _ ↦ 1) R₀ (fieldsOfBoussinesq sol) I α :=
  ⟨isSolutionOn_of_boussinesq h.toIsSolutionOn hR₀, h.holderData⟩

/-- **On a compact interval of times every Boussinesq solution is a solution of the general
class.** For a solution `sol` of the class `Boussinesq.HalfPlane.IsSolutionOn` on `I` and
`[a, b] ⊆ I` there is a radius `R₀` for which the vorticity and the temperature of `sol` form a
solution of the class `IsSolutionOn` on `[a, b]`, for the Biot-Savart law and the coefficient `1`.
It is `isSolutionOn_of_boussinesq` with the radius that the Boussinesq class provides on
`[a, b]`, plus one. -/
theorem exists_isSolutionOn_of_boussinesq {sol : Boussinesq.VorticityStreamFields} {I : Set ℝ}
    (h : Boussinesq.HalfPlane.IsSolutionOn sol I) {a b : ℝ} (hab : Icc a b ⊆ I) :
    ∃ R₀ : ℝ,
      IsSolutionOn halfPlaneVelocity (fun _ ↦ 1) R₀ (fieldsOfBoussinesq sol) (Icc a b) := by
  obtain ⟨R, hR⟩ := h.support a b hab
  exact ⟨R + 1, isSolutionOn_of_boussinesq (h.mono hab) fun a' b' hab' ↦
    ⟨R, lt_add_one R, fun t ht ↦ hR t (hab' ht)⟩⟩

/-- **On a compact interval of times every regular Boussinesq solution is a regular solution of
the general class.** For a solution `sol` of the class `Boussinesq.HalfPlane.IsRegularSolutionOn`
on `I` with the exponent `α` and `[a, b] ⊆ I` there is a radius `R₀` for which the vorticity and
the temperature of `sol` form a solution of the class `IsRegularSolutionOn` on `[a, b]` with the
same exponent, for the Biot-Savart law and the coefficient `1`. It is
`exists_isSolutionOn_of_boussinesq` with the Hölder bounds of the slices, which are the same
condition in both classes. -/
theorem exists_isRegularSolutionOn_of_boussinesq {sol : Boussinesq.VorticityStreamFields}
    {I : Set ℝ} {α : ℝ} (h : Boussinesq.HalfPlane.IsRegularSolutionOn sol I α) {a b : ℝ}
    (hab : Icc a b ⊆ I) :
    ∃ R₀ : ℝ, IsRegularSolutionOn halfPlaneVelocity (fun _ ↦ 1) R₀ (fieldsOfBoussinesq sol)
      (Icc a b) α := by
  obtain ⟨R₀, hR₀⟩ := exists_isSolutionOn_of_boussinesq h.toIsSolutionOn hab
  exact ⟨R₀, hR₀, fun a' b' hab' ↦ h.holderData a' b' (hab'.trans hab)⟩

end HalfPlaneSystem
