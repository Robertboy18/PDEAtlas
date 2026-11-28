/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Solution
public import PDE.Fluid.Boussinesq.HalfPlane.Canonical
import PDE.FDeriv.Calculus

/-!
# Regular solutions of a half-plane system and their canonical representatives

The equations of a half-plane system hold in the open half-plane, but the fields are functions on
the whole plane, so two solutions with the same values on the closed half-plane may differ below the
boundary. Uniqueness holds on the closed half-plane only. This module replaces each solution by a
canonical representative, so that local solutions on overlapping time intervals can be glued to one
solution.

A regular solution `IsRegularSolutionOn U κ R₀ sol I α` is a solution whose time slices are data of
the class `IsHolderData` (`ω ∈ C^{1,α}`, `θ ∈ C^{2,α}` within the closed half-plane) with support
radius and bounds uniform on compact subintervals of the times. The canonical representative
`canonical sol` replaces the fields below the boundary by the weighted reflections of order one of
their values on the closed half-plane. It is again a solution, regular if `sol` is, and two
solutions that agree on the closed half-plane at a time have the same canonical representative at
that time, so canonical representatives of different solutions can be glued in time. The weighted
reflection of order one keeps joint `C¹` regularity, which is the regularity of the class of
solutions, and the velocity law sees only the values on the closed half-plane
(`IsVelocityLaw.congr`).

The set of times must have unique derivatives (`UniqueDiffOn`), which holds for intervals with more
than one point. Below the boundary the canonical representative solves no equation: only its values
on the closed half-plane have a meaning.

## Main results

* `IsRegularSolutionOn`: the regular solutions.
* `canonical sol`: the canonical representative; `canonical_vorticity_of_nonneg`,
  `canonical_temperature_of_nonneg`: it has the values of `sol` on the closed half-plane.
* `IsSolutionOn.canonical`, `IsRegularSolutionOn.canonical`: the two classes are preserved.
* `canonical_eq_of_eqOn`: the representative at a time depends only on the values of the fields on
  the closed half-plane at that time.

`Maximal.lean` glues canonical representatives of local solutions to the maximal solution, and
`APrioriEstimate.lean`, `Continuation.lean`, `Persistence.lean` and `PersistenceMaximal.lean` state
their results for `IsRegularSolutionOn`. The library has the same construction for the Boussinesq
system (`Boussinesq.HalfPlane.IsRegularSolutionOn`).
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology
open IncompressibleFlow SobolevSpace.GraphSpace.HigherOrderReflection Boussinesq.HalfPlane

open PDE (partialDeriv_congr_nhds)

namespace HalfPlaneSystem

set_option linter.missingDocs true

/-- A solution whose time slices are data of the class `IsHolderData` with support radius and
bounds uniform on every compact subinterval of the times. -/
structure IsRegularSolutionOn (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (κ : ℝ^2 → ℝ) (R₀ : ℝ) (sol : Fields)
    (I : Set ℝ) (α : ℝ) : Prop extends IsSolutionOn U κ R₀ sol I where
  /-- Uniform `C^{1,α} × C^{2,α}` bounds of the slices on compact subintervals. -/
  holderData : ∀ a b : ℝ, Icc a b ⊆ I → ∃ R N : ℝ, ∀ t ∈ Icc a b,
    IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N

/-- The canonical representative of the fields: below the boundary, the vorticity and the
temperature are the weighted reflections of order one of their values on the closed
half-plane. -/
def canonical (sol : Fields) : Fields where
  vorticity x t := weightedReflectionFun 1 1 (fun y ↦ sol.vorticity y t) x
  temperature x t := weightedReflectionFun 1 1 (fun y ↦ sol.temperature y t) x

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ}
  {sol sol' : Fields} {I : Set ℝ}

/-- On the closed half-plane the vorticity of the canonical representative is that of `sol`. -/
@[simp]
theorem canonical_vorticity_of_nonneg {x : ℝ^2} (hx : 0 ≤ x 1) (t : ℝ) :
    (canonical sol).vorticity x t = sol.vorticity x t :=
  weightedReflectionFun_eq_of_nonneg 1 1 (fun y ↦ sol.vorticity y t) x hx

/-- On the closed half-plane the temperature of the canonical representative is that of `sol`. -/
@[simp]
theorem canonical_temperature_of_nonneg {x : ℝ^2} (hx : 0 ≤ x 1) (t : ℝ) :
    (canonical sol).temperature x t = sol.temperature x t :=
  weightedReflectionFun_eq_of_nonneg 1 1 (fun y ↦ sol.temperature y t) x hx

/-- **Solutions are preserved by the canonical representative.** If `sol` solves the half-plane
system on a set of times with unique derivatives, so does `canonical sol`. This lets solutions
be glued through their canonical representatives. Proof: the weighted reflection of order one
keeps the joint `C¹` regularity; in the open half-plane the representative agrees with `sol`
near every point, and the velocity law sees only the values on the closed half-plane, so the
two equations are those of `sol`. -/
theorem IsSolutionOn.canonical (hU : IsVelocityLaw U R₀ C) (h : IsSolutionOn U κ R₀ sol I)
    (hI : UniqueDiffOn ℝ I) : IsSolutionOn U κ R₀ (canonical sol) I := by
  have hvel (t : ℝ) {x : ℝ^2} (hx : 0 < x 1) :
      U (fun y ↦ (HalfPlaneSystem.canonical sol).vorticity y t) x =
        U (fun y ↦ sol.vorticity y t) x :=
    hU.congr (fun y hy ↦ canonical_vorticity_of_nonneg hy t) x hx.le
  have hω (t : ℝ) {x : ℝ^2} (hx : 0 < x 1) :=
    eventuallyEq_canonical (f := fun y ↦ sol.vorticity y t) 1 (x := x) hx
  have hθ (t : ℝ) {x : ℝ^2} (hx : 0 < x 1) :=
    eventuallyEq_canonical (f := fun y ↦ sol.temperature y t) 1 (x := x) hx
  refine
    { vorticity_contDiffOn := PDE.Analysis.contDiffOn_weightedReflectionFun_slice
        (F := fun p : ℝ^2 × ℝ ↦ sol.vorticity p.1 p.2) 1 le_rfl hI h.vorticity_contDiffOn
      temperature_contDiffOn := PDE.Analysis.contDiffOn_weightedReflectionFun_slice
        (F := fun p : ℝ^2 × ℝ ↦ sol.temperature p.1 p.2) 1 le_rfl hI h.temperature_contDiffOn
      vorticity_differentiableAt_time := fun ht ↦
        PDE.Analysis.differentiableAt_weightedReflectionFun_slice
          (F := fun p : ℝ^2 × ℝ ↦ sol.vorticity p.1 p.2) 1 1
          fun _ ↦ h.vorticity_differentiableAt_time ht
      temperature_differentiableAt_time := fun ht ↦
        PDE.Analysis.differentiableAt_weightedReflectionFun_slice
          (F := fun p : ℝ^2 × ℝ ↦ sol.temperature p.1 p.2) 1 1
          fun _ ↦ h.temperature_differentiableAt_time ht
      vorticity_equation := fun {x t} hx ht ↦ ?_
      temperature_equation := fun {x t} hx ht ↦ ?_
      support := fun a b hab ↦ ?_ }
  -- The vorticity equation: near a point of the open half-plane the representative is `sol`,
  -- and the velocity is the velocity of `sol`.
  · have htime : (fun s ↦ (HalfPlaneSystem.canonical sol).vorticity x s) =
        fun s ↦ sol.vorticity x s :=
      funext fun s ↦ canonical_vorticity_of_nonneg hx.le s
    have h0 := h.vorticity_equation hx ht
    simp only [PDE.advectiveDerivative] at h0 ⊢
    change deriv (fun s ↦ (HalfPlaneSystem.canonical sol).vorticity x s) t +
        fderiv ℝ (weightedReflectionFun 1 1 (fun y ↦ sol.vorticity y t)) x
          (U (fun y ↦ (HalfPlaneSystem.canonical sol).vorticity y t) x) =
      κ x * (∂[(0 : Fin 2)] (weightedReflectionFun 1 1 (fun y ↦ sol.temperature y t))) x
    rw [htime, (hω t hx).fderiv_eq, hvel t hx, partialDeriv_congr_nhds 0 (hθ t hx)]
    exact h0
  -- The temperature equation, in the same way.
  · have htime : (fun s ↦ (HalfPlaneSystem.canonical sol).temperature x s) =
        fun s ↦ sol.temperature x s :=
      funext fun s ↦ canonical_temperature_of_nonneg hx.le s
    have h0 := h.temperature_equation hx ht
    simp only [PDE.advectiveDerivative] at h0 ⊢
    change deriv (fun s ↦ (HalfPlaneSystem.canonical sol).temperature x s) t +
        fderiv ℝ (weightedReflectionFun 1 1 (fun y ↦ sol.temperature y t)) x
          (U (fun y ↦ (HalfPlaneSystem.canonical sol).vorticity y t) x) = 0
    rw [htime, (hθ t hx).fderiv_eq, hvel t hx]
    exact h0
  -- The supports on the closed half-plane are those of `sol`.
  · obtain ⟨R, hR, hz⟩ := h.support a b hab
    exact ⟨R, hR, fun t ht x hx hxR ↦ by
      rw [canonical_vorticity_of_nonneg hx, canonical_temperature_of_nonneg hx]
      exact hz t ht x hx hxR⟩

/-- Regular solutions are preserved by the canonical representative. -/
theorem IsRegularSolutionOn.canonical {α : ℝ} (hU : IsVelocityLaw U R₀ C)
    (h : IsRegularSolutionOn U κ R₀ sol I α) (hI : UniqueDiffOn ℝ I) :
    IsRegularSolutionOn U κ R₀ (canonical sol) I α where
  toIsSolutionOn := h.toIsSolutionOn.canonical hU hI
  holderData a b hab := by
    obtain ⟨R, N, hRN⟩ := h.holderData a b hab
    exact ⟨R, N, fun t ht ↦ (hRN t ht).congr (fun x hx ↦ canonical_vorticity_of_nonneg hx t)
      (fun x hx ↦ canonical_temperature_of_nonneg hx t)⟩

/-- **The canonical representative depends only on the values on the closed half-plane.** Two
fields that agree there at a time `t` have the same canonical representative at `t`, on the
whole plane. With uniqueness on the closed half-plane this makes the canonical representatives
of two solutions with the same data equal on a common interval of times. Proof: the weighted
reflection is built from the values on the closed half-plane. -/
theorem canonical_eq_of_eqOn {t : ℝ}
    (heq : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t)
    (x : ℝ^2) :
    (canonical sol).vorticity x t = (canonical sol').vorticity x t ∧
      (canonical sol).temperature x t = (canonical sol').temperature x t :=
  ⟨congrFun (PDE.Analysis.weightedReflectionFun_congr 1 1 fun y hy ↦ (heq y hy).1) x,
    congrFun (PDE.Analysis.weightedReflectionFun_congr 1 1 fun y hy ↦ (heq y hy).2) x⟩

end HalfPlaneSystem
