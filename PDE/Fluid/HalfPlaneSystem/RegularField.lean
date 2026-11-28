/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.LevelK
public import PDE.Fluid.HalfPlaneSystem.FieldHigher

/-!
# The field of the law along a regular solution

Along a regular solution of order `k ≥ 1` of a half-plane system (`IsRegularSolutionOfOn`), with a
velocity law `U` and `0 < α < 1`, the velocity field extended across the boundary is a particle
field: on every compact interval of times it is Lipschitz in space, its spatial derivatives are
continuous in space and time, and it is tangent to the boundary.

The vorticity is a `C^{k,α}` vorticity history on every compact interval of times: the uniform
bounds of the slices and the uniform continuity in time of their derivatives are the fields of the
history. The field of the law `lawField U ω`, the extension of order two of `U (ω t)` across the
boundary, is then a smooth family of order two: its spatial derivatives of order at most two are
jointly continuous in time and space. The Lipschitz constant is not computed. Only the extension of
order two is treated; the extensions of higher order are in `FieldHigher.lean`, for histories.

## Main results

* `IsRegularSolutionOfOn.isCkVorticityHistory`: the vorticity is a vorticity history of order `k`
  with a support radius less than `R₀`.
* `IsRegularSolutionOfOn.isSmoothFamilyOn_lawField`: the field of the law is a smooth family of
  order two.
* `IsRegularSolutionOfOn.exists_isLipschitzFieldOn_lawField`: it is a Lipschitz field.
* `IsSolutionOn.lawField_normal_eq_zero`: along any solution in the class `IsSolutionOn` the field
  of the law is tangent to the boundary.

No other module of this folder uses these results. BlowupZoo uses them to show that the field of the
law of the wall of the cylinder is a particle field of its solution near the wall.
-/

@[expose] public section

noncomputable section

open Set
open IncompressibleFlow PDE.Analysis.ODE

namespace HalfPlaneSystem

set_option linter.missingDocs true

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {k : ℕ}
  {sol : Fields} {I : Set ℝ} {α : ℝ}

namespace IsRegularSolutionOfOn

/-- **The vorticity of a regular solution is a vorticity history** of order `k` on every compact
interval of times, with a support radius less than `R₀`. -/
theorem isCkVorticityHistory (h : IsRegularSolutionOfOn U κ R₀ k sol I α) {a b : ℝ}
    (hab : Icc a b ⊆ I) :
    ∃ R < R₀, ∃ N : ℝ, IsCkVorticityHistory k (fun t x ↦ sol.vorticity x t) a b α R N := by
  obtain ⟨R, hR, N, hRN⟩ := h.holderData a b hab
  refine ⟨R, hR, N,
    { contDiffOn := fun t ht ↦ (hRN t ht).vorticity_contDiffOn
      eq_zero := fun t ht y hy hyR ↦ ((hRN t ht).eq_zero y hy hyR).1
      norm_le := fun t ht j hj y hy ↦ (hRN t ht).norm_vorticity_le j hj y hy
      holder := fun t ht y z hy hz ↦ (hRN t ht).holder_vorticity y z hy hz
      uniform := fun j hj t ht ε hε ↦ ?_ }⟩
  obtain ⟨δ, hδ, hδε⟩ := h.vorticity_uniform j hj t (hab ht) ε hε
  exact ⟨δ, hδ, fun s hs hst y hy ↦ hδε s (hab hs) hst y hy⟩

/-- **The field of the law along a regular solution is a smooth family of order two** on every
compact interval of times. -/
theorem isSmoothFamilyOn_lawField (hU : IsVelocityLaw U R₀ C)
    (h : IsRegularSolutionOfOn U κ R₀ k sol I α) (hk : 1 ≤ k) (hα : 0 < α) (hα1 : α < 1)
    {a b : ℝ} (hab : Icc a b ⊆ I) :
    PDE.Analysis.IsSmoothFamilyOn 2 (lawField U (fun t x ↦ sol.vorticity x t)) (Icc a b) := by
  obtain ⟨R, hR, N, hω⟩ := (h.mono hα.le hα1.le hk).isCkVorticityHistory hab
  exact hω.isSmoothFamilyOn_extendedField_law hU hR.le le_rfl hα hα1

/-- **The field of the law along a regular solution is a Lipschitz field** on every compact
interval of times. -/
theorem exists_isLipschitzFieldOn_lawField (hU : IsVelocityLaw U R₀ C)
    (h : IsRegularSolutionOfOn U κ R₀ k sol I α) (hk : 1 ≤ k) (hα : 0 < α) (hα1 : α < 1)
    {a b : ℝ} (hab : Icc a b ⊆ I) :
    ∃ K, IsLipschitzFieldOn (lawField U (fun t x ↦ sol.vorticity x t)) a b K := by
  obtain ⟨R, hR, N, hω⟩ := (h.mono hα.le hα1.le hk).isCkVorticityHistory hab
  exact ⟨_, ((hω.toIsC1VorticityHistory le_rfl hα.le hα1.le).isC2FieldOn_lawField hU hR.le hα
    hα1).toIsC1FieldOn.isLipschitzFieldOn⟩

end IsRegularSolutionOfOn

/-- The field of the law along a solution is tangent to the boundary. -/
theorem IsSolutionOn.lawField_normal_eq_zero (hU : IsVelocityLaw U R₀ C)
    (h : IsSolutionOn U κ R₀ sol I) {t : ℝ} (ht : t ∈ I) {x : ℝ^2} (hx : x 1 = 0) :
    lawField U (fun t x ↦ sol.vorticity x t) t x 1 = 0 := by
  obtain ⟨R, hR, hz⟩ := h.exists_vorticity_eq_zero ht
  rw [lawField_of_nonneg U _ t hx.ge]
  exact hU.normal_eq_zero hR.le (h.contDiff_vorticity ht).continuous.continuousOn hz x hx

end HalfPlaneSystem
