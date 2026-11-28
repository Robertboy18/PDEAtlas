/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.LevelK
public import PDE.Fluid.HalfPlaneSystem.Canonical
public import PDE.Analysis.Calculus.HalfSpaceReflectionHigher
import PDE.FDeriv.Calculus

/-!
# Canonical representatives of order `k` of half-plane systems

A solution of a half-plane system is a pair of functions on the whole plane, but only its values on
the closed half-plane `H̄` are determined; the fields below the boundary are classical extensions.
This module builds a representative whose slices are functions on the whole plane of class `C^k` and
`C^{k+1}` with Hölder top derivatives and compact support, and whose spatial derivatives are
continuous in space and time, so that the regularity of a solution up to the boundary can be stated
with ordinary derivatives.

The representative of order `k`, `canonicalOf k sol`, replaces the fields below the boundary by the
weighted reflections of orders `k` (vorticity) and `k + 1` (temperature) of the values on `H̄`. For
`k ≥ 1` it is again a solution, regular of order `k` when `sol` is, and by construction it depends
only on the values on `H̄`. For slices of order `k` its slices are globally `C^k` and `C^{k+1}` with
compact support, and their top derivatives are globally `α`-Hölder; for a regular solution of order
`k` the spatial derivatives of orders at most `k` and `k + 1` of the representative are jointly
continuous in space and time. As in `Canonical.lean`, the set of times must have unique derivatives,
and below the boundary the representative solves no equation.

## Main results

* `canonicalOf k sol`: the representative of order `k`; `canonicalOf_vorticity_of_nonneg`,
  `canonicalOf_temperature_of_nonneg`: it has the values of `sol` on `H̄`.
* `IsSolutionOn.canonicalOf`, `IsRegularSolutionOfOn.canonicalOf`: for `k ≥ 1` the two classes are
  preserved.
* `IsHolderDataOf.contDiff_canonicalOf_vorticity`,
  `IsHolderDataOf.contDiff_canonicalOf_temperature`,
  `IsHolderDataOf.hasCompactSupport_canonicalOf_vorticity`,
  `IsHolderDataOf.hasCompactSupport_canonicalOf_temperature`,
  `IsHolderDataOf.norm_iteratedFDeriv_canonicalOf_vorticity_sub_le`,
  `IsHolderDataOf.norm_iteratedFDeriv_canonicalOf_temperature_sub_le`: for slices that are data of
  order `k` and `α ∈ [0, 1]`, the slices of the representative are globally `C^k` and `C^{k+1}`,
  have compact support, and their top derivatives are globally `α`-Hölder with constants
  `(reflectionBound k (k + 1) + 1) N` and `(reflectionBound (k + 1) (k + 2) + 1) N`.
* `IsRegularSolutionOfOn.continuousOn_iteratedFDeriv_canonicalOf_vorticity`,
  `IsRegularSolutionOfOn.continuousOn_iteratedFDeriv_canonicalOf_temperature`: for a regular
  solution of order `k` the derivatives of order `j ≤ k` of the vorticity and `j ≤ k + 1` of the
  temperature of the representative are jointly continuous on `I × ℝ²`.

`exists_maximalSolutionOf` (`PersistenceMaximal.lean`) takes the representative of order `k` of the
maximal solution, so that its conclusion has global regularity of the slices and jointly continuous
derivatives.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology
open SobolevSpace.GraphSpace.HigherOrderReflection Boussinesq.HalfPlane

open PDE (partialDeriv_congr_nhds)

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The representative of order `k` of the fields: below the boundary, the vorticity and the
temperature are the weighted reflections of orders `k` and `k + 1` of their values on the closed
half-plane. -/
def canonicalOf (k : ℕ) (sol : Fields) : Fields where
  vorticity x t := weightedReflectionFun 1 k (fun y ↦ sol.vorticity y t) x
  temperature x t := weightedReflectionFun 1 (k + 1) (fun y ↦ sol.temperature y t) x

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ}
  {k : ℕ} {sol sol' : Fields} {I : Set ℝ}

/-- On the closed half-plane the vorticity of the representative of order `k` is that of `sol`. -/
@[simp]
theorem canonicalOf_vorticity_of_nonneg {x : ℝ^2} (hx : 0 ≤ x 1) (t : ℝ) :
    (canonicalOf k sol).vorticity x t = sol.vorticity x t :=
  weightedReflectionFun_eq_of_nonneg 1 k (fun y ↦ sol.vorticity y t) x hx

/-- On the closed half-plane the temperature of the representative of order `k` is that of `sol`. -/
@[simp]
theorem canonicalOf_temperature_of_nonneg {x : ℝ^2} (hx : 0 ≤ x 1) (t : ℝ) :
    (canonicalOf k sol).temperature x t = sol.temperature x t :=
  weightedReflectionFun_eq_of_nonneg 1 (k + 1) (fun y ↦ sol.temperature y t) x hx

/-- **For `k ≥ 1` solutions are preserved by the representative of order `k`.** If `sol` solves
the half-plane system on a set of times with unique derivatives, so does `canonicalOf k sol`.
The representative can therefore replace the solution in every statement on the closed
half-plane. Proof: the weighted reflections of orders `k ≥ 1` and `k + 1` keep the joint `C¹`
regularity; in the open half-plane the representative agrees with `sol` near every point, and
the velocity law sees only the values on the closed half-plane. -/
theorem IsSolutionOn.canonicalOf (hU : IsVelocityLaw U R₀ C) (h : IsSolutionOn U κ R₀ sol I)
    (hk : 1 ≤ k) (hI : UniqueDiffOn ℝ I) : IsSolutionOn U κ R₀ (canonicalOf k sol) I := by
  have hvel (t : ℝ) {x : ℝ^2} (hx : 0 < x 1) :
      U (fun y ↦ (HalfPlaneSystem.canonicalOf k sol).vorticity y t) x =
        U (fun y ↦ sol.vorticity y t) x :=
    hU.congr (fun y hy ↦ canonicalOf_vorticity_of_nonneg hy t) x hx.le
  have hω (t : ℝ) {x : ℝ^2} (hx : 0 < x 1) :=
    eventuallyEq_canonical (f := fun y ↦ sol.vorticity y t) k (x := x) hx
  have hθ (t : ℝ) {x : ℝ^2} (hx : 0 < x 1) :=
    eventuallyEq_canonical (f := fun y ↦ sol.temperature y t) (k + 1) (x := x) hx
  refine
    { vorticity_contDiffOn := PDE.Analysis.contDiffOn_weightedReflectionFun_slice
        (F := fun p : ℝ^2 × ℝ ↦ sol.vorticity p.1 p.2) 1 hk hI h.vorticity_contDiffOn
      temperature_contDiffOn := PDE.Analysis.contDiffOn_weightedReflectionFun_slice
        (F := fun p : ℝ^2 × ℝ ↦ sol.temperature p.1 p.2) 1 (by omega) hI
        h.temperature_contDiffOn
      vorticity_differentiableAt_time := fun ht ↦
        PDE.Analysis.differentiableAt_weightedReflectionFun_slice
          (F := fun p : ℝ^2 × ℝ ↦ sol.vorticity p.1 p.2) 1 k
          fun _ ↦ h.vorticity_differentiableAt_time ht
      temperature_differentiableAt_time := fun ht ↦
        PDE.Analysis.differentiableAt_weightedReflectionFun_slice
          (F := fun p : ℝ^2 × ℝ ↦ sol.temperature p.1 p.2) 1 (k + 1)
          fun _ ↦ h.temperature_differentiableAt_time ht
      vorticity_equation := fun {x t} hx ht ↦ ?_
      temperature_equation := fun {x t} hx ht ↦ ?_
      support := fun a b hab ↦ ?_ }
  -- The vorticity equation: near a point of the open half-plane the representative is `sol`,
  -- and the velocity is the velocity of `sol`.
  · have htime : (fun s ↦ (HalfPlaneSystem.canonicalOf k sol).vorticity x s) =
        fun s ↦ sol.vorticity x s :=
      funext fun s ↦ canonicalOf_vorticity_of_nonneg hx.le s
    have h0 := h.vorticity_equation hx ht
    simp only [PDE.advectiveDerivative] at h0 ⊢
    change deriv (fun s ↦ (HalfPlaneSystem.canonicalOf k sol).vorticity x s) t +
        fderiv ℝ (weightedReflectionFun 1 k (fun y ↦ sol.vorticity y t)) x
          (U (fun y ↦ (HalfPlaneSystem.canonicalOf k sol).vorticity y t) x) =
      κ x * (∂[(0 : Fin 2)] (weightedReflectionFun 1 (k + 1) (fun y ↦ sol.temperature y t))) x
    rw [htime, (hω t hx).fderiv_eq, hvel t hx, partialDeriv_congr_nhds 0 (hθ t hx)]
    exact h0
  -- The temperature equation, in the same way.
  · have htime : (fun s ↦ (HalfPlaneSystem.canonicalOf k sol).temperature x s) =
        fun s ↦ sol.temperature x s :=
      funext fun s ↦ canonicalOf_temperature_of_nonneg hx.le s
    have h0 := h.temperature_equation hx ht
    simp only [PDE.advectiveDerivative] at h0 ⊢
    change deriv (fun s ↦ (HalfPlaneSystem.canonicalOf k sol).temperature x s) t +
        fderiv ℝ (weightedReflectionFun 1 (k + 1) (fun y ↦ sol.temperature y t)) x
          (U (fun y ↦ (HalfPlaneSystem.canonicalOf k sol).vorticity y t) x) = 0
    rw [htime, (hθ t hx).fderiv_eq, hvel t hx]
    exact h0
  -- The supports on the closed half-plane are those of `sol`.
  · obtain ⟨R, hR, hz⟩ := h.support a b hab
    exact ⟨R, hR, fun t ht x hx hxR ↦ by
      rw [canonicalOf_vorticity_of_nonneg hx, canonicalOf_temperature_of_nonneg hx]
      exact hz t ht x hx hxR⟩

/-- **For `k ≥ 1` regular solutions of order `k` are preserved by the representative of order
`k`.** -/
theorem IsRegularSolutionOfOn.canonicalOf {α : ℝ} (hU : IsVelocityLaw U R₀ C)
    (h : IsRegularSolutionOfOn U κ R₀ k sol I α) (hk : 1 ≤ k) (hI : UniqueDiffOn ℝ I) :
    IsRegularSolutionOfOn U κ R₀ k (HalfPlaneSystem.canonicalOf k sol) I α :=
  h.congr (h.toIsSolutionOn.canonicalOf hU hk hI) fun t _ _ hx ↦
    ⟨canonicalOf_vorticity_of_nonneg hx t, canonicalOf_temperature_of_nonneg hx t⟩

/-! ### Regularity of the representatives -/

namespace IsHolderDataOf

variable {t α R N : ℝ}

/-- For slices of order `k ≥ 1`, the vorticity slice of the representative is globally `C^k`. -/
theorem contDiff_canonicalOf_vorticity
    (h : IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N)
    (hk : 1 ≤ k) : ContDiff ℝ k (fun x ↦ (canonicalOf k sol).vorticity x t) :=
  PDE.Analysis.contDiff_weightedReflectionFun 1 hk h.vorticity_contDiffOn

/-- For slices of order `k`, the temperature slice of the representative is globally
`C^{k+1}`. -/
theorem contDiff_canonicalOf_temperature
    (h : IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N) :
    ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun x ↦ (canonicalOf k sol).temperature x t) :=
  PDE.Analysis.contDiff_weightedReflectionFun 1 (k := k + 1) (by omega) h.temperature_contDiffOn

/-- For slices of order `k ≥ 1` and `0 ≤ α ≤ 1`, the `k`-th derivative of the vorticity slice of
the representative is globally `α`-Hölder with constant `(reflectionBound k (k + 1) + 1) N`. -/
theorem norm_iteratedFDeriv_canonicalOf_vorticity_sub_le
    (h : IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N)
    (hk : 1 ≤ k) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (x x' : ℝ^2) :
    ‖iteratedFDeriv ℝ k (fun y ↦ (canonicalOf k sol).vorticity y t) x -
        iteratedFDeriv ℝ k (fun y ↦ (canonicalOf k sol).vorticity y t) x'‖ ≤
      (PDE.Analysis.reflectionBound k (k + 1) + 1) * N * ‖x - x'‖ ^ α :=
  PDE.Analysis.norm_iteratedFDeriv_weightedReflectionFun_sub_rpow_le 1 hk h.vorticity_contDiffOn
    hα0 hα1 h.nonneg h.holder_vorticity x x'

/-- For slices of order `k` and `0 ≤ α ≤ 1`, the `(k + 1)`-th derivative of the temperature slice
of the representative is globally `α`-Hölder with constant
`(reflectionBound (k + 1) (k + 2) + 1) N`. -/
theorem norm_iteratedFDeriv_canonicalOf_temperature_sub_le
    (h : IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (x x' : ℝ^2) :
    ‖iteratedFDeriv ℝ (k + 1) (fun y ↦ (canonicalOf k sol).temperature y t) x -
        iteratedFDeriv ℝ (k + 1) (fun y ↦ (canonicalOf k sol).temperature y t) x'‖ ≤
      (PDE.Analysis.reflectionBound (k + 1) (k + 2) + 1) * N * ‖x - x'‖ ^ α :=
  PDE.Analysis.norm_iteratedFDeriv_weightedReflectionFun_sub_rpow_le 1 (k := k + 1) (by omega)
    h.temperature_contDiffOn hα0 hα1 h.nonneg h.holder_temperature x x'

/-- For slices of order `k`, the vorticity slice of the representative has compact support. -/
theorem hasCompactSupport_canonicalOf_vorticity
    (h : IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N) :
    HasCompactSupport (fun x ↦ (canonicalOf k sol).vorticity x t) :=
  PDE.Analysis.hasCompactSupport_weightedReflectionFun 1 (R := R)
    fun y hy hyR ↦ (h.eq_zero y hy hyR).1

/-- For slices of order `k`, the temperature slice of the representative has compact support. -/
theorem hasCompactSupport_canonicalOf_temperature
    (h : IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N) :
    HasCompactSupport (fun x ↦ (canonicalOf k sol).temperature x t) :=
  PDE.Analysis.hasCompactSupport_weightedReflectionFun 1 (R := R)
    fun y hy hyR ↦ (h.eq_zero y hy hyR).2

end IsHolderDataOf

namespace IsRegularSolutionOfOn

variable {α : ℝ}

/-- **Continuous vorticity jets.** For a regular solution of order `k ≥ 1`, the derivatives of
order `j ≤ k` of the vorticity slices of the representative are jointly continuous on
`I × ℝ²`. -/
theorem continuousOn_iteratedFDeriv_canonicalOf_vorticity
    (h : IsRegularSolutionOfOn U κ R₀ k sol I α) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) :
    ContinuousOn
      (fun p : ℝ × ℝ^2 ↦
        iteratedFDeriv ℝ j (fun x ↦ (HalfPlaneSystem.canonicalOf k sol).vorticity x p.1) p.2)
      (I ×ˢ univ) :=
  PDE.Analysis.continuousOn_iteratedFDeriv_weightedReflectionFun 1 hk
    (F := fun t y ↦ sol.vorticity y t)
    (fun _ ht ↦ (h.exists_isHolderDataOf ht).choose_spec.2.choose_spec.vorticity_contDiffOn) hj
    (h.vorticity_uniform j hj)

/-- **Continuous temperature jets.** For a regular solution of order `k`, the derivatives of
order `j ≤ k + 1` of the temperature slices of the representative are jointly continuous on
`I × ℝ²`. -/
theorem continuousOn_iteratedFDeriv_canonicalOf_temperature
    (h : IsRegularSolutionOfOn U κ R₀ k sol I α) {j : ℕ} (hj : j ≤ k + 1) :
    ContinuousOn
      (fun p : ℝ × ℝ^2 ↦
        iteratedFDeriv ℝ j (fun x ↦ (HalfPlaneSystem.canonicalOf k sol).temperature x p.1) p.2)
      (I ×ˢ univ) :=
  PDE.Analysis.continuousOn_iteratedFDeriv_weightedReflectionFun 1 (k := k + 1) (by omega)
    (F := fun t y ↦ sol.temperature y t)
    (fun _ ht ↦ (h.exists_isHolderDataOf ht).choose_spec.2.choose_spec.temperature_contDiffOn) hj
    (h.temperature_uniform j hj)

end IsRegularSolutionOfOn

end HalfPlaneSystem
