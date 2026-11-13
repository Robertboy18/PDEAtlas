/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.LevelK
public import PDE.Analysis.Calculus.SmoothFamilyEvolution
public import PDE.Fluid.Boussinesq.VorticityStream.Normalization
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Regular solutions as smooth families

On an open set of times `I`, the representative `canonicalOf k sol` of a regular solution of
order `k` has vorticity and temperature slices that are smooth families of orders `k` and `k + 1`
(`C^k` in space with spatial derivatives jointly continuous in space and time), and its velocity
agrees on the closed half-plane with the extended velocity `extendedVelocity (k + 1) (ω t)`, a
smooth family of order `k + 1`. In particular the traces `ω_x(0, t)`, `θ_xx(0, t)` and
`u_x(0, t)` at the boundary point `0` are continuous in time.

## Main results

* `IsRegularSolutionOfOn.isCkVorticityHistory`.
* `IsRegularSolutionOfOn.isSmoothFamilyOn_canonicalOf_vorticity`,
  `IsRegularSolutionOfOn.isSmoothFamilyOn_canonicalOf_temperature`,
  `IsRegularSolutionOfOn.isSmoothFamilyOn_extendedVelocity`.
* `IsRegularSolutionOfOn.extendedVelocity_eq`.
* `IsRegularSolutionOfOn.continuousOn_vorticityXAtOrigin`,
  `IsRegularSolutionOfOn.continuousOn_temperatureXXAtOrigin`,
  `IsRegularSolutionOfOn.continuousOn_tangentialVelocityXAtOrigin`.
-/

@[expose] public section

noncomputable section

open Set Filter PDE.Analysis IncompressibleFlow
open scoped Topology

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {k : ℕ} {sol : VorticityStreamFields} {I : Set ℝ} {α : ℝ}

namespace IsRegularSolutionOfOn

/-- On a compact interval of times a regular solution of order `k` is a `C^{k,α}` vorticity
history. -/
theorem isCkVorticityHistory (h : IsRegularSolutionOfOn k sol I α) {a b : ℝ}
    (hab : Icc a b ⊆ I) :
    ∃ R N : ℝ, IsCkVorticityHistory k (fun t x ↦ sol.vorticity x t) a b α R N := by
  obtain ⟨R, N, hRN⟩ := h.holderData a b hab
  refine ⟨R, N,
    { contDiffOn := fun t ht ↦ (hRN t ht).vorticity_contDiffOn
      eq_zero := fun t ht y hy hyR ↦ ((hRN t ht).eq_zero y hy hyR).1
      norm_le := fun t ht j hj y hy ↦ (hRN t ht).norm_vorticity_le j hj y hy
      holder := fun t ht y z hy hz ↦ (hRN t ht).holder_vorticity y z hy hz
      uniform := fun j hj t ht ε hε ↦ ?_ }⟩
  obtain ⟨δ, hδ, h'⟩ := h.vorticity_uniform j hj t (hab ht) ε hε
  exact ⟨δ, hδ, fun s hs hst y hy ↦ h' s (hab hs) hst y hy⟩

/-- The vorticity slices of the representative of order `k` are a smooth family of order `k`. -/
theorem isSmoothFamilyOn_canonicalOf_vorticity (h : IsRegularSolutionOfOn k sol I α)
    (hk : 1 ≤ k) : IsSmoothFamilyOn k (fun t x ↦ (HalfPlane.canonicalOf k sol).vorticity x t) I :=
  ⟨fun _ ht ↦ by
    obtain ⟨R, N, hRN⟩ := h.exists_isHolderDataOf ht
    exact hRN.contDiff_canonicalOf_vorticity hk,
    fun _ hj ↦ h.continuousOn_iteratedFDeriv_canonicalOf_vorticity hk hj⟩

/-- The temperature slices of the representative of order `k` are a smooth family of order
`k + 1`. -/
theorem isSmoothFamilyOn_canonicalOf_temperature (h : IsRegularSolutionOfOn k sol I α) :
    IsSmoothFamilyOn (k + 1) (fun t x ↦ (HalfPlane.canonicalOf k sol).temperature x t) I :=
  ⟨fun _ ht ↦ by
    obtain ⟨R, N, hRN⟩ := h.exists_isHolderDataOf ht
    exact hRN.contDiff_canonicalOf_temperature,
    fun _ hj ↦ h.continuousOn_iteratedFDeriv_canonicalOf_temperature hj⟩

/-- On an open set of times, the extended velocities of the vorticity slices of a regular solution
of order `k` are a smooth family of order `k + 1`. -/
theorem isSmoothFamilyOn_extendedVelocity (h : IsRegularSolutionOfOn k sol I α) (hI : IsOpen I)
    (hα : 0 < α) (hα1 : α < 1) :
    IsSmoothFamilyOn (k + 1) (fun t ↦ extendedVelocity (k + 1) (fun y ↦ sol.vorticity y t)) I := by
  refine IsSmoothFamilyOn.of_local fun r hr ↦ ?_
  obtain ⟨a, b, hrab, hab⟩ := IsSmoothFamilyOn.exists_Icc_subset hI hr
  obtain ⟨R, N, hω⟩ := h.isCkVorticityHistory hab
  exact ⟨Ioo a b, isOpen_Ioo, hrab,
    (hω.isSmoothFamilyOn_extendedVelocity hα hα1).mono_set fun s hs ↦ Ioo_subset_Icc_self hs.1⟩

/-- On the closed half-plane the extended velocity of the vorticity slice is the velocity of the
representative of order `k`. -/
theorem extendedVelocity_eq (h : IsRegularSolutionOfOn k sol I α) (hk : 1 ≤ k)
    (hI : UniqueDiffOn ℝ I) {t : ℝ} (ht : t ∈ I) {x : ℝ^2} (hx : 0 ≤ x 1) :
    extendedVelocity (k + 1) (fun y ↦ sol.vorticity y t) x =
      vorticityStreamVelocity (HalfPlane.canonicalOf k sol) x t := by
  rw [extendedVelocity_of_nonneg _ _ hx, (h.canonicalOf hk hI).toIsSolutionOn.velocity_eq ht hx]
  have hG : GreenFunction.halfSpaceGreenPotential (fun y ↦ sol.vorticity y t) =
      GreenFunction.halfSpaceGreenPotential (fun y ↦ (HalfPlane.canonicalOf k sol).vorticity y t) :=
    GreenFunction.halfSpaceGreenPotential_congr fun y hy ↦
      (HalfPlane.canonicalOf_vorticity_of_nonneg (le_of_lt hy) t).symm
  simp only [halfPlaneVelocity, hG]

/-- The trace `ω_x(0, t)` of the representative is continuous in time. -/
theorem continuousOn_vorticityXAtOrigin (h : IsRegularSolutionOfOn k sol I α) (hk : 1 ≤ k) :
    ContinuousOn (vorticityXAtOrigin (HalfPlane.canonicalOf k sol)) I :=
  IsSmoothFamilyOn.continuousOn_iteratedPartialDeriv_apply [0]
    ((h.isSmoothFamilyOn_canonicalOf_vorticity hk).mono hk) 0

/-- The trace `θ_xx(0, t)` of the representative is continuous in time. -/
theorem continuousOn_temperatureXXAtOrigin (h : IsRegularSolutionOfOn k sol I α) (hk : 1 ≤ k) :
    ContinuousOn (temperatureXXAtOrigin (HalfPlane.canonicalOf k sol)) I :=
  IsSmoothFamilyOn.continuousOn_iteratedPartialDeriv_apply [0, 0]
    ((h.isSmoothFamilyOn_canonicalOf_temperature).mono (show 2 ≤ k + 1 by omega)) 0

/-- The strain `u_x(0, t)` of the representative is continuous in time on an open set of times. -/
theorem continuousOn_tangentialVelocityXAtOrigin (h : IsRegularSolutionOfOn k sol I α)
    (hk : 1 ≤ k) (hI : IsOpen I) (hα : 0 < α) (hα1 : α < 1) :
    ContinuousOn (tangentialVelocityXAtOrigin (HalfPlane.canonicalOf k sol)) I := by
  set V := fun t ↦ extendedVelocity (k + 1) (fun y ↦ sol.vorticity y t)
  have hV := h.isSmoothFamilyOn_extendedVelocity hI hα hα1
  have hV0 : IsSmoothFamilyOn (k + 1) (fun t x ↦ V t x 0) I :=
    (hV.clm_comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0)).congr fun _ _ ↦ rfl
  refine (IsSmoothFamilyOn.continuousOn_iteratedPartialDeriv_apply [0]
    (hV0.mono (show 1 ≤ k + 1 by omega)) 0).congr
    fun t ht ↦ ?_
  have hS := (h.canonicalOf hk hI.uniqueDiffOn).toIsSolutionOn
  have hψ := hS.classical.regularity.streamFunction_spatial_contDiff ht
  have hu : Differentiable ℝ
      (fun x ↦ vorticityStreamVelocity (HalfPlane.canonicalOf k sol) x t 0) :=
    (((contDiff_piLp (p := (2 : ENNReal))).1
      (contDiff_planarStreamVelocity _ hψ) 0).differentiable (by norm_num))
  have hVd : Differentiable ℝ (fun x ↦ V t x 0) :=
    ((hV0.contDiff ht).differentiable (by simp))
  change (∂[0] (fun x ↦ vorticityStreamVelocity (HalfPlane.canonicalOf k sol) x t 0)) 0 =
    (∂[0] (fun x ↦ V t x 0)) 0
  simp only [PDE.partialDeriv]
  rw [fderiv_eq_of_eqOn_closedUpper (by simp) (hu 0) (hVd 0)
    fun y hy ↦ by rw [show V t y = _ from h.extendedVelocity_eq hk hI.uniqueDiffOn ht hy]]

end IsRegularSolutionOfOn

end Boussinesq.HalfPlane
