/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Canonical
public import PDE.Fluid.Boussinesq.HalfPlane.Symmetry
public import PDE.Fluid.Incompressible.HalfPlane.VelocityFieldHigher
import PDE.FDeriv.Laplacian.Congruence
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.Linearity

/-!
# Half-plane Boussinesq data and solutions of class `C^{k,α} × C^{k+1,α}`

The data class `IsHolderDataOf k ω₀ θ₀ α R N` asks `ω₀ ∈ C^{k,α}` and `θ₀ ∈ C^{k+1,α}` within the
closed half-plane `H̄`, both vanishing there outside the disc of radius `R`, with every derivative
within `H̄` and the top Hölder constants at most `N`. For `k ≥ 1` it is the class `IsHolderData`
of the local theorem with the bound `2N` (`IsHolderDataOf.toIsHolderData`), and `IsHolderData` is
the class of order one (`IsHolderData.toIsHolderDataOf`). A regular solution of order `k`
(`IsRegularSolutionOfOn k`) is a solution whose slices are data of order `k` with bounds uniform
on compact intervals of times and whose spatial derivatives within `H̄` are continuous in time
uniformly on `H̄`.

The whole-plane representative `canonicalOf k sol` replaces the fields below the boundary by the
weighted reflections of orders `k`, `k + 1` and `k + 2` of their values on `H̄`. It is again a
solution (`IsSolutionOn.canonicalOf`) and depends only on the values on `H̄`
(`IsSolutionOn.canonicalOf_eq`). For slices of order `k` its slices are globally `C^k` and
`C^{k+1}` with compact support, and their top derivatives are globally `α`-Hölder; for a regular
solution of order `k` their spatial derivatives of orders at most `k` and `k + 1` are jointly
continuous in space and time. Representatives of symmetric slices are symmetric.

## Main definitions

* `IsHolderDataOf`, `IsRegularSolutionOfOn`, `canonicalOf`.

## Main results

* `IsHolderDataOf.toIsHolderData`, `IsHolderData.toIsHolderDataOf`, `IsHolderDataOf.mono`,
  `IsHolderDataOf.congr`, `IsHolderDataOf.of_le`, `IsHolderDataOf.of_eq_zero`,
  `IsRegularSolutionOfOn.toIsRegularSolutionOn`.
* `IsSolutionOn.canonicalOf`, `canonicalOf_eq_of_eqOn`, `IsSolutionOn.canonicalOf_eq`.
* `IsHolderDataOf.contDiff_canonicalOf_vorticity`,
  `IsHolderDataOf.norm_iteratedFDeriv_canonicalOf_vorticity_sub_le`,
  `IsHolderDataOf.hasCompactSupport_canonicalOf_vorticity` and their temperature versions.
* `IsRegularSolutionOfOn.continuousOn_iteratedFDeriv_canonicalOf_vorticity`,
  `IsRegularSolutionOfOn.continuousOn_iteratedFDeriv_canonicalOf_temperature`.
* `canonicalOf_vorticity_tangentialReflection`, `canonicalOf_temperature_tangentialReflection`,
  `IsSolutionOn.canonicalOf_streamFunction_tangentialReflection`.

## How it works

The reflections leave the values on `H̄` unchanged (`canonicalOf_vorticity_of_nonneg`,
`canonicalOf_temperature_of_nonneg`, `canonicalOf_streamFunction_of_nonneg`), and near each point of
the open half-plane the representative agrees with the fields (`eventuallyEq_canonical`). So the
velocity, both transport equations and the Poisson equation hold there exactly as for the fields,
and the Dirichlet condition reads only values on the boundary line
(`Boussinesq.IsClassicalVorticityStreamSolutionOn.canonicalOf`). The Green potential reads the
vorticity only on the open half-plane (`halfSpaceGreenPotential_canonicalOf`), which gives the
stream law of `IsSolutionOn.canonicalOf`. The global regularity, the derivative and Hölder bounds,
the compact supports and the parities are the corresponding facts for weighted reflections, such as
`PDE.Analysis.contDiff_weightedReflectionFun` and
`PDE.Analysis.norm_iteratedFDeriv_weightedReflectionFun_sub_rpow_le`. The stream function is only
`C²` but is reflected with order `k + 2`; this uses the regularity of weighted reflections of every
order at least the regularity (`PDE.Analysis.contDiff_weightedReflectionFun_of_le`).
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology
open GreenFunction IncompressibleFlow SobolevSpace.GraphSpace.HigherOrderReflection

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### Data of order `k` -/

/-- Data `ω₀ ∈ C^{k,α}` and `θ₀ ∈ C^{k+1,α}` within the closed half-plane, vanishing there outside
the disc of radius `R`, with every derivative within the closed half-plane and the Hölder
constants of the top derivatives at most `N`. -/
structure IsHolderDataOf (k : ℕ) (ω₀ θ₀ : ℝ^2 → ℝ) (α R N : ℝ) : Prop where
  /-- The vorticity is `C^k` within the closed half-plane. -/
  vorticity_contDiffOn : ContDiffOn ℝ k ω₀ H̄
  /-- The temperature is `C^{k+1}` within the closed half-plane. -/
  temperature_contDiffOn : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) θ₀ H̄
  /-- Both vanish on the closed half-plane outside the disc of radius `R`. -/
  eq_zero : ∀ x : ℝ^2, 0 ≤ x 1 → R < ‖x‖ → ω₀ x = 0 ∧ θ₀ x = 0
  /-- The derivatives of the vorticity of order at most `k` are bounded by `N`. -/
  norm_vorticity_le : ∀ j ≤ k, ∀ x : ℝ^2, 0 ≤ x 1 → ‖iteratedFDerivWithin ℝ j ω₀ H̄ x‖ ≤ N
  /-- The `k`-th derivative of the vorticity is `α`-Hölder with constant `N`. -/
  holder_vorticity : ∀ x y : ℝ^2, 0 ≤ x 1 → 0 ≤ y 1 →
    ‖iteratedFDerivWithin ℝ k ω₀ H̄ x - iteratedFDerivWithin ℝ k ω₀ H̄ y‖ ≤ N * ‖x - y‖ ^ α
  /-- The derivatives of the temperature of order at most `k + 1` are bounded by `N`. -/
  norm_temperature_le : ∀ j ≤ k + 1, ∀ x : ℝ^2, 0 ≤ x 1 →
    ‖iteratedFDerivWithin ℝ j θ₀ H̄ x‖ ≤ N
  /-- The `(k + 1)`-th derivative of the temperature is `α`-Hölder with constant `N`. -/
  holder_temperature : ∀ x y : ℝ^2, 0 ≤ x 1 → 0 ≤ y 1 →
    ‖iteratedFDerivWithin ℝ (k + 1) θ₀ H̄ x - iteratedFDerivWithin ℝ (k + 1) θ₀ H̄ y‖ ≤
      N * ‖x - y‖ ^ α

namespace IsHolderDataOf

variable {k : ℕ} {ω₀ θ₀ ω₁ θ₁ : ℝ^2 → ℝ} {α R N : ℝ}

/-- The bound of data of order `k` is nonnegative. -/
theorem nonneg (h : IsHolderDataOf k ω₀ θ₀ α R N) : 0 ≤ N :=
  (norm_nonneg _).trans (h.norm_vorticity_le 0 (Nat.zero_le k) 0 (by simp))

/-- Every derivative of order at most `k` of the vorticity is `α`-Hölder with constant `2N`. -/
theorem norm_iteratedFDerivWithin_vorticity_sub_le (h : IsHolderDataOf k ω₀ θ₀ α R N)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {j : ℕ} (hj : j ≤ k) {x y : ℝ^2} (hx : 0 ≤ x 1)
    (hy : 0 ≤ y 1) :
    ‖iteratedFDerivWithin ℝ j ω₀ H̄ x - iteratedFDerivWithin ℝ j ω₀ H̄ y‖ ≤
      2 * N * ‖x - y‖ ^ α :=
  PDE.Analysis.norm_iteratedFDerivWithin_sub_le_two_mul h.vorticity_contDiffOn h.norm_vorticity_le
    h.holder_vorticity hα0 hα1 hj hx hy

/-- Every derivative of order at most `k + 1` of the temperature is `α`-Hölder with constant
`2N`. -/
theorem norm_iteratedFDerivWithin_temperature_sub_le (h : IsHolderDataOf k ω₀ θ₀ α R N)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {j : ℕ} (hj : j ≤ k + 1) {x y : ℝ^2} (hx : 0 ≤ x 1)
    (hy : 0 ≤ y 1) :
    ‖iteratedFDerivWithin ℝ j θ₀ H̄ x - iteratedFDerivWithin ℝ j θ₀ H̄ y‖ ≤
      2 * N * ‖x - y‖ ^ α :=
  PDE.Analysis.norm_iteratedFDerivWithin_sub_le_two_mul h.temperature_contDiffOn
    h.norm_temperature_le h.holder_temperature hα0 hα1 hj hx hy

/-- **Lowering the order.** Data of order `k` are data of every order `j ≤ k` with the bound
`2N`. -/
theorem mono (h : IsHolderDataOf k ω₀ θ₀ α R N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {j : ℕ}
    (hj : j ≤ k) : IsHolderDataOf j ω₀ θ₀ α R (2 * N) where
  vorticity_contDiffOn := h.vorticity_contDiffOn.of_le (by exact_mod_cast hj)
  temperature_contDiffOn := h.temperature_contDiffOn.of_le (by exact_mod_cast (by omega))
  eq_zero := h.eq_zero
  norm_vorticity_le i hi x hx :=
    (h.norm_vorticity_le i (hi.trans hj) x hx).trans (by linarith [h.nonneg])
  holder_vorticity x y hx hy := h.norm_iteratedFDerivWithin_vorticity_sub_le hα0 hα1 hj hx hy
  norm_temperature_le i hi x hx :=
    (h.norm_temperature_le i (by omega) x hx).trans (by linarith [h.nonneg])
  holder_temperature x y hx hy :=
    h.norm_iteratedFDerivWithin_temperature_sub_le hα0 hα1 (by omega) hx hy

/-- **Data of order `k ≥ 1` are data of the local theorem** with the bound `2N`: the gradients
below the top order are Lipschitz and bounded, hence `α`-Hölder with constant `2N`. -/
theorem toIsHolderData (h : IsHolderDataOf k ω₀ θ₀ α R N) (hk : 1 ≤ k) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : IsHolderData ω₀ θ₀ α R (2 * N) where
  vorticity_contDiffOn := h.vorticity_contDiffOn.of_le (by exact_mod_cast hk)
  temperature_contDiffOn :=
    h.temperature_contDiffOn.of_le (by exact_mod_cast (show 2 ≤ k + 1 by omega))
  eq_zero := h.eq_zero
  abs_vorticity_le x hx := by
    have h0 := h.norm_vorticity_le 0 (Nat.zero_le k) x hx
    rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] at h0
    linarith [h.nonneg]
  norm_fderivWithin_vorticity_le x hx := by
    have h1 := h.norm_vorticity_le 1 hk x hx
    rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper x hx)] at h1
    linarith [h.nonneg]
  holder_vorticity x y hx hy := by
    have h1 := h.norm_iteratedFDerivWithin_vorticity_sub_le hα0 hα1 hk hx hy
    rwa [norm_iteratedFDerivWithin_one_sub _ hx hy] at h1
  abs_temperature_le x hx := by
    have h0 := h.norm_temperature_le 0 (Nat.zero_le _) x hx
    rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] at h0
    linarith [h.nonneg]
  norm_fderivWithin_temperature_le x hx := by
    have h1 := h.norm_temperature_le 1 (by omega) x hx
    rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper x hx)] at h1
    linarith [h.nonneg]
  norm_fderivWithin_fderivWithin_temperature_le x hx := by
    have h2 := h.norm_temperature_le 2 (by omega) x hx
    rw [norm_iteratedFDerivWithin_two _ hx] at h2
    linarith [h.nonneg]
  holder_temperature x y hx hy := by
    have h2 := h.norm_iteratedFDerivWithin_temperature_sub_le hα0 hα1 (j := 2) (by omega) hx hy
    rwa [norm_iteratedFDerivWithin_succ_sub _ hx hy 1,
      norm_iteratedFDerivWithin_one_sub _ hx hy] at h2

/-- The data class of order `k` depends only on the values on the closed half-plane. -/
theorem congr (h : IsHolderDataOf k ω₀ θ₀ α R N) (hω : ∀ x : ℝ^2, 0 ≤ x 1 → ω₁ x = ω₀ x)
    (hθ : ∀ x : ℝ^2, 0 ≤ x 1 → θ₁ x = θ₀ x) : IsHolderDataOf k ω₁ θ₁ α R N := by
  have hω' : EqOn ω₁ ω₀ H̄ := fun x hx ↦ hω x hx
  have hθ' : EqOn θ₁ θ₀ H̄ := fun x hx ↦ hθ x hx
  have dω (j : ℕ) {x : ℝ^2} (hx : 0 ≤ x 1) :
      iteratedFDerivWithin ℝ j ω₁ H̄ x = iteratedFDerivWithin ℝ j ω₀ H̄ x :=
    iteratedFDerivWithin_congr hω' hx j
  have dθ (j : ℕ) {x : ℝ^2} (hx : 0 ≤ x 1) :
      iteratedFDerivWithin ℝ j θ₁ H̄ x = iteratedFDerivWithin ℝ j θ₀ H̄ x :=
    iteratedFDerivWithin_congr hθ' hx j
  exact
    { vorticity_contDiffOn := h.vorticity_contDiffOn.congr hω'
      temperature_contDiffOn := h.temperature_contDiffOn.congr hθ'
      eq_zero := fun x hx hxR ↦ by
        rw [hω x hx, hθ x hx]
        exact h.eq_zero x hx hxR
      norm_vorticity_le := fun j hj x hx ↦ by
        rw [dω j hx]; exact h.norm_vorticity_le j hj x hx
      holder_vorticity := fun x y hx hy ↦ by
        rw [dω k hx, dω k hy]; exact h.holder_vorticity x y hx hy
      norm_temperature_le := fun j hj x hx ↦ by
        rw [dθ j hx]; exact h.norm_temperature_le j hj x hx
      holder_temperature := fun x y hx hy ↦ by
        rw [dθ (k + 1) hx, dθ (k + 1) hy]; exact h.holder_temperature x y hx hy }

end IsHolderDataOf

/-- Data of order `k` keep the class for a larger support radius and a larger bound. -/
theorem IsHolderDataOf.of_le {k : ℕ} {ω₀ θ₀ : ℝ^2 → ℝ} {α R N R' N' : ℝ}
    (h : IsHolderDataOf k ω₀ θ₀ α R N) (hR : R ≤ R') (hN : N ≤ N') :
    IsHolderDataOf k ω₀ θ₀ α R' N' where
  vorticity_contDiffOn := h.vorticity_contDiffOn
  temperature_contDiffOn := h.temperature_contDiffOn
  eq_zero x hx hxR := h.eq_zero x hx (hR.trans_lt hxR)
  norm_vorticity_le j hj x hx := (h.norm_vorticity_le j hj x hx).trans hN
  holder_vorticity x y hx hy := (h.holder_vorticity x y hx hy).trans
    (mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg (norm_nonneg _) α))
  norm_temperature_le j hj x hx := (h.norm_temperature_le j hj x hx).trans hN
  holder_temperature x y hx hy := (h.holder_temperature x y hx hy).trans
    (mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg (norm_nonneg _) α))

/-- Data of order `k` that vanish on the closed half-plane outside the disc of radius `R'` have
the support radius `R'`. -/
theorem IsHolderDataOf.of_eq_zero {k : ℕ} {ω₀ θ₀ : ℝ^2 → ℝ} {α R N R' : ℝ}
    (h : IsHolderDataOf k ω₀ θ₀ α R N)
    (h' : ∀ x : ℝ^2, 0 ≤ x 1 → R' < ‖x‖ → ω₀ x = 0 ∧ θ₀ x = 0) :
    IsHolderDataOf k ω₀ θ₀ α R' N :=
  { h with eq_zero := h' }

/-- **The data of the local theorem are the data of order one.** -/
theorem IsHolderData.toIsHolderDataOf {ω₀ θ₀ : ℝ^2 → ℝ} {α R N : ℝ}
    (h : IsHolderData ω₀ θ₀ α R N) : IsHolderDataOf 1 ω₀ θ₀ α R N where
  vorticity_contDiffOn := by exact_mod_cast h.vorticity_contDiffOn
  temperature_contDiffOn := by exact_mod_cast h.temperature_contDiffOn
  eq_zero := h.eq_zero
  norm_vorticity_le j hj x hx := by
    interval_cases j
    · rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
      exact h.abs_vorticity_le x hx
    · rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper x hx)]
      exact h.norm_fderivWithin_vorticity_le x hx
  holder_vorticity x y hx hy := by
    rw [norm_iteratedFDerivWithin_one_sub _ hx hy]
    exact h.holder_vorticity x y hx hy
  norm_temperature_le j hj x hx := by
    interval_cases j
    · rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
      exact h.abs_temperature_le x hx
    · rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper x hx)]
      exact h.norm_fderivWithin_temperature_le x hx
    · rw [norm_iteratedFDerivWithin_two _ hx]
      exact h.norm_fderivWithin_fderivWithin_temperature_le x hx
  holder_temperature x y hx hy := by
    rw [norm_iteratedFDerivWithin_succ_sub _ hx hy 1, norm_iteratedFDerivWithin_one_sub _ hx hy]
    exact h.holder_temperature x y hx hy

/-! ### Regular solutions of order `k` -/

/-- A solution whose time slices are data of order `k` with support radius and bounds uniform on
every compact subinterval of the times, and whose spatial derivatives within the closed
half-plane, of orders at most `k` for the vorticity and `k + 1` for the temperature, are
continuous in time uniformly on the closed half-plane. -/
structure IsRegularSolutionOfOn (k : ℕ) (sol : VorticityStreamFields) (I : Set ℝ) (α : ℝ) :
    Prop extends IsSolutionOn sol I where
  /-- Uniform `C^{k,α} × C^{k+1,α}` bounds of the slices on compact subintervals. -/
  holderData : ∀ a b : ℝ, Icc a b ⊆ I → ∃ R N : ℝ, ∀ t ∈ Icc a b,
    IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N
  /-- The derivatives of the vorticity of order at most `k` are continuous in time uniformly on
  the closed half-plane. -/
  vorticity_uniform : ∀ j ≤ k, ∀ t ∈ I, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ I, |s - t| < δ →
    ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖iteratedFDerivWithin ℝ j (fun y ↦ sol.vorticity y s) H̄ x -
        iteratedFDerivWithin ℝ j (fun y ↦ sol.vorticity y t) H̄ x‖ ≤ ε
  /-- The derivatives of the temperature of order at most `k + 1` are continuous in time
  uniformly on the closed half-plane. -/
  temperature_uniform : ∀ j ≤ k + 1, ∀ t ∈ I, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ I, |s - t| < δ →
    ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖iteratedFDerivWithin ℝ j (fun y ↦ sol.temperature y s) H̄ x -
        iteratedFDerivWithin ℝ j (fun y ↦ sol.temperature y t) H̄ x‖ ≤ ε

namespace IsRegularSolutionOfOn

variable {k : ℕ} {sol : VorticityStreamFields} {I : Set ℝ} {α : ℝ}

/-- **Regular solutions of order `k ≥ 1` are regular solutions.** -/
theorem toIsRegularSolutionOn (h : IsRegularSolutionOfOn k sol I α) (hk : 1 ≤ k)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : IsRegularSolutionOn sol I α where
  toIsSolutionOn := h.toIsSolutionOn
  holderData a b hab := by
    obtain ⟨R, N, hRN⟩ := h.holderData a b hab
    exact ⟨R, 2 * N, fun t ht ↦ (hRN t ht).toIsHolderData hk hα0 hα1⟩

/-- Regular solutions of order `k` are regular solutions of every order `j ≤ k`. -/
theorem mono (h : IsRegularSolutionOfOn k sol I α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {j : ℕ}
    (hj : j ≤ k) : IsRegularSolutionOfOn j sol I α where
  toIsSolutionOn := h.toIsSolutionOn
  holderData a b hab := by
    obtain ⟨R, N, hRN⟩ := h.holderData a b hab
    exact ⟨R, 2 * N, fun t ht ↦ (hRN t ht).mono hα0 hα1 hj⟩
  vorticity_uniform i hi := h.vorticity_uniform i (hi.trans hj)
  temperature_uniform i hi := h.temperature_uniform i (by omega)

/-- At every time a slice of a regular solution of order `k` is data of order `k`. -/
theorem exists_isHolderDataOf (h : IsRegularSolutionOfOn k sol I α) {t : ℝ} (ht : t ∈ I) :
    ∃ R N : ℝ,
      IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N := by
  obtain ⟨R, N, hRN⟩ := h.holderData t t (by simpa using ht)
  exact ⟨R, N, hRN t ⟨le_rfl, le_rfl⟩⟩

end IsRegularSolutionOfOn

/-! ### Whole-plane representatives of order `k` -/

/-- The representative of order `k` of the fields: below the boundary, the vorticity, the
temperature and the stream function are the weighted reflections of orders `k`, `k + 1` and
`k + 2` of their values on the closed half-plane. -/
def canonicalOf (k : ℕ) (sol : VorticityStreamFields) : VorticityStreamFields where
  vorticity x t := weightedReflectionFun 1 k (fun y ↦ sol.vorticity y t) x
  temperature x t := weightedReflectionFun 1 (k + 1) (fun y ↦ sol.temperature y t) x
  streamFunction x t := weightedReflectionFun 1 (k + 2) (fun y ↦ sol.streamFunction y t) x

variable {k : ℕ} {sol sol' : VorticityStreamFields} {I : Set ℝ}

/-- On the closed half-plane the representative of order `k` has the vorticity of the fields. -/
@[simp]
theorem canonicalOf_vorticity_of_nonneg {x : ℝ^2} (hx : 0 ≤ x 1) (t : ℝ) :
    (canonicalOf k sol).vorticity x t = sol.vorticity x t :=
  weightedReflectionFun_eq_of_nonneg 1 k (fun y ↦ sol.vorticity y t) x hx

/-- On the closed half-plane the representative of order `k` has the temperature of the fields. -/
@[simp]
theorem canonicalOf_temperature_of_nonneg {x : ℝ^2} (hx : 0 ≤ x 1) (t : ℝ) :
    (canonicalOf k sol).temperature x t = sol.temperature x t :=
  weightedReflectionFun_eq_of_nonneg 1 (k + 1) (fun y ↦ sol.temperature y t) x hx

/-- On the closed half-plane the representative of order `k` has the stream function of the
fields. -/
@[simp]
theorem canonicalOf_streamFunction_of_nonneg {x : ℝ^2} (hx : 0 ≤ x 1) (t : ℝ) :
    (canonicalOf k sol).streamFunction x t = sol.streamFunction x t :=
  weightedReflectionFun_eq_of_nonneg 1 (k + 2) (fun y ↦ sol.streamFunction y t) x hx

/-- On the open half-plane the velocity of the representative is the velocity. -/
theorem vorticityStreamVelocity_canonicalOf {x : ℝ^2} (hx : x ∈ upperHalfPlane) (t : ℝ) :
    vorticityStreamVelocity (canonicalOf k sol) x t = vorticityStreamVelocity sol x t := by
  have h := (eventuallyEq_canonical (f := fun y ↦ sol.streamFunction y t) (k + 2) hx).fderiv_eq
    (𝕜 := ℝ)
  simp only [vorticityStreamVelocity, planarStreamVelocity]
  change WithLp.toLp 2 ![-(fderiv ℝ (weightedReflectionFun 1 (k + 2)
      (fun y ↦ sol.streamFunction y t)) x (EuclideanSpace.single 1 1)),
      fderiv ℝ (weightedReflectionFun 1 (k + 2) (fun y ↦ sol.streamFunction y t)) x
        (EuclideanSpace.single 0 1)] = _
  rw [h]
  rfl

/-- For `k ≥ 1` the classical class is preserved by the representative of order `k`. -/
theorem _root_.Boussinesq.IsClassicalVorticityStreamSolutionOn.canonicalOf
    (h : IsClassicalVorticityStreamSolutionOn sol I) (hk : 1 ≤ k) (hI : UniqueDiffOn ℝ I) :
    IsClassicalVorticityStreamSolutionOn (HalfPlane.canonicalOf k sol) I where
  regularity :=
    { vorticity_contDiffOn := PDE.Analysis.contDiffOn_weightedReflectionFun_slice
        (F := fun p : ℝ^2 × ℝ ↦ sol.vorticity p.1 p.2) 1 hk hI
        h.regularity.vorticity_contDiffOn
      temperature_contDiffOn := PDE.Analysis.contDiffOn_weightedReflectionFun_slice
        (F := fun p : ℝ^2 × ℝ ↦ sol.temperature p.1 p.2) 1 (by omega) hI
        h.regularity.temperature_contDiffOn
      vorticity_differentiableAt_time := fun ht ↦
        PDE.Analysis.differentiableAt_weightedReflectionFun_slice
          (F := fun p : ℝ^2 × ℝ ↦ sol.vorticity p.1 p.2) 1 k
          fun _ ↦ h.regularity.vorticity_differentiableAt_time ht
      temperature_differentiableAt_time := fun ht ↦
        PDE.Analysis.differentiableAt_weightedReflectionFun_slice
          (F := fun p : ℝ^2 × ℝ ↦ sol.temperature p.1 p.2) 1 (k + 1)
          fun _ ↦ h.regularity.temperature_differentiableAt_time ht
      streamFunction_spatial_contDiff := fun ht ↦
        PDE.Analysis.contDiff_weightedReflectionFun_of_le (k := 2) 1 (by norm_num) (by omega)
          (by exact_mod_cast (h.regularity.streamFunction_spatial_contDiff ht).contDiffOn) }
  vorticity_equation := by
    intro x t hx ht
    have hω := eventuallyEq_canonical (f := fun y ↦ sol.vorticity y t) k hx
    have hθ := eventuallyEq_canonical (f := fun y ↦ sol.temperature y t) (k + 1) hx
    have htime :
        (fun s ↦ (HalfPlane.canonicalOf k sol).vorticity x s) = fun s ↦ sol.vorticity x s :=
      funext fun s ↦ canonicalOf_vorticity_of_nonneg (le_of_lt hx) s
    have h0 := h.vorticity_equation hx ht
    simp only [PDE.advectiveDerivative] at h0 ⊢
    change deriv (fun s ↦ (HalfPlane.canonicalOf k sol).vorticity x s) t +
        fderiv ℝ (weightedReflectionFun 1 k (fun y ↦ sol.vorticity y t)) x
          (vorticityStreamVelocity (HalfPlane.canonicalOf k sol) x t) =
      (∂[(0 : Fin 2)] (weightedReflectionFun 1 (k + 1) (fun y ↦ sol.temperature y t))) x
    rw [htime, hω.fderiv_eq, vorticityStreamVelocity_canonicalOf hx,
      PDE.partialDeriv_congr_nhds 0 hθ]
    exact h0
  temperature_equation := by
    intro x t hx ht
    have hθ := eventuallyEq_canonical (f := fun y ↦ sol.temperature y t) (k + 1) hx
    have htime :
        (fun s ↦ (HalfPlane.canonicalOf k sol).temperature x s) = fun s ↦ sol.temperature x s :=
      funext fun s ↦ canonicalOf_temperature_of_nonneg (le_of_lt hx) s
    have h0 := h.temperature_equation hx ht
    simp only [PDE.advectiveDerivative] at h0 ⊢
    change deriv (fun s ↦ (HalfPlane.canonicalOf k sol).temperature x s) t +
        fderiv ℝ (weightedReflectionFun 1 (k + 1) (fun y ↦ sol.temperature y t)) x
          (vorticityStreamVelocity (HalfPlane.canonicalOf k sol) x t) = 0
    rw [htime, hθ.fderiv_eq, vorticityStreamVelocity_canonicalOf hx]
    exact h0
  streamFunction_equation := by
    intro x t hx ht
    have hψ := eventuallyEq_canonical (f := fun y ↦ sol.streamFunction y t) (k + 2) hx
    change -PDE.laplacian (weightedReflectionFun 1 (k + 2) (fun y ↦ sol.streamFunction y t)) x =
      (HalfPlane.canonicalOf k sol).vorticity x t
    rw [EuclideanLaplacian.laplacian_congr_nhds hψ,
      canonicalOf_vorticity_of_nonneg (le_of_lt hx)]
    exact h.streamFunction_equation hx ht
  zero_streamFunction_boundary := by
    intro x₁ t ht
    rw [canonicalOf_streamFunction_of_nonneg (by simp)]
    exact h.zero_streamFunction_boundary x₁ ht

/-- The Green potential of a vorticity slice of the representative is that of the original
slice. -/
theorem halfSpaceGreenPotential_canonicalOf (t : ℝ) :
    halfSpaceGreenPotential (fun y ↦ (canonicalOf k sol).vorticity y t) =
      halfSpaceGreenPotential (fun y ↦ sol.vorticity y t) :=
  halfSpaceGreenPotential_congr fun _ hy ↦ canonicalOf_vorticity_of_nonneg (le_of_lt hy) t

/-- **For `k ≥ 1` solutions are preserved by the representative of order `k`.** -/
theorem IsSolutionOn.canonicalOf (h : IsSolutionOn sol I) (hk : 1 ≤ k) (hI : UniqueDiffOn ℝ I) :
    IsSolutionOn (canonicalOf k sol) I where
  classical := h.classical.canonicalOf hk hI
  stream t ht x hx := by
    rw [canonicalOf_streamFunction_of_nonneg hx, halfSpaceGreenPotential_canonicalOf]
    exact h.stream t ht x hx
  support a b hab := by
    obtain ⟨R, hR⟩ := h.support a b hab
    exact ⟨R, fun t ht x hx hxR ↦ by
      rw [canonicalOf_vorticity_of_nonneg hx, canonicalOf_temperature_of_nonneg hx]
      exact hR t ht x hx hxR⟩

/-- For `k ≥ 1` regular solutions of order `k` are preserved by the representative of
order `k`. -/
theorem IsRegularSolutionOfOn.canonicalOf {α : ℝ} (h : IsRegularSolutionOfOn k sol I α)
    (hk : 1 ≤ k) (hI : UniqueDiffOn ℝ I) :
    IsRegularSolutionOfOn k (HalfPlane.canonicalOf k sol) I α := by
  have dω (j : ℕ) (t : ℝ) {x : ℝ^2} (hx : 0 ≤ x 1) :
      iteratedFDerivWithin ℝ j (fun y ↦ (HalfPlane.canonicalOf k sol).vorticity y t) H̄ x =
        iteratedFDerivWithin ℝ j (fun y ↦ sol.vorticity y t) H̄ x := by
    have hEq : EqOn (fun y ↦ (HalfPlane.canonicalOf k sol).vorticity y t)
        (fun y ↦ sol.vorticity y t) H̄ := fun y hy ↦ canonicalOf_vorticity_of_nonneg hy t
    exact iteratedFDerivWithin_congr hEq hx j
  have dθ (j : ℕ) (t : ℝ) {x : ℝ^2} (hx : 0 ≤ x 1) :
      iteratedFDerivWithin ℝ j (fun y ↦ (HalfPlane.canonicalOf k sol).temperature y t) H̄ x =
        iteratedFDerivWithin ℝ j (fun y ↦ sol.temperature y t) H̄ x := by
    have hEq : EqOn (fun y ↦ (HalfPlane.canonicalOf k sol).temperature y t)
        (fun y ↦ sol.temperature y t) H̄ := fun y hy ↦ canonicalOf_temperature_of_nonneg hy t
    exact iteratedFDerivWithin_congr hEq hx j
  exact
    { toIsSolutionOn := h.toIsSolutionOn.canonicalOf hk hI
      holderData := fun a b hab ↦ by
        obtain ⟨R, N, hRN⟩ := h.holderData a b hab
        exact ⟨R, N, fun t ht ↦ (hRN t ht).congr (fun x hx ↦ canonicalOf_vorticity_of_nonneg hx t)
          (fun x hx ↦ canonicalOf_temperature_of_nonneg hx t)⟩
      vorticity_uniform := fun j hj t ht ε hε ↦ by
        obtain ⟨δ, hδ, hδε⟩ := h.vorticity_uniform j hj t ht ε hε
        exact ⟨δ, hδ, fun s hs hst x hx ↦ by
          rw [dω j s hx, dω j t hx]; exact hδε s hs hst x hx⟩
      temperature_uniform := fun j hj t ht ε hε ↦ by
        obtain ⟨δ, hδ, hδε⟩ := h.temperature_uniform j hj t ht ε hε
        exact ⟨δ, hδ, fun s hs hst x hx ↦ by
          rw [dθ j s hx, dθ j t hx]; exact hδε s hs hst x hx⟩ }

/-- **The representative depends only on the values on the closed half-plane.** -/
theorem canonicalOf_eq_of_eqOn {t : ℝ}
    (hω : ∀ x : ℝ^2, 0 ≤ x 1 → sol.vorticity x t = sol'.vorticity x t)
    (hθ : ∀ x : ℝ^2, 0 ≤ x 1 → sol.temperature x t = sol'.temperature x t)
    (hψ : ∀ x : ℝ^2, 0 ≤ x 1 → sol.streamFunction x t = sol'.streamFunction x t) (x : ℝ^2) :
    (canonicalOf k sol).vorticity x t = (canonicalOf k sol').vorticity x t ∧
      (canonicalOf k sol).temperature x t = (canonicalOf k sol').temperature x t ∧
      (canonicalOf k sol).streamFunction x t = (canonicalOf k sol').streamFunction x t := by
  refine ⟨?_, ?_, ?_⟩
  · exact congrFun (PDE.Analysis.weightedReflectionFun_congr 1 k hω) x
  · exact congrFun (PDE.Analysis.weightedReflectionFun_congr 1 (k + 1) hθ) x
  · exact congrFun (PDE.Analysis.weightedReflectionFun_congr 1 (k + 2) hψ) x

/-- Two solutions that agree on the closed half-plane at a time have the same representative of
order `k` at that time. -/
theorem IsSolutionOn.canonicalOf_eq {I' : Set ℝ} (h : IsSolutionOn sol I)
    (h' : IsSolutionOn sol' I') {t : ℝ} (ht : t ∈ I) (ht' : t ∈ I')
    (heq : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t)
    (x : ℝ^2) :
    (HalfPlane.canonicalOf k sol).vorticity x t = (HalfPlane.canonicalOf k sol').vorticity x t ∧
      (HalfPlane.canonicalOf k sol).temperature x t =
        (HalfPlane.canonicalOf k sol').temperature x t ∧
      (HalfPlane.canonicalOf k sol).streamFunction x t =
        (HalfPlane.canonicalOf k sol').streamFunction x t := by
  have hG : halfSpaceGreenPotential (fun y ↦ sol.vorticity y t) =
      halfSpaceGreenPotential (fun y ↦ sol'.vorticity y t) :=
    halfSpaceGreenPotential_congr fun y hy ↦ (heq y (le_of_lt hy)).1
  refine canonicalOf_eq_of_eqOn (fun y hy ↦ (heq y hy).1) (fun y hy ↦ (heq y hy).2)
    (fun y hy ↦ ?_) x
  rw [h.stream t ht y hy, h'.stream t ht' y hy, hG]

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

/-- For slices of order `k ≥ 1`, the derivatives of order `j ≤ k` of the vorticity slice of the
representative are bounded by `reflectionBound k j · N`. -/
theorem norm_iteratedFDeriv_canonicalOf_vorticity_le
    (h : IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N)
    (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) (x : ℝ^2) :
    ‖iteratedFDeriv ℝ j (fun y ↦ (canonicalOf k sol).vorticity y t) x‖ ≤
      PDE.Analysis.reflectionBound k j * N :=
  PDE.Analysis.norm_iteratedFDeriv_weightedReflectionFun_le 1 hk h.vorticity_contDiffOn hj
    (h.norm_vorticity_le j hj) x

/-- For slices of order `k`, the derivatives of order `j ≤ k + 1` of the temperature slice of the
representative are bounded by `reflectionBound (k + 1) j · N`. -/
theorem norm_iteratedFDeriv_canonicalOf_temperature_le
    (h : IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N)
    {j : ℕ} (hj : j ≤ k + 1) (x : ℝ^2) :
    ‖iteratedFDeriv ℝ j (fun y ↦ (canonicalOf k sol).temperature y t) x‖ ≤
      PDE.Analysis.reflectionBound (k + 1) j * N :=
  PDE.Analysis.norm_iteratedFDeriv_weightedReflectionFun_le 1 (k := k + 1) (by omega)
    h.temperature_contDiffOn hj (h.norm_temperature_le j hj) x

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
    (h : IsRegularSolutionOfOn k sol I α) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) :
    ContinuousOn
      (fun p : ℝ × ℝ^2 ↦
        iteratedFDeriv ℝ j (fun x ↦ (HalfPlane.canonicalOf k sol).vorticity x p.1) p.2)
      (I ×ˢ univ) :=
  PDE.Analysis.continuousOn_iteratedFDeriv_weightedReflectionFun 1 hk
    (F := fun t y ↦ sol.vorticity y t)
    (fun _ ht ↦ (h.exists_isHolderDataOf ht).choose_spec.choose_spec.vorticity_contDiffOn) hj
    (h.vorticity_uniform j hj)

/-- **Continuous temperature jets.** For a regular solution of order `k`, the derivatives of
order `j ≤ k + 1` of the temperature slices of the representative are jointly continuous on
`I × ℝ²`. -/
theorem continuousOn_iteratedFDeriv_canonicalOf_temperature
    (h : IsRegularSolutionOfOn k sol I α) {j : ℕ} (hj : j ≤ k + 1) :
    ContinuousOn
      (fun p : ℝ × ℝ^2 ↦
        iteratedFDeriv ℝ j (fun x ↦ (HalfPlane.canonicalOf k sol).temperature x p.1) p.2)
      (I ×ˢ univ) :=
  PDE.Analysis.continuousOn_iteratedFDeriv_weightedReflectionFun 1 (k := k + 1) (by omega)
    (F := fun t y ↦ sol.temperature y t)
    (fun _ ht ↦ (h.exists_isHolderDataOf ht).choose_spec.choose_spec.temperature_contDiffOn) hj
    (h.temperature_uniform j hj)

end IsRegularSolutionOfOn

/-! ### Parity -/

/-- **Parity of the vorticity representative.** If the vorticity slice is odd in `x₀` on the
closed half-plane, the vorticity slice of the representative is odd in `x₀` everywhere. -/
theorem canonicalOf_vorticity_tangentialReflection {t : ℝ}
    (hω : ∀ y : ℝ^2, 0 ≤ y 1 → sol.vorticity (tangentialReflection y) t = -sol.vorticity y t)
    (x : ℝ^2) :
    (canonicalOf k sol).vorticity (tangentialReflection x) t =
      -(canonicalOf k sol).vorticity x t := by
  have h := PDE.Analysis.weightedReflectionFun_comp_coordinateReflection 1 (k := k)
    (f := fun y ↦ sol.vorticity y t) (l := 0) (by decide) (ε := -1)
    (fun y hy ↦ by rw [neg_one_mul]; exact hω y hy) x
  rw [neg_one_mul] at h
  exact h

/-- **Parity of the temperature representative.** If the temperature slice is even in `x₀` on
the closed half-plane, the temperature slice of the representative is even in `x₀`
everywhere. -/
theorem canonicalOf_temperature_tangentialReflection {t : ℝ}
    (hθ : ∀ y : ℝ^2, 0 ≤ y 1 → sol.temperature (tangentialReflection y) t = sol.temperature y t)
    (x : ℝ^2) :
    (canonicalOf k sol).temperature (tangentialReflection x) t =
      (canonicalOf k sol).temperature x t := by
  have h := PDE.Analysis.weightedReflectionFun_comp_coordinateReflection 1 (k := k + 1)
    (f := fun y ↦ sol.temperature y t) (l := 0) (by decide) (ε := 1)
    (fun y hy ↦ by rw [one_mul]; exact hθ y hy) x
  rw [one_mul] at h
  exact h

/-- **Parity of the stream function representative.** If the vorticity slice of a solution is
odd in `x₀` on the closed half-plane, the stream function slice of the representative is odd in
`x₀` everywhere: on the closed half-plane the stream function is the Green potential, which
commutes with the reflection. -/
theorem IsSolutionOn.canonicalOf_streamFunction_tangentialReflection (h : IsSolutionOn sol I)
    {t : ℝ} (ht : t ∈ I)
    (hω : ∀ y : ℝ^2, 0 ≤ y 1 → sol.vorticity (tangentialReflection y) t = -sol.vorticity y t)
    (x : ℝ^2) :
    (HalfPlane.canonicalOf k sol).streamFunction (tangentialReflection x) t =
      -(HalfPlane.canonicalOf k sol).streamFunction x t := by
  have hψ (y : ℝ^2) (hy : 0 ≤ y 1) :
      sol.streamFunction (tangentialReflection y) t = -sol.streamFunction y t := by
    have hRy : 0 ≤ tangentialReflection y 1 := by rwa [tangentialReflection_apply_one]
    rw [h.stream t ht _ hRy, h.stream t ht y hy,
      ← halfSpaceGreenPotential_comp_tangentialReflection, ← halfSpaceGreenPotential_neg]
    exact congrFun (halfSpaceGreenPotential_congr fun z hz ↦ hω z (le_of_lt hz)) y
  have h := PDE.Analysis.weightedReflectionFun_comp_coordinateReflection 1 (k := k + 2)
    (f := fun y ↦ sol.streamFunction y t) (l := 0) (by decide) (ε := -1)
    (fun y hy ↦ by rw [neg_one_mul]; exact hψ y hy) x
  rw [neg_one_mul] at h
  exact h

end Boussinesq.HalfPlane
