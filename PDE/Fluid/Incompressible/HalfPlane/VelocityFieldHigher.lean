/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityComparison
public import PDE.Analysis.Calculus.SmoothFamily
public import PDE.Analysis.ODE.Flow.IntegralEstimates
public import PDE.Analysis.Calculus.HolderLimitHigher
import PDE.Analysis.Calculus.FaaDiBrunoBounds

/-!
# Velocity fields of `C^{k,α}` vorticity histories

A vorticity history `ω` on the times `[a, b]` is `C^{k,α}` (`IsCkVorticityHistory k`) if at every
time it is `C^k` within the closed half-plane `H̄`, vanishes there outside a common disc, its
derivatives within `H̄` of order at most `k` are bounded by a common `N`, the `k`-th is `α`-Hölder
with constant `N`, and every derivative of order at most `k` is continuous in time uniformly on
`H̄`. For `k ≥ 1` such a history is a `C¹` history (`IsCkVorticityHistory.toIsC1VorticityHistory`),
and conversely a `C¹` history with a Hölder gradient is a history of order one
(`IsC1VorticityHistory.toIsCkVorticityHistory`). Uniform `C^{k,α}` bounds pass to pointwise limits
that are Cauchy uniformly on `[a, b] × H̄` (`IsCkVorticityHistory.of_tendsto`).

Its velocities are `C^{k+1}` within `H̄` with the `C^{k+1,α}` bounds of the half-plane Biot-Savart
law, and their derivatives of order at most `k + 1` are continuous in time uniformly on `H̄`: below
the top order by the size bounds of the velocity of `ω s - ω t`, at the top order by the homogeneous
Kato bound, the Hölder constant of the top derivative of `ω s - ω t` being at most `2N`. The
extension `extendedVelocity (k + 1) (ω t)` by the weighted reflection of order `k + 1` is therefore
a smooth family of order `k + 1` in the sense of `PDE.Analysis.IsSmoothFamilyOn`
(`IsCkVorticityHistory.isSmoothFamilyOn_extendedVelocity`), a `C¹` field tangent to the boundary,
and its derivatives on `H̄` are those of the velocity within `H̄`.

Extensions of different orders have the same flow and the same first variation on `H̄`, since
the flows preserve `H̄` and the fields and their derivatives agree there
(`flowOn_extendedVelocity_eq`, `variationOn_extendedVelocity_eq`); so the derivatives within `H̄`
of the flow maps do not depend on the order (`iteratedFDerivWithin_flowOn_extendedVelocity_eq`).

## Main definitions

* `IsCkVorticityHistory k ω a b α R N`.

## Main results

* `IsCkVorticityHistory.toIsVorticityHistory`, `toIsC1VorticityHistory`, `mono`, `of_le`,
  `of_eq_zero`, `IsC1VorticityHistory.toIsCkVorticityHistory`.
* `IsCkVorticityHistory.of_tendsto`: limits of `C^{k,α}` histories.
* `IsCkVorticityHistory.exists_norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le`: continuity in
  time of the derivatives of the velocity, uniformly on `H̄`.
* `IsCkVorticityHistory.isSmoothFamilyOn_extendedVelocity`,
  `IsCkVorticityHistory.isC1FieldOn_extendedVelocity`.
* `iteratedFDeriv_extendedVelocity_of_nonneg`,
  `IsCkVorticityHistory.norm_iteratedFDeriv_extendedVelocity_le`,
  `IsCkVorticityHistory.norm_iteratedFDeriv_extendedVelocity_sub_le`: the bounds on `H̄`.
* `flowOn_extendedVelocity_eq`, `variationOn_extendedVelocity_eq`,
  `iteratedFDerivWithin_flowOn_extendedVelocity_eq`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology NNReal
open SobolevSpace SobolevSpace.GraphSpace.HigherOrderReflection

namespace IncompressibleFlow

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The first iterated derivatives within the closed half-plane of two functions at a point of it
differ by their derivatives within it. -/
theorem norm_iteratedFDerivWithin_one_sub_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f g : ℝ^2 → F) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖iteratedFDerivWithin ℝ 1 f H̄ x - iteratedFDerivWithin ℝ 1 g H̄ x‖ =
      ‖fderivWithin ℝ f H̄ x - fderivWithin ℝ g H̄ x‖ := by
  rw [PDE.Analysis.iteratedFDerivWithin_one_eq (uniqueDiffOn_closedUpper x hx),
    PDE.Analysis.iteratedFDerivWithin_one_eq (uniqueDiffOn_closedUpper x hx), ← map_sub,
    LinearIsometryEquiv.norm_map]

/-! ### Components and the extension -/

/-- The derivatives within the closed half-plane of a component of two maps differ by at most
the difference of the derivatives of the maps. -/
theorem norm_iteratedFDerivWithin_apply_sub_apply_le {u w : ℝ^2 → ℝ^2} {m : ℕ}
    (hu : ContDiffOn ℝ m u H̄) (hw : ContDiffOn ℝ m w H̄) (c : Fin 2) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖iteratedFDerivWithin ℝ m (fun z ↦ u z c) H̄ y -
        iteratedFDerivWithin ℝ m (fun z ↦ w z c) H̄ y‖ ≤
      ‖iteratedFDerivWithin ℝ m u H̄ y - iteratedFDerivWithin ℝ m w H̄ y‖ := by
  set P := (EuclideanSpace.proj c : ℝ^2 →L[ℝ] ℝ)
  change ‖iteratedFDerivWithin ℝ m (P ∘ u) H̄ y - iteratedFDerivWithin ℝ m (P ∘ w) H̄ y‖ ≤ _
  rw [P.iteratedFDerivWithin_comp_left (hu y hy) uniqueDiffOn_closedUpper hy le_rfl,
    P.iteratedFDerivWithin_comp_left (hw y hy) uniqueDiffOn_closedUpper hy le_rfl]
  have e : P.compContinuousMultilinearMap (iteratedFDerivWithin ℝ m u H̄ y) -
      P.compContinuousMultilinearMap (iteratedFDerivWithin ℝ m w H̄ y) =
      P.compContinuousMultilinearMap (iteratedFDerivWithin ℝ m u H̄ y -
        iteratedFDerivWithin ℝ m w H̄ y) := by
    ext v; simp
  rw [e]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) ?_)
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
    simpa [P] using PiLp.norm_apply_le v c

/-- The extended velocity as the sum of its two components placed in the coordinate
directions. -/
theorem extendedVelocity_eq_sum (K : ℕ) (f : ℝ^2 → ℝ) :
    extendedVelocity K f = fun x ↦
      ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
          (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity f y 0) x) +
        ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
          (weightedReflectionFun 1 K (fun y ↦ halfPlaneVelocity f y 1) x) := by
  funext x
  ext c
  fin_cases c <;> simp [extendedVelocity_apply]

/-- On the closed half-plane the iterated derivatives of the extended velocity are those of the
velocity within the closed half-plane. -/
theorem iteratedFDeriv_extendedVelocity_of_nonneg {f : ℝ^2 → ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hu : ContDiffOn ℝ K (halfPlaneVelocity f) H̄) {m : ℕ} (hm : m ≤ K) {x : ℝ^2}
    (hx : 0 ≤ x 1) :
    iteratedFDeriv ℝ m (extendedVelocity K f) x =
      iteratedFDerivWithin ℝ m (halfPlaneVelocity f) H̄ x := by
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_closedUpper
    (((contDiff_extendedVelocity hK hu).of_le (by exact_mod_cast hm)).contDiffAt) hx]
  have h : EqOn (extendedVelocity K f) (halfPlaneVelocity f) H̄ := fun y hy ↦
    extendedVelocity_of_nonneg K f hy
  exact iteratedFDerivWithin_congr h hx m

/-! ### `C^{k,α}` histories -/

/-- A `C^{k,α}` vorticity history on the times `[a, b]`: at every time it is `C^k` within the
closed half-plane `H̄` and vanishes there outside the disc of radius `R`, its derivatives within
`H̄` of order at most `k` are bounded by `N`, the `k`-th is `α`-Hölder on `H̄` with constant `N`,
and every derivative of order at most `k` is continuous in time uniformly on `H̄`. -/
structure IsCkVorticityHistory (k : ℕ) (ω : ℝ → ℝ^2 → ℝ) (a b α R N : ℝ) : Prop where
  /-- `C^k` regularity within the closed half-plane. -/
  contDiffOn : ∀ t ∈ Icc a b, ContDiffOn ℝ k (ω t) H̄
  /-- A common support disc. -/
  eq_zero : ∀ t ∈ Icc a b, ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → ω t y = 0
  /-- A common bound of the derivatives of order at most `k`. -/
  norm_le : ∀ t ∈ Icc a b, ∀ j ≤ k, ∀ y : ℝ^2, 0 ≤ y 1 →
    ‖iteratedFDerivWithin ℝ j (ω t) H̄ y‖ ≤ N
  /-- A common Hölder bound of the `k`-th derivative. -/
  holder : ∀ t ∈ Icc a b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
    ‖iteratedFDerivWithin ℝ k (ω t) H̄ y - iteratedFDerivWithin ℝ k (ω t) H̄ z‖ ≤
      N * ‖y - z‖ ^ α
  /-- Continuity in time of the derivatives, uniformly on the closed half-plane. -/
  uniform : ∀ j ≤ k, ∀ t ∈ Icc a b, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ →
    ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖iteratedFDerivWithin ℝ j (ω s) H̄ y - iteratedFDerivWithin ℝ j (ω t) H̄ y‖ ≤ ε

namespace IsCkVorticityHistory

variable {k : ℕ} {ω : ℝ → ℝ^2 → ℝ} {a b α R N : ℝ}

/-- At every time a `C^{k,α}` history is continuous on the closed half-plane. -/
theorem continuousOn (hω : IsCkVorticityHistory k ω a b α R N) {t : ℝ} (ht : t ∈ Icc a b) :
    ContinuousOn (ω t) H̄ :=
  (hω.contDiffOn t ht).continuousOn

/-- At every time a `C^{k,α}` history is bounded by `N` on the closed half-plane. -/
theorem abs_le (hω : IsCkVorticityHistory k ω a b α R N) {t : ℝ} (ht : t ∈ Icc a b) {y : ℝ^2}
    (hy : 0 ≤ y 1) : |ω t y| ≤ N := by
  have h := hω.norm_le t ht 0 (Nat.zero_le k) y hy
  rwa [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] at h

/-- The common bound of a `C^{k,α}` history on a nonempty time interval is nonnegative. -/
theorem nonneg (hω : IsCkVorticityHistory k ω a b α R N) {t : ℝ} (ht : t ∈ Icc a b) :
    0 ≤ N :=
  (abs_nonneg _).trans (hω.abs_le ht (y := 0) (by simp))

/-- A `C^{k,α}` history vanishes on `H̄` outside the disc of radius `max R 0`. -/
theorem eq_zero_max (hω : IsCkVorticityHistory k ω a b α R N) {t : ℝ} (ht : t ∈ Icc a b)
    (y : ℝ^2) (hy : 0 ≤ y 1) (hyR : max R 0 < ‖y‖) : ω t y = 0 :=
  hω.eq_zero t ht y hy ((le_max_left R 0).trans_lt hyR)

/-- Every derivative of order at most `k` of a `C^{k,α}` history is `α`-Hölder on the closed
half-plane with constant `2N`, for `0 ≤ α ≤ 1`. -/
theorem norm_iteratedFDerivWithin_sub_le (hω : IsCkVorticityHistory k ω a b α R N)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {t : ℝ} (ht : t ∈ Icc a b) {j : ℕ} (hj : j ≤ k) {y z : ℝ^2}
    (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    ‖iteratedFDerivWithin ℝ j (ω t) H̄ y - iteratedFDerivWithin ℝ j (ω t) H̄ z‖ ≤
      2 * N * ‖y - z‖ ^ α :=
  PDE.Analysis.norm_iteratedFDerivWithin_sub_le_two_mul (hω.contDiffOn t ht) (hω.norm_le t ht)
    (hω.holder t ht)
    hα0 hα1 hj hy hz

/-- A `C^{k,α}` history is a `C^{j,α}` history with constant `2N` for every `j ≤ k`. -/
theorem mono (hω : IsCkVorticityHistory k ω a b α R N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {j : ℕ}
    (hj : j ≤ k) : IsCkVorticityHistory j ω a b α R (2 * N) where
  contDiffOn t ht := (hω.contDiffOn t ht).of_le (by exact_mod_cast hj)
  eq_zero := hω.eq_zero
  norm_le t ht i hi y hy := (hω.norm_le t ht i (hi.trans hj) y hy).trans (by
    linarith [hω.nonneg ht])
  holder t ht y z hy hz := hω.norm_iteratedFDerivWithin_sub_le hα0 hα1 ht hj hy hz
  uniform i hi := hω.uniform i (hi.trans hj)

/-- For `k ≥ 1` a `C^{k,α}` history is a vorticity history with bound `N` and Hölder constant
`2N`. -/
theorem toIsVorticityHistory (hω : IsCkVorticityHistory k ω a b α R N) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : IsVorticityHistory ω a b α R N (2 * N) where
  continuousOn _ ht := hω.continuousOn ht
  eq_zero := hω.eq_zero
  abs_le _ ht _ hy := hω.abs_le ht hy
  holder t ht y z hy hz := by
    have h := hω.norm_iteratedFDerivWithin_sub_le hα0 hα1 ht (Nat.zero_le k) hy hz
    rwa [PDE.Analysis.norm_iteratedFDerivWithin_zero_sub, Real.norm_eq_abs] at h
  uniform t ht ε hε := by
    obtain ⟨δ, hδ, h⟩ := hω.uniform 0 (Nat.zero_le k) t ht ε hε
    refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
    have h' := h s hs hst y hy
    rwa [PDE.Analysis.norm_iteratedFDerivWithin_zero_sub_apply, Real.norm_eq_abs] at h'

/-- For `k ≥ 1` a `C^{k,α}` history is a `C¹` history with gradient bound `N` and Hölder
constants `2N`. -/
theorem toIsC1VorticityHistory (hω : IsCkVorticityHistory k ω a b α R N) (hk : 1 ≤ k)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : IsC1VorticityHistory ω a b α R N (2 * N) N (2 * N) where
  toIsVorticityHistory := hω.toIsVorticityHistory hα0 hα1
  contDiffOn t ht := (hω.contDiffOn t ht).of_le (by exact_mod_cast hk)
  norm_fderivWithin_le t ht y hy := by
    have h := hω.norm_le t ht 1 hk y hy
    rwa [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper y hy)] at h
  holder_fderivWithin t ht y z hy hz := by
    have h := hω.norm_iteratedFDerivWithin_sub_le hα0 hα1 ht hk hy hz
    rwa [norm_iteratedFDerivWithin_one_sub _ hy hz] at h
  uniform_fderivWithin t ht ε hε := by
    obtain ⟨δ, hδ, h⟩ := hω.uniform 1 hk t ht ε hε
    refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
    have h' := h s hs hst y hy
    rwa [norm_iteratedFDerivWithin_one_sub_apply _ _ hy] at h'

/-- At every time the velocity of a `C^{k,α}` history is `C^{k+1}` within the closed
half-plane, for `0 < α < 1`. -/
theorem contDiffOn_halfPlaneVelocity (hω : IsCkVorticityHistory k ω a b α R N) (hα : 0 < α)
    (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (halfPlaneVelocity (ω t)) H̄ := by
  have h := contDiffOn_succ_halfPlaneVelocity hα hα1 (hω.contDiffOn t ht) (hω.eq_zero t ht)
    (hω.holder t ht)
  exact_mod_cast h

/-- The difference of two times of a `C^{k,α}` history: it is `C^k` within the closed half-plane,
vanishes there outside the disc of radius `max R 0`, its derivatives are the differences of the
derivatives, and its `k`-th derivative is `α`-Hölder with constant `2N`. -/
theorem sub_data (hω : IsCkVorticityHistory k ω a b α R N) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) :
    ContDiffOn ℝ k (ω s - ω t) H̄ ∧
      (∀ y : ℝ^2, 0 ≤ y 1 → max R 0 < ‖y‖ → (ω s - ω t) y = 0) ∧
      (∀ j ≤ k, ∀ y : ℝ^2, 0 ≤ y 1 → iteratedFDerivWithin ℝ j (ω s - ω t) H̄ y =
        iteratedFDerivWithin ℝ j (ω s) H̄ y - iteratedFDerivWithin ℝ j (ω t) H̄ y) ∧
      ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
        ‖iteratedFDerivWithin ℝ k (ω s - ω t) H̄ y - iteratedFDerivWithin ℝ k (ω s - ω t) H̄ z‖ ≤
          2 * N * ‖y - z‖ ^ α := by
  have hd (j : ℕ) (hj : j ≤ k) (y : ℝ^2) (hy : 0 ≤ y 1) :
      iteratedFDerivWithin ℝ j (ω s - ω t) H̄ y =
        iteratedFDerivWithin ℝ j (ω s) H̄ y - iteratedFDerivWithin ℝ j (ω t) H̄ y :=
    iteratedFDerivWithin_sub_apply (((hω.contDiffOn s hs) y hy).of_le (by exact_mod_cast hj))
      (((hω.contDiffOn t ht) y hy).of_le (by exact_mod_cast hj)) uniqueDiffOn_closedUpper hy
  refine ⟨(hω.contDiffOn s hs).sub (hω.contDiffOn t ht), fun y hy hyR ↦ ?_, hd,
    fun y z hy hz ↦ ?_⟩
  · simp [hω.eq_zero_max hs y hy hyR, hω.eq_zero_max ht y hy hyR]
  · rw [hd k le_rfl y hy, hd k le_rfl z hz]
    have h1 := hω.holder s hs y z hy hz
    have h2 := hω.holder t ht y z hy hz
    calc ‖iteratedFDerivWithin ℝ k (ω s) H̄ y - iteratedFDerivWithin ℝ k (ω t) H̄ y -
          (iteratedFDerivWithin ℝ k (ω s) H̄ z - iteratedFDerivWithin ℝ k (ω t) H̄ z)‖
        = ‖(iteratedFDerivWithin ℝ k (ω s) H̄ y - iteratedFDerivWithin ℝ k (ω s) H̄ z) -
            (iteratedFDerivWithin ℝ k (ω t) H̄ y - iteratedFDerivWithin ℝ k (ω t) H̄ z)‖ := by
          congr 1; abel
      _ ≤ ‖iteratedFDerivWithin ℝ k (ω s) H̄ y - iteratedFDerivWithin ℝ k (ω s) H̄ z‖ +
            ‖iteratedFDerivWithin ℝ k (ω t) H̄ y - iteratedFDerivWithin ℝ k (ω t) H̄ z‖ :=
          norm_sub_le _ _
      _ ≤ 2 * N * ‖y - z‖ ^ α := by linarith

/-- **Continuity in time of the derivatives of the velocity**, uniformly on the closed
half-plane: for `k ≥ 1`, `0 < α < 1` and every order `j ≤ k + 1`, the derivatives of order `j`
within `H̄` of the velocities of `ω s` and `ω t` are uniformly close for `s` close to `t`. Below the
top order this is the size bound of the velocity of `ω s - ω t`, at the top order the homogeneous
Kato bound. -/
theorem exists_norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le
    (hω : IsCkVorticityHistory k ω a b α R N) (hα : 0 < α) (hα1 : α < 1) {j : ℕ}
    (hj : j ≤ k + 1) {t : ℝ} (ht : t ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc a b, |s - t| < δ → ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖iteratedFDerivWithin ℝ j (halfPlaneVelocity (ω s)) H̄ y -
        iteratedFDerivWithin ℝ j (halfPlaneVelocity (ω t)) H̄ y‖ ≤ ε := by
  set R₀ := max R 0
  have hR₀ : 0 ≤ R₀ := le_max_right R 0
  have hN := hω.nonneg ht
  have hpi := Real.pi_pos
  -- the derivatives of the velocity of the difference are the differences
  have hred (s : ℝ) (hs : s ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
      iteratedFDerivWithin ℝ j (halfPlaneVelocity (ω s)) H̄ y -
          iteratedFDerivWithin ℝ j (halfPlaneVelocity (ω t)) H̄ y =
        iteratedFDerivWithin ℝ j (halfPlaneVelocity (ω s - ω t)) H̄ y :=
    (iteratedFDerivWithin_halfPlaneVelocity_sub (hω.continuousOn hs) (hω.eq_zero s hs)
      (hω.continuousOn ht) (hω.eq_zero t ht)
      ((hω.contDiffOn_halfPlaneVelocity hα hα1 hs).of_le (by exact_mod_cast hj))
      ((hω.contDiffOn_halfPlaneVelocity hα hα1 ht).of_le (by exact_mod_cast hj)) hy).symm
  -- the mass of a derivative of the difference
  have hmass (s : ℝ) (hs : s ∈ Icc a b) {i : ℕ} (hi : i ≤ k) {η : ℝ}
      (hη : ∀ y : ℝ^2, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ i (ω s - ω t) H̄ y‖ ≤ η) :
      ∫ y in HalfSpace.upper 2, ‖iteratedFDerivWithin ℝ i (ω s - ω t) H̄ y‖ ≤
        Real.pi * R₀ ^ 2 * η := by
    obtain ⟨hgc, hgR, -, -⟩ := hω.sub_data hs ht
    exact setIntegral_upper_le hR₀
      ((hgc.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi)
        uniqueDiffOn_closedUpper).norm)
      (fun y hy hyR ↦ by rw [iteratedFDerivWithin_eq_zero_of_eq_zero hgR i hy hyR, norm_zero])
      hη fun y ↦ norm_nonneg _
  -- the derivatives of the difference are small when the times are close
  have hsmall (i : ℕ) (hi : i ≤ k) {η : ℝ} (hη : 0 < η) : ∃ δ > 0, ∀ s ∈ Icc a b,
      |s - t| < δ → ∀ y : ℝ^2, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ i (ω s - ω t) H̄ y‖ ≤ η := by
    obtain ⟨δ, hδ, h⟩ := hω.uniform i hi t ht η hη
    exact ⟨δ, hδ, fun s hs hst y hy ↦ by
      rw [(hω.sub_data hs ht).2.2.1 i hi y hy]; exact h s hs hst y hy⟩
  rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
  · cases j with
    | zero =>
      have hpos : 0 < 1 + R₀ ^ 2 := by positivity
      obtain ⟨δ, hδ, h⟩ := hsmall 0 (Nat.zero_le k) (div_pos hε hpos)
      refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
      obtain ⟨hgc, hgR, -, -⟩ := hω.sub_data hs ht
      rw [hred s hs hy, norm_iteratedFDerivWithin_zero]
      have hB : ∀ z : ℝ^2, 0 ≤ z 1 → |(ω s - ω t) z| ≤ ε / (1 + R₀ ^ 2) := fun z hz ↦ by
        simpa only [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] using h s hs hst z hz
      refine (norm_halfPlaneVelocity_le_of_abs_le hgc.continuousOn hgR hR₀ hB y).trans ?_
      rw [mul_div_cancel₀ _ hpos.ne']
    | succ i =>
      have hik : i + 1 ≤ k := by omega
      have hpos : 0 < 2 + R₀ ^ 2 + k := by positivity
      set η := ε / (2 + R₀ ^ 2 + k)
      have hη : 0 < η := div_pos hε hpos
      obtain ⟨δ₁, hδ₁, h₁⟩ := hsmall (i + 1) hik hη
      obtain ⟨δ₂, hδ₂, h₂⟩ := hsmall i (by omega) hη
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs hst y hy ↦ ?_⟩
      obtain ⟨hgc, hgR, -, -⟩ := hω.sub_data hs ht
      rw [hred s hs hy]
      have hB₁ := h₁ s hs (hst.trans_le (min_le_left _ _))
      have hB₂ := h₂ s hs (hst.trans_le (min_le_right _ _))
      have h := norm_iteratedFDerivWithin_halfPlaneVelocity_le i
        (hgc.of_le (by exact_mod_cast hik)) hgR hB₁ (hmass s hs hik hB₁) hB₂ y
      refine h.trans ?_
      have he : η * (2 + R₀ ^ 2 + k) = ε := div_mul_cancel₀ ε hpos.ne'
      have hk' : ((i : ℝ) + 1) * η ≤ k * η :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hik) hη.le
      rw [show Real.pi * R₀ ^ 2 * η / Real.pi = R₀ ^ 2 * η by field_simp]
      linarith
  · obtain rfl : j = k + 1 := by omega
    have hcont : Continuous fun η ↦ katoModulus α R₀ (2 * N) η + k * η :=
      (continuous_katoModulus α R₀ (by positivity : (0 : ℝ) ≤ 2 * N)).add
        (continuous_const.mul continuous_id)
    obtain ⟨η, hη, hη1, hηε⟩ := exists_pos_le_one_of_continuousAt hcont.continuousAt
      (by simp) hε
    obtain ⟨δ, hδ, h⟩ := hsmall k le_rfl hη
    refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
    obtain ⟨hgc, hgR, -, hgM⟩ := hω.sub_data hs ht
    rw [hred s hs hy]
    have hB := h s hs hst
    refine (norm_iteratedFDerivWithin_halfPlaneVelocity_le_kato_homogeneous hα hα1 hgc hgR
      hgM hB hη (hmass s hs le_rfl hB) hy).trans (le_trans ?_ hηε)
    have hlog := PDE.Analysis.mul_one_add_log_le_osgoodModulus hη.le hη1
      (by positivity : (0 : ℝ) ≤ 2 * N)
    rw [mul_one] at hlog
    have h50 : 50 * η / α * (1 + Real.log (2 + 2 * N / η)) =
        50 / α * (η * (1 + Real.log (2 + 2 * N / η))) := by ring
    unfold katoModulus
    rw [h50]
    gcongr

/-- **The extended velocities of a `C^{k,α}` history are a smooth family of order `k + 1`.** For
`0 < α < 1`, the fields `extendedVelocity (k + 1) (ω t)`, `t ∈ [a, b]`, are `C^{k+1}` and their
derivatives of order at most `k + 1` are jointly continuous on `[a, b] × ℝ²`. -/
theorem isSmoothFamilyOn_extendedVelocity (hω : IsCkVorticityHistory k ω a b α R N)
    (hα : 0 < α) (hα1 : α < 1) :
    PDE.Analysis.IsSmoothFamilyOn (k + 1) (fun t ↦ extendedVelocity (k + 1) (ω t)) (Icc a b) := by
  have hc (c : Fin 2) : PDE.Analysis.IsSmoothFamilyOn (k + 1)
      (fun t x ↦ weightedReflectionFun 1 (k + 1) (fun y ↦ halfPlaneVelocity (ω t) y c) x)
      (Icc a b) := by
    refine ⟨fun t ht ↦ PDE.Analysis.contDiff_weightedReflectionFun 1 (by omega)
      (contDiffOn_halfPlaneVelocity_apply (hω.contDiffOn_halfPlaneVelocity hα hα1 ht) c),
      fun j hj ↦ ?_⟩
    refine PDE.Analysis.continuousOn_iteratedFDeriv_weightedReflectionFun 1 (by omega)
      (F := fun t y ↦ halfPlaneVelocity (ω t) y c)
      (fun t ht ↦ contDiffOn_halfPlaneVelocity_apply (hω.contDiffOn_halfPlaneVelocity hα hα1 ht) c)
      hj (fun t ht ε hε ↦ ?_)
    obtain ⟨δ, hδ, h⟩ :=
      hω.exists_norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le hα hα1 hj ht hε
    refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
    exact (norm_iteratedFDerivWithin_apply_sub_apply_le
      ((hω.contDiffOn_halfPlaneVelocity hα hα1 hs).of_le (by exact_mod_cast hj))
      ((hω.contDiffOn_halfPlaneVelocity hα hα1 ht).of_le (by exact_mod_cast hj)) c hy).trans
        (h s hs hst y hy)
  refine ((((hc 0).clm_comp
      (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))).add
    ((hc 1).clm_comp
      (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))))).congr
    fun t _ ↦ ?_
  exact (extendedVelocity_eq_sum (k + 1) (ω t)).symm

/-- For `0 < α < 1` the extended velocities of order `k + 1` of a `C^{k,α}` history form a `C¹`
field on `[a, b] × ℝ²` with derivatives bounded by
`2 reflectionBound (k + 1) 1 · katoBound α R₀ N (2N)`, `R₀ = max R 0`. -/
theorem isC1FieldOn_extendedVelocity (hω : IsCkVorticityHistory k ω a b α R N) (hα : 0 < α)
    (hα1 : α < 1) :
    PDE.Analysis.ODE.IsC1FieldOn (fun t ↦ extendedVelocity (k + 1) (ω t))
      (fun t x ↦ fderiv ℝ (extendedVelocity (k + 1) (ω t)) x) a b
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound (k + 1) 1 *
        katoBound α (max R 0) N (2 * N))) :=
  (hω.toIsVorticityHistory hα.le hα1.le).isC1FieldOn_extendedVelocity hα hα1 (by omega)
    fun _ ht ↦ hω.contDiffOn_halfPlaneVelocity hα hα1 ht

/-- The extended velocity of a `C^{k,α}` history is tangent to the boundary. -/
theorem extendedVelocity_normal_eq_zero (hω : IsCkVorticityHistory k ω a b α R N) (K : ℕ)
    {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^2} (hx : x 1 = 0) : extendedVelocity K (ω t) x 1 = 0 :=
  IncompressibleFlow.extendedVelocity_normal_eq_zero K (hω.continuousOn ht) (hω.eq_zero t ht) hx

/-- **The `C^{k+1}` bounds of the velocity on the closed half-plane.** For `0 < α < 1` and
`j ≤ k + 1`, the `j`-th derivative of the extended velocity at a point of `H̄`, which is the
`j`-th derivative of the velocity within `H̄`, is at most `(200/α + 40π(1 + R₀²) + k + 33) N`,
`R₀ = max R 0`. -/
theorem norm_iteratedFDeriv_extendedVelocity_le (hω : IsCkVorticityHistory k ω a b α R N)
    (hα : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc a b) {j : ℕ} (hj : j ≤ k + 1) {y : ℝ^2}
    (hy : 0 ≤ y 1) :
    ‖iteratedFDeriv ℝ j (extendedVelocity (k + 1) (ω t)) y‖ ≤
      (200 / α + 40 * Real.pi * (1 + max R 0 ^ 2) + k + 33) * N := by
  rw [iteratedFDeriv_extendedVelocity_of_nonneg (by omega)
    (hω.contDiffOn_halfPlaneVelocity hα hα1 ht) hj hy]
  exact norm_iteratedFDerivWithin_halfPlaneVelocity_le_mul hα hα1 (le_max_right R 0)
    (hω.contDiffOn t ht) (hω.eq_zero_max ht) (fun i hi z hz ↦ hω.norm_le t ht i hi z hz)
    (hω.holder t ht) hj hy

/-- **The top Hölder bound of the velocity on the closed half-plane.** For `0 < α < 1` the
`(k + 1)`-th derivatives of the extended velocity at two points of `H̄` differ by at most
`(844/(α(1-α)) + k) N |y - z|^α`. -/
theorem norm_iteratedFDeriv_extendedVelocity_sub_le (hω : IsCkVorticityHistory k ω a b α R N)
    (hα : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc a b) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) :
    ‖iteratedFDeriv ℝ (k + 1) (extendedVelocity (k + 1) (ω t)) y -
        iteratedFDeriv ℝ (k + 1) (extendedVelocity (k + 1) (ω t)) z‖ ≤
      (844 / (α * (1 - α)) + k) * N * ‖y - z‖ ^ α := by
  have hu := hω.contDiffOn_halfPlaneVelocity hα hα1 ht
  rw [iteratedFDeriv_extendedVelocity_of_nonneg (by omega) hu le_rfl hy,
    iteratedFDeriv_extendedVelocity_of_nonneg (by omega) hu le_rfl hz]
  exact norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le hα hα1 (hω.contDiffOn t ht)
    (hω.eq_zero t ht) (hω.holder t ht) hy hz

end IsCkVorticityHistory

/-! ### Extensions of different orders -/

section Orders

variable {ω : ℝ → ℝ^2 → ℝ} {a b α R B M : ℝ} {K K' : ℕ}

/-- The flow of an extended velocity of a vorticity history preserves the closed half-plane. -/
theorem mapsTo_flowOn_extendedVelocity (hω : IsVorticityHistory ω a b α R B M) {L : ℝ≥0}
    (hv : PDE.Analysis.ODE.IsLipschitzFieldOn (fun r ↦ extendedVelocity K (ω r)) a b L)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    MapsTo (PDE.Analysis.ODE.flowOn (fun r ↦ extendedVelocity K (ω r)) a b s t) H̄ H̄ :=
  hv.mapsTo_flowOn_nonneg (j := 1) (fun r hr _ hy ↦
    IncompressibleFlow.extendedVelocity_normal_eq_zero K (hω.continuousOn r hr)
      (hω.eq_zero r hr) hy) hs ht

/-- **Extensions of different orders have the same flow on the closed half-plane.** -/
theorem flowOn_extendedVelocity_eq (hω : IsVorticityHistory ω a b α R B M) (hα : 0 < α)
    (hα1 : α < 1) (hK : 1 ≤ K) (hK' : 1 ≤ K')
    (hu : ∀ t ∈ Icc a b, ContDiffOn ℝ K (halfPlaneVelocity (ω t)) H̄)
    (hu' : ∀ t ∈ Icc a b, ContDiffOn ℝ K' (halfPlaneVelocity (ω t)) H̄) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    PDE.Analysis.ODE.flowOn (fun r ↦ extendedVelocity K (ω r)) a b s t x =
      PDE.Analysis.ODE.flowOn (fun r ↦ extendedVelocity K' (ω r)) a b s t x := by
  have hv := hω.isC1FieldOn_extendedVelocity hα hα1 hK hu
  have hv' := hω.isC1FieldOn_extendedVelocity hα hα1 hK' hu'
  refine PDE.Analysis.ODE.flowOn_eq_of_eqOn hv.isLipschitzFieldOn hv'.isLipschitzFieldOn
    (fun s hs t ht ↦ mapsTo_flowOn_extendedVelocity hω hv'.isLipschitzFieldOn hs ht)
    (fun r _ y hy ↦ ?_) hs ht hx
  rw [extendedVelocity_of_nonneg K (ω r) hy, extendedVelocity_of_nonneg K' (ω r) hy]

/-- **Extensions of different orders have the same first variation on the closed
half-plane.** -/
theorem variationOn_extendedVelocity_eq (hω : IsVorticityHistory ω a b α R B M) (hα : 0 < α)
    (hα1 : α < 1) (hK : 1 ≤ K) (hK' : 1 ≤ K')
    (hu : ∀ t ∈ Icc a b, ContDiffOn ℝ K (halfPlaneVelocity (ω t)) H̄)
    (hu' : ∀ t ∈ Icc a b, ContDiffOn ℝ K' (halfPlaneVelocity (ω t)) H̄) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    PDE.Analysis.ODE.variationOn (fun r ↦ extendedVelocity K (ω r))
        (fun r y ↦ fderiv ℝ (extendedVelocity K (ω r)) y) a b s t x =
      PDE.Analysis.ODE.variationOn (fun r ↦ extendedVelocity K' (ω r))
        (fun r y ↦ fderiv ℝ (extendedVelocity K' (ω r)) y) a b s t x := by
  have hv := hω.isC1FieldOn_extendedVelocity hα hα1 hK hu
  have hv' := hω.isC1FieldOn_extendedVelocity hα hα1 hK' hu'
  refine hv.variationOn_eq_of_eqOn hv'
    (fun s hs t ht ↦ mapsTo_flowOn_extendedVelocity hω hv'.isLipschitzFieldOn hs ht)
    (fun r _ y hy ↦ ?_) (fun r hr y hy ↦ ?_) hs ht hx
  · rw [extendedVelocity_of_nonneg K (ω r) hy, extendedVelocity_of_nonneg K' (ω r) hy]
  · change fderiv ℝ (extendedVelocity K (ω r)) y = fderiv ℝ (extendedVelocity K' (ω r)) y
    rw [fderiv_extendedVelocity_of_nonneg hK (hu r hr) hy,
      fderiv_extendedVelocity_of_nonneg hK' (hu' r hr) hy]

/-- **The derivatives within the closed half-plane of the flow maps do not depend on the order
of the extension.** -/
theorem iteratedFDerivWithin_flowOn_extendedVelocity_eq (hω : IsVorticityHistory ω a b α R B M)
    (hα : 0 < α) (hα1 : α < 1) (hK : 1 ≤ K) (hK' : 1 ≤ K')
    (hu : ∀ t ∈ Icc a b, ContDiffOn ℝ K (halfPlaneVelocity (ω t)) H̄)
    (hu' : ∀ t ∈ Icc a b, ContDiffOn ℝ K' (halfPlaneVelocity (ω t)) H̄) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (j : ℕ) {x : ℝ^2} (hx : 0 ≤ x 1) :
    iteratedFDerivWithin ℝ j (PDE.Analysis.ODE.flowOn (fun r ↦ extendedVelocity K (ω r)) a b s t)
        H̄ x =
      iteratedFDerivWithin ℝ j
        (PDE.Analysis.ODE.flowOn (fun r ↦ extendedVelocity K' (ω r)) a b s t) H̄ x := by
  have h : EqOn (PDE.Analysis.ODE.flowOn (fun r ↦ extendedVelocity K (ω r)) a b s t)
      (PDE.Analysis.ODE.flowOn (fun r ↦ extendedVelocity K' (ω r)) a b s t) H̄ := fun _ hy ↦
    flowOn_extendedVelocity_eq hω hα hα1 hK hK' hu hu' hs ht hy
  exact iteratedFDerivWithin_congr h hx j

end Orders

/-! ### Order one and limits -/

/-- A `C^{1,α}` history is a history of order one, with the largest of its bounds. -/
theorem IsC1VorticityHistory.toIsCkVorticityHistory {ω : ℝ → ℝ^2 → ℝ} {a b α R B M B₁ M₁ : ℝ}
    (hω : IsC1VorticityHistory ω a b α R B M B₁ M₁) :
    IsCkVorticityHistory 1 ω a b α R (max B (max B₁ M₁)) where
  contDiffOn t ht := by exact_mod_cast hω.contDiffOn t ht
  eq_zero := hω.eq_zero
  norm_le t ht j hj y hy := by
    interval_cases j
    · rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
      exact (hω.abs_le t ht y hy).trans (le_max_left _ _)
    · rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper y hy)]
      exact (hω.norm_fderivWithin_le t ht y hy).trans
        ((le_max_left _ _).trans (le_max_right _ _))
  holder t ht y z hy hz := by
    rw [norm_iteratedFDerivWithin_one_sub _ hy hz]
    exact (hω.holder_fderivWithin t ht y z hy hz).trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) (Real.rpow_nonneg (norm_nonneg _) α))
  uniform j hj t ht ε hε := by
    interval_cases j
    · obtain ⟨δ, hδ, h⟩ := hω.uniform t ht ε hε
      refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
      rw [PDE.Analysis.norm_iteratedFDerivWithin_zero_sub_apply, Real.norm_eq_abs]
      exact h s hs hst y hy
    · obtain ⟨δ, hδ, h⟩ := hω.uniform_fderivWithin t ht ε hε
      refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
      rw [norm_iteratedFDerivWithin_one_sub_apply _ _ hy]
      exact h s hs hst y hy

namespace IsCkVorticityHistory

variable {k : ℕ} {ω : ℝ → ℝ^2 → ℝ} {a b α R N : ℝ}

/-- A `C^{k,α}` history with bound `N` has every larger bound. -/
theorem of_le (hω : IsCkVorticityHistory k ω a b α R N) {N' : ℝ} (hN : N ≤ N') :
    IsCkVorticityHistory k ω a b α R N' where
  contDiffOn := hω.contDiffOn
  eq_zero := hω.eq_zero
  norm_le t ht j hj y hy := (hω.norm_le t ht j hj y hy).trans hN
  holder t ht y z hy hz := (hω.holder t ht y z hy hz).trans
    (mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg (norm_nonneg _) α))
  uniform := hω.uniform

/-- A `C^{k,α}` history that vanishes on the closed half-plane outside the disc of radius `R'`
has the support radius `R'`. -/
theorem of_eq_zero (hω : IsCkVorticityHistory k ω a b α R N) {R' : ℝ}
    (h : ∀ t ∈ Icc a b, ∀ y : ℝ^2, 0 ≤ y 1 → R' < ‖y‖ → ω t y = 0) :
    IsCkVorticityHistory k ω a b α R' N :=
  { hω with eq_zero := h }

/-- **Limits of `C^{k,α}` histories.** For `0 < α ≤ 1`, a pointwise limit on `[a, b] × H̄` of
`C^{k,α}` histories with common support radius and bound that are Cauchy uniformly on
`[a, b] × H̄` is a `C^{k,α}` history with the same support radius and bound. -/
theorem of_tendsto {g : ℕ → ℝ → ℝ^2 → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : ∀ n, IsCkVorticityHistory k (g n) a b α R N)
    (hc : ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀, ∀ t ∈ Icc a b, ∀ y : ℝ^2, 0 ≤ y 1 →
      |g n t y - g m t y| ≤ ε)
    (hlim : ∀ t ∈ Icc a b, ∀ y : ℝ^2, 0 ≤ y 1 → Tendsto (fun n ↦ g n t y) atTop (𝓝 (ω t y))) :
    IsCkVorticityHistory k ω a b α R N := by
  have hc' : ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀, ∀ t ∈ Icc a b, ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖g n t y - g m t y‖ ≤ ε := by
    simpa only [Real.norm_eq_abs] using hc
  have key {t : ℝ} (ht : t ∈ Icc a b) := PDE.Analysis.contDiffOn_of_tendsto (I := Icc a b) hα
    hα1 ((hg 0).nonneg ht) (fun n s hs ↦ (hg n).contDiffOn s hs) (fun n s hs ↦ (hg n).norm_le s hs)
    (fun n s hs ↦ (hg n).holder s hs) hc' ht (hlim t ht)
  refine ⟨fun t ht ↦ (key ht).1, fun t ht y hy hyR ↦ ?_, fun t ht j hj y hy ↦ ?_,
    fun t ht y z hy hz ↦ ?_, fun j hj t ht ε hε ↦ ?_⟩
  · exact tendsto_nhds_unique (hlim t ht y hy)
      (tendsto_const_nhds.congr fun n ↦ ((hg n).eq_zero t ht y hy hyR).symm)
  · exact le_of_tendsto ((key ht).2 j hj y hy).norm
      (Eventually.of_forall fun n ↦ (hg n).norm_le t ht j hj y hy)
  · exact le_of_tendsto (((key ht).2 k le_rfl y hy).sub ((key ht).2 k le_rfl z hz)).norm
      (Eventually.of_forall fun n ↦ (hg n).holder t ht y z hy hz)
  · have hε3 : 0 < ε / 3 := by positivity
    obtain ⟨n₀, hn₀⟩ := PDE.Analysis.iteratedFDerivWithin_cauchy (I := Icc a b) hα hα1
      ((hg 0).nonneg ht) (fun n s hs ↦ (hg n).contDiffOn s hs)
      (fun n s hs ↦ (hg n).norm_le s hs) (fun n s hs ↦ (hg n).holder s hs) hc' j hj (ε / 3) hε3
    have hconv {s : ℝ} (hs : s ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
        ‖iteratedFDerivWithin ℝ j (g n₀ s) H̄ y - iteratedFDerivWithin ℝ j (ω s) H̄ y‖ ≤
          ε / 3 :=
      le_of_tendsto ((tendsto_const_nhds.sub ((key hs).2 j hj y hy)).norm)
        (eventually_atTop.mpr ⟨n₀, fun m hm ↦ hn₀ n₀ le_rfl m hm s hs y hy⟩)
    obtain ⟨δ, hδ, h⟩ := (hg n₀).uniform j hj t ht (ε / 3) hε3
    refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
    have e₁ := norm_sub_le_norm_sub_add_norm_sub (iteratedFDerivWithin ℝ j (ω s) H̄ y)
      (iteratedFDerivWithin ℝ j (g n₀ s) H̄ y) (iteratedFDerivWithin ℝ j (ω t) H̄ y)
    have e₂ := norm_sub_le_norm_sub_add_norm_sub (iteratedFDerivWithin ℝ j (g n₀ s) H̄ y)
      (iteratedFDerivWithin ℝ j (g n₀ t) H̄ y) (iteratedFDerivWithin ℝ j (ω t) H̄ y)
    linarith [h s hs hst y hy, hconv ht hy, hconv hs hy, norm_sub_rev
      (iteratedFDerivWithin ℝ j (g n₀ s) H̄ y) (iteratedFDerivWithin ℝ j (ω s) H̄ y)]

end IsCkVorticityHistory

end IncompressibleFlow
