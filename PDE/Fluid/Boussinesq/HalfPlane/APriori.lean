/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.APrioriTopBounds
import PDE.Fluid.Boussinesq.HalfPlane.IterationBounds

/-!
# The a priori estimate behind the continuation criterion

A regular solution of the Boussinesq equations in the closed half-plane `H̄` on `[0, b]` whose
velocity gradient is bounded by `A t` with `∫₀ᵇ A ≤ Λ` keeps data of the class `IsHolderData` with
support radius and bounds depending only on `α`, the data bounds `R`, `N`, on `Λ` and on `b`
(`exists_holderData_bound`).

## Main definitions

* `secondDerivConst`: the constant `200/α + 40π(1 + R²) + 34` of the Schauder bound of `D²u`.
* `topBound`: the top-order bound `c (1 + C L exp (C L))` of `Dω`, `D²θ` and their Hölder
  constants on `[0, b]`, `b ≤ L`.

## Main results

* `exists_holderData_bound`: every time slice of a regular solution on `[0, t₁]` with
  `∫₀^{t₁} A ≤ Λ` is of the class `IsHolderData` with bounds depending only on `α`, `R`, `N`,
  `Λ` and `b`.
* `IsSolutionOn.top_bound`: under the lower-order bounds, the gradient of the vorticity, the
  Hessian of the temperature and their `α`-Hölder constants are at most `topBound` on `[0, b]`.
* `IsSolutionOn.norm_vorticityGradient_le`: `‖Dω_r‖ ≤ (N + ∫₀ʳ Y) exp Λ` on `H̄`.
* `IsSolutionOn.norm_hessian_le`: `‖D²θ_r‖ ≤ (N + Gθ k Bω L + 2 Gθ k ∫₀ʳ Y) exp (2Λ)` on `H̄`,
  `k = secondDerivConst α R₁`.
* `IsSolutionOn.norm_vorticityGradient_sub_le`: the Hölder constant of `Dω_r` on `H̄`.
* `IsSolutionOn.norm_hessian_sub_le`: the Hölder constant of `D²θ_r` on `H̄`.
* `norm_fderivWithin_fderivWithin_halfPlaneVelocity_le`: at one time the second derivatives of
  the velocity of a `C^{1,α}` vorticity are at most `secondDerivBound α R B B₁ M₁`.
* `norm_fderivWithin_fderivWithin_halfPlaneVelocity_sub_le`: they are `α`-Hölder on `H̄` with
  constant `(844/(α(1-α)) + 1) M₁`.

## How it works

The lower-order quantities (support, values, temperature gradient) and the Hölder constants of the
vorticity and of the temperature gradient are bounded by the transport of the data
(`IsSolutionOn.eq_zero_of_norm`, `IsSolutionOn.abs_vorticity_le`,
`IsSolutionOn.norm_fderiv_temperature_le`, `IsSolutionOn.holder_bound`). The top-order quantities,
the gradient of the vorticity and the Hessian of the temperature with their Hölder constants, are
bounded through their transported equations along the trajectories of the velocity field of the
vorticity history (`IsSolutionOn.hasDerivWithinAt_hessian`,
`IsSolutionOn.hasDerivWithinAt_vorticityGradient`). Let `Y(s)` be the running supremum of these four
quantities. The second derivatives of the velocity enter only linearly, through the Schauder bound
`‖D²u‖ ≤ secondDerivConst α R (B + 2Y)` and the Hölder bound `(844/(α(1-α)) + 1) Y`
(`norm_fderivWithin_fderivWithin_halfPlaneVelocity_le`,
`norm_fderivWithin_fderivWithin_halfPlaneVelocity_sub_le`), so `Y(s) ≤ c + C ∫₀ˢ Y`. Grönwall's
inequality for monotone functions, `PDE.Analysis.ODE.le_of_le_add_integral_of_monotoneOn`, then
bounds `Y` by `topBound` (`IsSolutionOn.top_bound`). In `exists_holderData_bound` all constants are
those of `[0, b]`, so the same `R'` and `N'` serve every `t₁ ≤ b`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE IncompressibleFlow PDE.Hyperbolic.Transport
open scoped Topology NNReal
open SobolevSpace

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The constant `200/α + 40π(1 + R²) + 34` of `secondDerivBound`. -/
def secondDerivConst (α R : ℝ) : ℝ :=
  200 / α + 40 * Real.pi * (1 + R ^ 2) + 1 + 33

private theorem secondDerivConst_nonneg {α : ℝ} (R : ℝ) (hα : 0 < α) :
    0 ≤ secondDerivConst α R := by
  unfold secondDerivConst
  positivity

/-- For nonnegative `B`, `B₁`, `M₁` the second-derivative bound is at most
`secondDerivConst α R * (B + B₁ + M₁)`. -/
theorem secondDerivBound_le {α R B B₁ M₁ : ℝ} (hα : 0 < α) (hB : 0 ≤ B) (hB₁ : 0 ≤ B₁)
    (hM₁ : 0 ≤ M₁) : secondDerivBound α R B B₁ M₁ ≤ secondDerivConst α R * (B + B₁ + M₁) := by
  refine mul_le_mul_of_nonneg_left ?_ (secondDerivConst_nonneg R hα)
  refine max_le (by linarith) (max_le (by linarith) (by linarith))

/-- At one time, the second derivatives of the velocity of a `C^{1,α}` vorticity are bounded by
`secondDerivBound α R B B₁ M₁`. -/
theorem norm_fderivWithin_fderivWithin_halfPlaneVelocity_le {α R B B₁ M₁ : ℝ} {f : ℝ^2 → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R) (hf : ContDiffOn ℝ 1 f H̄)
    (hz : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hB : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ B)
    (hB₁ : ∀ y : ℝ^2, 0 ≤ y 1 → ‖fderivWithin ℝ f H̄ y‖ ≤ B₁)
    (hM₁ : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderivWithin ℝ f H̄ y - fderivWithin ℝ f H̄ z‖ ≤ M₁ * ‖y - z‖ ^ α)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity f) H̄) H̄ x‖ ≤
      secondDerivBound α R B B₁ M₁ := by
  rw [← norm_iteratedFDerivWithin_two _ hx]
  have hN : ∀ j ≤ 1, ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖iteratedFDerivWithin ℝ j f H̄ y‖ ≤ max B (max B₁ M₁) := by
    intro j hj y hy
    interval_cases j
    · rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
      exact (hB y hy).trans (le_max_left _ _)
    · rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper y hy)]
      exact (hB₁ y hy).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ 1 f H̄ y - iteratedFDerivWithin ℝ 1 f H̄ z‖ ≤
        max B (max B₁ M₁) * ‖y - z‖ ^ α := fun y z hy hz ↦ by
    rw [norm_iteratedFDerivWithin_one_sub _ hy hz]
    refine (hM₁ y z hy hz).trans ?_
    gcongr
    exact (le_max_right _ _).trans (le_max_right _ _)
  have h := norm_iteratedFDerivWithin_halfPlaneVelocity_le_mul (k := 1) hα hα1 hR
    (by exact_mod_cast hf) hz hN hM (j := 2) le_rfl hx
  unfold secondDerivBound
  exact_mod_cast h

/-- At one time, the second derivatives of the velocity of a `C^{1,α}` vorticity are `α`-Hölder
on the closed half-plane with constant `(844/(α(1-α)) + 1) M₁`. -/
theorem norm_fderivWithin_fderivWithin_halfPlaneVelocity_sub_le {α R M₁ : ℝ} {f : ℝ^2 → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hf : ContDiffOn ℝ 1 f H̄)
    (hz : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hM₁ : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderivWithin ℝ f H̄ y - fderivWithin ℝ f H̄ z‖ ≤ M₁ * ‖y - z‖ ^ α)
    {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    ‖fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity f) H̄) H̄ x -
        fderivWithin ℝ (fderivWithin ℝ (halfPlaneVelocity f) H̄) H̄ x'‖ ≤
      (844 / (α * (1 - α)) + 1) * M₁ * ‖x - x'‖ ^ α := by
  have h := norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le hα hα1 (k := 1)
    (by exact_mod_cast hf) hz (fun y z hy hz ↦ by
      rw [norm_iteratedFDerivWithin_one_sub _ hy hz]
      exact hM₁ y z hy hz) hx hx'
  rw [norm_iteratedFDerivWithin_succ_sub _ hx hx' 1, norm_iteratedFDerivWithin_one_sub _ hx hx']
    at h
  exact_mod_cast h

/-- For a function monotone on `[0, b]` and `r ∈ [0, b]`, `c ≥ 0`:
`∫₀ʳ (c + C Y) ≤ c b + C ∫₀ʳ Y`. -/
theorem integral_add_mul_le {Y : ℝ → ℝ} {b c C r : ℝ} (hYm : MonotoneOn Y (Icc 0 b))
    (hc : 0 ≤ c) (hr : r ∈ Icc 0 b) :
    ∫ ρ in (0)..r, (c + C * Y ρ) ≤ c * b + C * ∫ ρ in (0)..r, Y ρ := by
  have hY : IntervalIntegrable Y volume 0 r :=
    (hYm.mono (by rw [uIcc_of_le hr.1]; exact Icc_subset_Icc le_rfl hr.2)).intervalIntegrable
  rw [intervalIntegral.integral_add intervalIntegrable_const (hY.const_mul C),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, sub_zero, smul_eq_mul]
  have := mul_le_mul_of_nonneg_right hr.2 hc
  linarith

/-- A function monotone on `[0, b]` gives integrable affine majorants on `[0, r] ⊆ [0, b]`. -/
theorem intervalIntegrable_add_mul {Y : ℝ → ℝ} {b c C r : ℝ} (hYm : MonotoneOn Y (Icc 0 b))
    (hr : r ∈ Icc 0 b) : IntervalIntegrable (fun ρ ↦ c + C * Y ρ) volume 0 r :=
  intervalIntegrable_const.add
    ((hYm.mono (by rw [uIcc_of_le hr.1]; exact Icc_subset_Icc le_rfl hr.2)).intervalIntegrable
      |>.const_mul C)

/-- A Hölder constant on the closed half-plane is nonnegative. -/
theorem nonneg_of_norm_sub_le {E : Type*} [SeminormedAddCommGroup E] {F : ℝ^2 → E} {M α : ℝ}
    (h : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → ‖F y - F z‖ ≤ M * ‖y - z‖ ^ α) : 0 ≤ M := by
  have h1 := h (EuclideanSpace.single 1 1) 0 (by simp) (by simp)
  have hn : ‖(EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : ℝ^2) - 0‖ = 1 := by simp
  rw [hn, Real.one_rpow, mul_one] at h1
  exact (norm_nonneg _).trans h1

/-- The constant term `c` of the closed inequality `Y ≤ c + C ∫ Y` of the top-order bounds. -/
def topConst (α N Λ L R₁ Bω Gθ Qθ : ℝ) : ℝ :=
  N * Real.exp Λ + (N + Gθ * secondDerivConst α R₁ * Bω * L) * Real.exp Λ ^ 2 +
    N * Real.exp Λ ^ 2 + (N + Real.exp Λ * (Qθ * secondDerivConst α R₁ * Bω * L)) * Real.exp Λ ^ 3

/-- The rate `C` of the closed inequality `Y ≤ c + C ∫ Y` of the top-order bounds. -/
def topRate (α Λ R₁ Mω Gθ Qθ : ℝ) : ℝ :=
  Real.exp Λ + 2 * Gθ * secondDerivConst α R₁ * Real.exp Λ ^ 2 +
    Real.exp Λ ^ 3 * (1 + 844 / (α * (1 - α)) * Mω) +
    Real.exp Λ ^ 4 * (2 * (844 / (α * (1 - α))) * Mω + 2 * Qθ * secondDerivConst α R₁ +
      Gθ * (844 / (α * (1 - α)) + 1))

/-- The top-order bound `c (1 + C L exp (C L))`: a bound of the gradient of the vorticity, of the
Hessian of the temperature and of their `α`-Hölder constants on `[0, b]`, `b ≤ L`. -/
def topBound (α N Λ L R₁ Bω Mω Gθ Qθ : ℝ) : ℝ :=
  topConst α N Λ L R₁ Bω Gθ Qθ *
    (1 + topRate α Λ R₁ Mω Gθ Qθ * L * Real.exp (topRate α Λ R₁ Mω Gθ Qθ * L))

/-- Data of the class `IsHolderData` with support radius `R` have every larger support radius. -/
theorem IsHolderData.mono_radius {ω₀ θ₀ : ℝ^2 → ℝ} {α R R' N : ℝ}
    (hd : IsHolderData ω₀ θ₀ α R N) (hR : R ≤ R') : IsHolderData ω₀ θ₀ α R' N :=
  { hd with eq_zero := fun x hx hxR ↦ hd.eq_zero x hx (hR.trans_lt hxR) }

/-- The bound of the Hölder constant of the vorticity is monotone in the length of the interval
of times. -/
theorem vorticityHolderBound_le {α N Λ t b : ℝ} (hα : 0 < α) (hα1 : α < 1) (hN : 0 ≤ N)
    (ht : 0 ≤ t) (htb : t ≤ b) : vorticityHolderBound α N Λ t ≤ vorticityHolderBound α N Λ b := by
  have hCα : 0 ≤ 844 / (α * (1 - α)) := div_nonneg (by norm_num) (mul_nonneg hα.le (by linarith))
  have hb : 0 ≤ b := ht.trans htb
  unfold vorticityHolderBound
  gcongr

/-- The bound of the Hölder constant of the temperature gradient is monotone in the length of
the interval of times. -/
theorem gradientHolderBound_le {α N Λ t b : ℝ} (hα : 0 < α) (hα1 : α < 1) (hN : 0 ≤ N)
    (ht : 0 ≤ t) (htb : t ≤ b) : gradientHolderBound α N Λ t ≤ gradientHolderBound α N Λ b := by
  have hCα : 0 ≤ 844 / (α * (1 - α)) := div_nonneg (by norm_num) (mul_nonneg hα.le (by linarith))
  have hv0 : 0 ≤ vorticityHolderBound α N Λ t := by unfold vorticityHolderBound; positivity
  have hb : 0 ≤ b := ht.trans htb
  have hvb := vorticityHolderBound_le (Λ := Λ) hα hα1 hN ht htb
  unfold gradientHolderBound
  gcongr

namespace IsSolutionOn

variable {sol : VorticityStreamFields} {I : Set ℝ} {b : ℝ}

set_option quotPrecheck false in
/-- The velocity field of the vorticity history. -/
local notation "𝐯" => historyField fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- Its spatial derivative. -/
local notation "𝐃𝐯" => historyFieldDeriv fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- Its second spatial derivative. -/
local notation "𝐃²𝐯" => historyFieldDeriv₂ fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- The position at time `ρ` of the particle of label `a` for the flow of the history. -/
local notation "𝐗 " ρ:max a:max => flowOn 𝐯 0 b ρ 0 a

set_option quotPrecheck false in
/-- The temperature gradient along the particle of label `a`. -/
local notation "𝐆 " ρ:max a:max => fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄ (𝐗 ρ a)

set_option quotPrecheck false in
/-- The Hessian of the temperature along the particle of label `a`. -/
local notation "𝐇 " ρ:max a:max =>
  fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ (𝐗 ρ a)

set_option quotPrecheck false in
/-- The vorticity gradient along the particle of label `a`. -/
local notation "𝐙 " ρ:max a:max => fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ (𝐗 ρ a)

section Flow

variable {α R₀ B M B₁ M₁ Λ : ℝ} {K K₁ K₂ : ℝ≥0} {A : ℝ → ℝ}
  (h : IsSolutionOn sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField sol) (velocityFieldDeriv sol) 0 b K)
  (hω : IsC1VorticityHistory (fun t x ↦ sol.vorticity x t) 0 b α R₀ B M B₁ M₁)
  (hα : 0 < α) (hα1 : α < 1)
  (hv₂ : IsC2FieldOn (historyField fun t x ↦ sol.vorticity x t)
    (historyFieldDeriv fun t x ↦ sol.vorticity x t)
    (historyFieldDeriv₂ fun t x ↦ sol.vorticity x t) 0 b K₁ K₂)
  (hA : ContinuousOn A (Icc 0 b))
  (hDu : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖velocityFieldDeriv sol t x‖ ≤ A t)
  (hΛ : ∫ t in (0)..b, A t ≤ Λ)

include h hb hI hω hα hα1 hDu in
/-- The bound of the derivative of the velocity field of the history on the closed half-plane. -/
theorem norm_historyFieldDeriv_le :
    ∀ ρ ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖historyFieldDeriv (fun t x ↦ sol.vorticity x t) ρ x‖ ≤ A ρ := fun ρ hρ x hx ↦ by
  rw [← h.velocityFieldDeriv_eq_historyFieldDeriv hb hI hω hα hα1 hρ hx]
  exact hDu ρ hρ x hx

omit hα hα1 in
include h hb hI hv hω hv₂ hA hDu hΛ in
/-- The flow of the history is `exp Λ`-Lipschitz on the closed half-plane. -/
theorem norm_flowOn_historyField_sub_le {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) {a a' : ℝ^2} (ha : 0 ≤ a 1)
    (ha' : 0 ≤ a' 1) : ‖𝐗 ρ a - 𝐗 ρ a'‖ ≤ Real.exp Λ * ‖a - a'‖ := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  rw [← flowOn_eq_historyField hv hω hL hρ h0 ha, ← flowOn_eq_historyField hv hω hL hρ h0 ha']
  exact h.norm_trajectory_sub_le hb hI hv hA hDu hΛ hρ ha ha'

omit h hb hI hv hα hα1 in
include hω hv₂ in
/-- The label of a point of the closed half-plane for the flow of the history lies in the
closed half-plane, and its trajectory passes through the point. -/
theorem label_historyField {r : ℝ} (hr : r ∈ Icc 0 b) (hb : 0 ≤ b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    0 ≤ (flowOn 𝐯 0 b 0 r y) 1 ∧ 𝐗 r (flowOn 𝐯 0 b 0 r y) = y := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  exact ⟨mapsTo_flowOn_historyField hω hL 0 h0 r hr hy, hL.flowOn_flowOn_self h0 hr y⟩

omit hα hα1 in
include h hb hI hv hω hv₂ hA hDu hΛ in
/-- The labels of the flow of the history are `exp Λ`-Lipschitz on the closed half-plane. -/
theorem norm_label_historyField_sub_le {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) : ‖flowOn 𝐯 0 b 0 r y - flowOn 𝐯 0 b 0 r z‖ ≤ Real.exp Λ * ‖y - z‖ := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  rw [← flowOn_eq_historyField hv hω hL h0 hr hy, ← flowOn_eq_historyField hv hω hL h0 hr hz]
  exact h.norm_label_sub_le hb hI hv hA hDu hΛ hr hy hz

include h hb hI hω hα hα1 in
/-- The derivative of the velocity field of the history is `α`-Hölder on the closed half-plane
with constant `844/(α(1-α)) M` when the vorticity is `α`-Hölder with constant `M`. -/
theorem norm_historyFieldDeriv_sub_le {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) {Mω : ℝ}
    (hMω : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      |sol.vorticity y ρ - sol.vorticity z ρ| ≤ Mω * ‖y - z‖ ^ α)
    {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    ‖𝐃𝐯 ρ x - 𝐃𝐯 ρ x'‖ ≤ 844 / (α * (1 - α)) * Mω * ‖x - x'‖ ^ α := by
  rw [← h.velocityFieldDeriv_eq_historyFieldDeriv hb hI hω hα hα1 hρ hx,
    ← h.velocityFieldDeriv_eq_historyFieldDeriv hb hI hω hα hα1 hρ hx']
  exact h.norm_velocityFieldDeriv_sub_le hb hI hα hα1 hρ hMω hx hx'

end Flow

section Top

variable {α R₀ B M B₁ M₁ Λ R N Rq Nq R₁ Bω Mω Gθ Qθ L : ℝ} {K K₁ K₂ : ℝ≥0} {A Y : ℝ → ℝ}
  (h : IsSolutionOn sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField sol) (velocityFieldDeriv sol) 0 b K)
  (hω : IsC1VorticityHistory (fun t x ↦ sol.vorticity x t) 0 b α R₀ B M B₁ M₁)
  (hα : 0 < α) (hα1 : α < 1)
  (hv₂ : IsC2FieldOn (historyField fun t x ↦ sol.vorticity x t)
    (historyFieldDeriv fun t x ↦ sol.vorticity x t)
    (historyFieldDeriv₂ fun t x ↦ sol.vorticity x t) 0 b K₁ K₂)
  (hreg : ∀ t ∈ Icc 0 b,
    IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α Rq Nq)
  (hA : ContinuousOn A (Icc 0 b))
  (hDu : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖velocityFieldDeriv sol t x‖ ≤ A t)
  (hΛ : ∫ t in (0)..b, A t ≤ Λ)
  (hd : IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N)
  (hR₁0 : 0 ≤ R₁)
  (hR₁ : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → R₁ < ‖x‖ → sol.vorticity x t = 0)
  (hBω : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → |sol.vorticity x t| ≤ Bω)
  (hMω : ∀ t ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
    |sol.vorticity y t - sol.vorticity z t| ≤ Mω * ‖y - z‖ ^ α)
  (hGθ : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
    ‖fderivWithin ℝ (fun x ↦ sol.temperature x t) H̄ x‖ ≤ Gθ)
  (hQθ : ∀ t ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
    ‖fderivWithin ℝ (fun x ↦ sol.temperature x t) H̄ y -
      fderivWithin ℝ (fun x ↦ sol.temperature x t) H̄ z‖ ≤ Qθ * ‖y - z‖ ^ α)
  (hbL : b ≤ L)
  (hYm : MonotoneOn Y (Icc 0 b)) (hY0 : ∀ t ∈ Icc 0 b, 0 ≤ Y t)
  (hY₁ : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
    ‖fderivWithin ℝ (fun x ↦ sol.vorticity x t) H̄ x‖ ≤ Y t)
  (hY₂ : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
    ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x t) H̄) H̄ x‖ ≤ Y t)
  (hY₃ : ∀ t ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
    ‖fderivWithin ℝ (fun x ↦ sol.vorticity x t) H̄ y -
      fderivWithin ℝ (fun x ↦ sol.vorticity x t) H̄ z‖ ≤ Y t * ‖y - z‖ ^ α)
  (hY₄ : ∀ t ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
    ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x t) H̄) H̄ y -
      fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x t) H̄) H̄ z‖ ≤
        Y t * ‖y - z‖ ^ α)

omit h hb hI hv in
include hω hα hα1 hreg hR₁0 hR₁ hBω hY0 hY₁ hY₃ in
/-- **The Schauder bound of the second derivatives of the field** at the time `ρ`:
`‖D²v(ρ, x)‖ ≤ secondDerivConst α R₁ (B + 2 Y ρ)`. -/
theorem norm_historyFieldDeriv₂_le {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖𝐃²𝐯 ρ x‖ ≤ secondDerivConst α R₁ * (Bω + Y ρ + Y ρ) := by
  have hBω0 : 0 ≤ Bω := (abs_nonneg _).trans (hBω ρ hρ 0 (by simp))
  rw [IsC1VorticityHistory.historyFieldDeriv₂_eq hω hα hα1 hρ hx]
  exact (norm_fderivWithin_fderivWithin_halfPlaneVelocity_le hα hα1 hR₁0
    (hreg ρ hρ).vorticity_contDiffOn (hR₁ ρ hρ) (hBω ρ hρ) (hY₁ ρ hρ) (hY₃ ρ hρ) hx).trans
    (secondDerivBound_le hα hBω0 (hY0 ρ hρ) (hY0 ρ hρ))

omit h hb hI hv in
include hω hα hα1 hreg hR₁ hY₃ in
/-- **The Hölder bound of the second derivatives of the field** at the time `ρ`, with constant
`(844/(α(1-α)) + 1) Y ρ`. -/
theorem norm_historyFieldDeriv₂_sub_le {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) {x x' : ℝ^2} (hx : 0 ≤ x 1)
    (hx' : 0 ≤ x' 1) :
    ‖𝐃²𝐯 ρ x - 𝐃²𝐯 ρ x'‖ ≤ (844 / (α * (1 - α)) + 1) * Y ρ * ‖x - x'‖ ^ α := by
  rw [IsC1VorticityHistory.historyFieldDeriv₂_eq hω hα hα1 hρ hx,
    IsC1VorticityHistory.historyFieldDeriv₂_eq hω hα hα1 hρ hx']
  exact norm_fderivWithin_fderivWithin_halfPlaneVelocity_sub_le hα hα1
    (hreg ρ hρ).vorticity_contDiffOn (hR₁ ρ hρ) (hY₃ ρ hρ) hx hx'

omit hv₂ hreg hR₁0 hR₁ hBω hY0 hY₁ hY₃ in
include h hb hI hv hω hα hα1 hv₂ hA hDu hΛ in
/-- `‖X(ρ, a) - X(ρ, a')‖^α ≤ exp Λ ‖a - a'‖^α` for labels in the closed half-plane. -/
theorem rpow_norm_flowOn_sub_le {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) {a a' : ℝ^2} (ha : 0 ≤ a 1)
    (ha' : 0 ≤ a' 1) : ‖𝐗 ρ a - 𝐗 ρ a'‖ ^ α ≤ Real.exp Λ * ‖a - a'‖ ^ α :=
  (Real.rpow_le_rpow (norm_nonneg _)
    (h.norm_flowOn_historyField_sub_le hb hI hv hω hv₂ hA hDu hΛ hρ ha ha') hα.le).trans
    (mul_rpow_le_mul (Real.one_le_exp (zero_le_Λ hb hDu hΛ)) (norm_nonneg _) hα1.le)

omit hv₂ hreg hR₁0 hR₁ hBω hY0 hY₁ hY₃ in
include h hb hI hv hω hα hα1 hv₂ hA hDu hΛ in
/-- `‖Y(r, y) - Y(r, z)‖^α ≤ exp Λ ‖y - z‖^α` for the labels at the time `r`. -/
theorem rpow_norm_label_sub_le {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) :
    ‖flowOn 𝐯 0 b 0 r y - flowOn 𝐯 0 b 0 r z‖ ^ α ≤ Real.exp Λ * ‖y - z‖ ^ α :=
  (Real.rpow_le_rpow (norm_nonneg _)
    (h.norm_label_historyField_sub_le hb hI hv hω hv₂ hA hDu hΛ hr hy hz) hα.le).trans
    (mul_rpow_le_mul (Real.one_le_exp (zero_le_Λ hb hDu hΛ)) (norm_nonneg _) hα1.le)

include h hb hI hv hω hα hα1 hv₂ hreg hA hDu hΛ hd hR₁0 hR₁ hBω hGθ hbL hYm hY0 hY₁ hY₃ in
/-- **The Hessian of the temperature at the time `r`:** with `k = secondDerivConst α R₁`,
`‖D²θ_r‖ ≤ (N + Gθ k Bω L + 2 Gθ k ∫₀ʳ Y) exp (2Λ)` on the closed half-plane. -/
theorem norm_hessian_le {r : ℝ} (hr : r ∈ Icc 0 b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ y‖ ≤
      (N + Gθ * secondDerivConst α R₁ * Bω * L +
        2 * Gθ * secondDerivConst α R₁ * ∫ ρ in (0)..r, Y ρ) * Real.exp (2 * Λ) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  obtain ⟨ha, hya⟩ := label_historyField hω hv₂ hr hb.le hy
  set a := flowOn 𝐯 0 b 0 r y
  set k := secondDerivConst α R₁
  have hk : 0 ≤ k := secondDerivConst_nonneg R₁ hα
  have hGθ0 : 0 ≤ Gθ := (norm_nonneg _).trans (hGθ 0 h0 0 (by simp))
  have hBω0 : 0 ≤ Bω := (abs_nonneg _).trans (hBω 0 h0 0 (by simp))
  have hsub : Icc 0 r ⊆ Icc 0 b := Icc_subset_Icc le_rfl hr.2
  have hgm : ∀ ρ ∈ Icc 0 r,
      ‖𝐆 ρ a‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖ ≤ Gθ * k * Bω + 2 * Gθ * k * Y ρ := fun ρ hρ ↦ by
    have hX := mapsTo_flowOn_historyField hω hL ρ (hsub hρ) 0 h0 ha
    refine (mul_le_mul (hGθ ρ (hsub hρ) _ hX)
      (norm_historyFieldDeriv₂_le hω hα hα1 hreg hR₁0 hR₁ hBω hY0 hY₁ hY₃ (hsub hρ) hX)
      (ContinuousLinearMap.opNorm_nonneg _) hGθ0).trans_eq (by ring)
  have key := h.norm_hessian_flowOn_le hb hI hv hω hv₂ hreg hA
    (h.norm_historyFieldDeriv_le hb hI hω hα hα1 hDu) hΛ ha hr
    (intervalIntegrable_add_mul hYm hr) hgm
  rw [hya] at key
  have hN := hd.norm_fderivWithin_fderivWithin_temperature_le a ha
  have hint := integral_add_mul_le (C := 2 * Gθ * k) hYm (by positivity : 0 ≤ Gθ * k * Bω) hr
  have hbL' : Gθ * k * Bω * b ≤ Gθ * k * Bω * L := mul_le_mul_of_nonneg_left hbL (by positivity)
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  linarith

include h hb hI hv hω hα hα1 hv₂ hreg hA hDu hΛ hd hYm hY₂ in
/-- **The gradient of the vorticity at the time `r`:**
`‖Dω_r‖ ≤ (N + ∫₀ʳ Y) exp Λ` on the closed half-plane. -/
theorem norm_vorticityGradient_le {r : ℝ} (hr : r ∈ Icc 0 b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖fderivWithin ℝ (fun x ↦ sol.vorticity x r) H̄ y‖ ≤
      (N + ∫ ρ in (0)..r, Y ρ) * Real.exp (1 * Λ) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  obtain ⟨ha, hya⟩ := label_historyField hω hv₂ hr hb.le hy
  set a := flowOn 𝐯 0 b 0 r y
  have hsub : Icc 0 r ⊆ Icc 0 b := Icc_subset_Icc le_rfl hr.2
  have hYi : IntervalIntegrable Y volume 0 r :=
    (hYm.mono (by rw [uIcc_of_le hr.1]; exact hsub)).intervalIntegrable
  have key := h.norm_vorticityGradient_flowOn_le hb hI hv hω hα hα1 hv₂ hreg hA
    (h.norm_historyFieldDeriv_le hb hI hω hα hα1 hDu) hΛ ha hr hYi
    (fun ρ hρ ↦ hY₂ ρ (hsub hρ) _ (mapsTo_flowOn_historyField hω hL ρ (hsub hρ) 0 h0 ha))
  rw [hya] at key
  have hN := hd.norm_fderivWithin_vorticity_le a ha
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  linarith

include h hb hI hv hω hα hα1 hv₂ hreg hA hDu hΛ hd hR₁0 hR₁ hBω hMω hGθ hQθ hbL hYm hY0 hY₁ hY₂
  hY₃ in
/-- **The Hölder constant of the Hessian of the temperature at the time `r`:** with
`k = secondDerivConst α R₁` and `Cα = 844/(α(1-α))`, the Hessian is `α`-Hölder on the closed
half-plane with constant
`(N + exp Λ (Qθ k Bω L + (2 Cα Mω + 2 Qθ k + Gθ (Cα + 1)) ∫₀ʳ Y)) exp (2Λ) exp Λ`. -/
theorem norm_hessian_sub_le {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) :
    ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ y -
        fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ z‖ ≤
      (N + Real.exp Λ * (Qθ * secondDerivConst α R₁ * Bω * L +
        (2 * (844 / (α * (1 - α))) * Mω + 2 * Qθ * secondDerivConst α R₁ +
          Gθ * (844 / (α * (1 - α)) + 1)) * ∫ ρ in (0)..r, Y ρ)) * Real.exp (2 * Λ) *
        (Real.exp Λ * ‖y - z‖ ^ α) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  obtain ⟨ha, hya⟩ := label_historyField hω hv₂ hr hb.le hy
  obtain ⟨ha', hza⟩ := label_historyField hω hv₂ hr hb.le hz
  have hlab := h.rpow_norm_label_sub_le hb hI hv hω hα hα1 hv₂ hA hDu hΛ hr hy hz
  set a := flowOn 𝐯 0 b 0 r y
  set a' := flowOn 𝐯 0 b 0 r z
  set k := secondDerivConst α R₁
  set Cα := 844 / (α * (1 - α))
  set E := Real.exp Λ
  have hk : 0 ≤ k := secondDerivConst_nonneg R₁ hα
  have hCα : 0 ≤ Cα := div_nonneg (by norm_num) (mul_nonneg hα.le (by linarith))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hGθ0 : 0 ≤ Gθ := (norm_nonneg _).trans (hGθ 0 h0 0 (by simp))
  have hBω0 : 0 ≤ Bω := (abs_nonneg _).trans (hBω 0 h0 0 (by simp))
  have hMω0 : 0 ≤ Mω := nonneg_of_norm_sub_le (F := fun x ↦ sol.vorticity x 0) (α := α)
    fun y z hy hz ↦ by rw [Real.norm_eq_abs]; exact hMω 0 h0 y z hy hz
  have hQθ0 : 0 ≤ Qθ := nonneg_of_norm_sub_le (hQθ 0 h0)
  have hL0 : 0 ≤ L := hb.le.trans hbL
  set d := E * ‖a - a'‖ ^ α
  have hd0 : 0 ≤ d := by positivity
  set C₃ := 2 * Cα * Mω + 2 * Qθ * k + Gθ * (Cα + 1)
  have hC₃ : 0 ≤ C₃ := by positivity
  have hsub : Icc 0 r ⊆ Icc 0 b := Icc_subset_Icc le_rfl hr.2
  have hgm : ∀ ρ ∈ Icc 0 r,
      2 * ‖𝐇 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖ + ‖𝐆 ρ a - 𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖ +
        ‖𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a) - 𝐃²𝐯 ρ (𝐗 ρ a')‖ ≤ d * (Qθ * k * Bω) + d * C₃ * Y ρ := by
    intro ρ hρ
    have hρ' := hsub hρ
    have hX := mapsTo_flowOn_historyField hω hL ρ hρ' 0 h0 ha
    have hX' := mapsTo_flowOn_historyField hω hL ρ hρ' 0 h0 ha'
    have hδ := h.rpow_norm_flowOn_sub_le hb hI hv hω hα hα1 hv₂ hA hDu hΛ hρ' ha ha'
    have hYρ := hY0 ρ hρ'
    have e1 : ‖𝐇 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖ ≤ Y ρ * (Cα * Mω * d) :=
      mul_le_mul (hY₂ ρ hρ' _ hX')
        ((h.norm_historyFieldDeriv_sub_le hb hI hω hα hα1 hρ' (hMω ρ hρ') hX hX').trans
          (mul_le_mul_of_nonneg_left hδ (by positivity)))
        (norm_nonneg _) hYρ
    have e2 : ‖𝐆 ρ a - 𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖ ≤ (Qθ * d) * (k * (Bω + Y ρ + Y ρ)) :=
      mul_le_mul ((hQθ ρ hρ' _ _ hX hX').trans (mul_le_mul_of_nonneg_left hδ hQθ0))
        (norm_historyFieldDeriv₂_le hω hα hα1 hreg hR₁0 hR₁ hBω hY0 hY₁ hY₃ hρ' hX)
        (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
    have e3 : ‖𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a) - 𝐃²𝐯 ρ (𝐗 ρ a')‖ ≤ Gθ * ((Cα + 1) * Y ρ * d) :=
      mul_le_mul (hGθ ρ hρ' _ hX')
        ((norm_historyFieldDeriv₂_sub_le hω hα hα1 hreg hR₁ hY₃ hρ' hX hX').trans
          (mul_le_mul_of_nonneg_left hδ (by positivity)))
        (ContinuousLinearMap.opNorm_nonneg _) hGθ0
    simp only [C₃]
    linarith
  have key := h.norm_hessian_flowOn_sub_le hb hI hv hω hv₂ hreg hA
    (h.norm_historyFieldDeriv_le hb hI hω hα hα1 hDu) hΛ ha ha' hr
    (intervalIntegrable_add_mul hYm hr) hgm
  rw [hya, hza] at key
  have hdata := hd.holder_temperature a a' ha ha'
  have hint := integral_add_mul_le (C := d * C₃) hYm (by positivity : 0 ≤ d * (Qθ * k * Bω)) hr
  have hbL' : d * (Qθ * k * Bω) * b ≤ d * (Qθ * k * Bω) * L :=
    mul_le_mul_of_nonneg_left hbL (by positivity)
  have hIY : 0 ≤ ∫ ρ in (0)..r, Y ρ :=
    intervalIntegral.integral_nonneg hr.1 fun ρ hρ ↦ hY0 ρ (hsub hρ)
  have hc0 : 0 ≤ (N + E * (Qθ * k * Bω * L + C₃ * ∫ ρ in (0)..r, Y ρ)) * Real.exp (2 * Λ) := by
    positivity
  calc _ ≤ _ := key
    _ ≤ (N * ‖a - a'‖ ^ α + (d * (Qθ * k * Bω) * L + d * C₃ * ∫ ρ in (0)..r, Y ρ)) *
          Real.exp (2 * Λ) :=
        mul_le_mul_of_nonneg_right (add_le_add hdata (hint.trans (by linarith)))
          (Real.exp_pos _).le
    _ = (N + E * (Qθ * k * Bω * L + C₃ * ∫ ρ in (0)..r, Y ρ)) * Real.exp (2 * Λ) *
          ‖a - a'‖ ^ α := by simp only [d]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlab hc0

include h hb hI hv hω hα hα1 hv₂ hreg hA hDu hΛ hd hMω hYm hY0 hY₁ hY₄ in
/-- **The Hölder constant of the gradient of the vorticity at the time `r`:** with
`Cα = 844/(α(1-α))`, the gradient is `α`-Hölder on the closed half-plane with constant
`(N + exp Λ (1 + Cα Mω) ∫₀ʳ Y) exp Λ exp Λ`. -/
theorem norm_vorticityGradient_sub_le {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) :
    ‖fderivWithin ℝ (fun x ↦ sol.vorticity x r) H̄ y -
        fderivWithin ℝ (fun x ↦ sol.vorticity x r) H̄ z‖ ≤
      (N + Real.exp Λ * ((1 + 844 / (α * (1 - α)) * Mω) * ∫ ρ in (0)..r, Y ρ)) *
        Real.exp (1 * Λ) * (Real.exp Λ * ‖y - z‖ ^ α) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  obtain ⟨ha, hya⟩ := label_historyField hω hv₂ hr hb.le hy
  obtain ⟨ha', hza⟩ := label_historyField hω hv₂ hr hb.le hz
  have hlab := h.rpow_norm_label_sub_le hb hI hv hω hα hα1 hv₂ hA hDu hΛ hr hy hz
  set a := flowOn 𝐯 0 b 0 r y
  set a' := flowOn 𝐯 0 b 0 r z
  set Cα := 844 / (α * (1 - α))
  set E := Real.exp Λ
  have hCα : 0 ≤ Cα := div_nonneg (by norm_num) (mul_nonneg hα.le (by linarith))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hMω0 : 0 ≤ Mω := nonneg_of_norm_sub_le (F := fun x ↦ sol.vorticity x 0) (α := α)
    fun y z hy hz ↦ by rw [Real.norm_eq_abs]; exact hMω 0 h0 y z hy hz
  set d := E * ‖a - a'‖ ^ α
  have hd0 : 0 ≤ d := by positivity
  have hsub : Icc 0 r ⊆ Icc 0 b := Icc_subset_Icc le_rfl hr.2
  have hgm : ∀ ρ ∈ Icc 0 r, ‖𝐇 ρ a - 𝐇 ρ a'‖ + ‖𝐙 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖ ≤
      0 + d * (1 + Cα * Mω) * Y ρ := by
    intro ρ hρ
    have hρ' := hsub hρ
    have hX := mapsTo_flowOn_historyField hω hL ρ hρ' 0 h0 ha
    have hX' := mapsTo_flowOn_historyField hω hL ρ hρ' 0 h0 ha'
    have hδ := h.rpow_norm_flowOn_sub_le hb hI hv hω hα hα1 hv₂ hA hDu hΛ hρ' ha ha'
    have hYρ := hY0 ρ hρ'
    have e1 : ‖𝐇 ρ a - 𝐇 ρ a'‖ ≤ Y ρ * d :=
      (hY₄ ρ hρ' _ _ hX hX').trans (mul_le_mul_of_nonneg_left hδ hYρ)
    have e2 : ‖𝐙 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖ ≤ Y ρ * (Cα * Mω * d) :=
      mul_le_mul (hY₁ ρ hρ' _ hX')
        ((h.norm_historyFieldDeriv_sub_le hb hI hω hα hα1 hρ' (hMω ρ hρ') hX hX').trans
          (mul_le_mul_of_nonneg_left hδ (by positivity)))
        (norm_nonneg _) hYρ
    linarith
  have key := h.norm_vorticityGradient_flowOn_sub_le hb hI hv hω hα hα1 hv₂ hreg hA
    (h.norm_historyFieldDeriv_le hb hI hω hα hα1 hDu) hΛ ha ha' hr
    (intervalIntegrable_add_mul hYm hr) hgm
  rw [hya, hza] at key
  have hdata := hd.holder_vorticity a a' ha ha'
  have hint := integral_add_mul_le (C := d * (1 + Cα * Mω)) hYm le_rfl hr
  have hIY : 0 ≤ ∫ ρ in (0)..r, Y ρ :=
    intervalIntegral.integral_nonneg hr.1 fun ρ hρ ↦ hY0 ρ (hsub hρ)
  have hc0 : 0 ≤ (N + E * ((1 + Cα * Mω) * ∫ ρ in (0)..r, Y ρ)) * Real.exp (1 * Λ) := by
    positivity
  calc _ ≤ _ := key
    _ ≤ (N * ‖a - a'‖ ^ α + d * (1 + Cα * Mω) * ∫ ρ in (0)..r, Y ρ) * Real.exp (1 * Λ) :=
        mul_le_mul_of_nonneg_right (add_le_add hdata (hint.trans (by linarith)))
          (Real.exp_pos _).le
    _ = (N + E * ((1 + Cα * Mω) * ∫ ρ in (0)..r, Y ρ)) * Real.exp (1 * Λ) * ‖a - a'‖ ^ α := by
        simp only [d]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlab hc0

include h hb hI hv hω hα hα1 hv₂ hreg hA hDu hΛ hd hR₁0 hR₁ hBω hMω hGθ hQθ hbL in
/-- **The top-order a priori bound.** Under the lower-order bounds `R₁`, `Bω`, `Mω`, `Gθ`, `Qθ`
of the support, the vorticity and its Hölder constant, the temperature gradient and its Hölder
constant, at every time of `[0, b]` the gradient of the vorticity, the Hessian of the
temperature and their `α`-Hölder constants on the closed half-plane are at most
`topBound α N Λ L R₁ Bω Mω Gθ Qθ`. The running supremum `Y` of these four quantities satisfies
`Y ≤ c + C ∫ Y` by the transported equations and is bounded by Grönwall's inequality. -/
theorem top_bound {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    ‖fderivWithin ℝ (fun x ↦ sol.vorticity x r) H̄ y‖ ≤ topBound α N Λ L R₁ Bω Mω Gθ Qθ ∧
      ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ y‖ ≤
        topBound α N Λ L R₁ Bω Mω Gθ Qθ ∧
      ‖fderivWithin ℝ (fun x ↦ sol.vorticity x r) H̄ y -
          fderivWithin ℝ (fun x ↦ sol.vorticity x r) H̄ z‖ ≤
        topBound α N Λ L R₁ Bω Mω Gθ Qθ * ‖y - z‖ ^ α ∧
      ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ y -
          fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ z‖ ≤
        topBound α N Λ L R₁ Bω Mω Gθ Qθ * ‖y - z‖ ^ α := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  set E := Real.exp Λ
  set k := secondDerivConst α R₁
  set Cα := 844 / (α * (1 - α))
  have hk : 0 ≤ k := secondDerivConst_nonneg R₁ hα
  have hCα : 0 ≤ Cα := div_nonneg (by norm_num) (mul_nonneg hα.le (by linarith))
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hGθ0 : 0 ≤ Gθ := (norm_nonneg _).trans (hGθ 0 h0 0 (by simp))
  have hBω0 : 0 ≤ Bω := (abs_nonneg _).trans (hBω 0 h0 0 (by simp))
  have hMω0 : 0 ≤ Mω := nonneg_of_norm_sub_le (F := fun x ↦ sol.vorticity x 0) (α := α)
    fun y z hy hz ↦ by rw [Real.norm_eq_abs]; exact hMω 0 h0 y z hy hz
  have hQθ0 : 0 ≤ Qθ := nonneg_of_norm_sub_le (hQθ 0 h0)
  have hL0 : 0 ≤ L := hb.le.trans hbL
  have he1 : Real.exp (1 * Λ) = E := by rw [one_mul]
  have he2 : Real.exp (2 * Λ) = E ^ 2 := by rw [sq, ← Real.exp_add]; ring_nf
  -- The four quantities and their running supremum.
  set q : ℝ → ℝ^2 → ℝ^2 → ℝ := fun ρ y z ↦
    ‖fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ y‖ +
      ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ y‖ +
      ‖fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ y -
        fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ z‖ / ‖y - z‖ ^ α +
      ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ y -
        fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ z‖ / ‖y - z‖ ^ α
  have hdiv {u v : ℝ} {y z : ℝ^2} (hyz : y ≠ z) (huv : u ≤ v * ‖y - z‖ ^ α) :
      u / ‖y - z‖ ^ α ≤ v :=
    (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyz)) α)).mpr huv
  have hq0 : ∀ ρ y z, 0 ≤ q ρ y z := fun _ _ _ ↦ by positivity
  have hqb : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → y ≠ z →
      q ρ y z ≤ Nq + Nq + Nq + Nq := fun ρ hρ y z hy hz hyz ↦
    add_le_add (add_le_add (add_le_add ((hreg ρ hρ).norm_fderivWithin_vorticity_le y hy)
      ((hreg ρ hρ).norm_fderivWithin_fderivWithin_temperature_le y hy))
      (hdiv hyz ((hreg ρ hρ).holder_vorticity y z hy hz)))
      (hdiv hyz ((hreg ρ hρ).holder_temperature y z hy hz))
  set P := holderSup q
  have hPm : MonotoneOn P (Icc 0 b) := monotoneOn_holderSup hqb
  have hP0 : ∀ ρ ∈ Icc 0 b, 0 ≤ P ρ := fun ρ hρ ↦ holderSup_nonneg hq0 hqb hρ
  have hle (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) (hyz : y ≠ z) :
      q ρ y z ≤ P ρ := le_holderSup hqb hρ.2 ⟨hρ.1, le_rfl⟩ hy hz hyz
  have hshift (y : ℝ^2) (hy : 0 ≤ y 1) :
      0 ≤ (y + EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1 ∧
        y ≠ y + EuclideanSpace.single (1 : Fin 2) (1 : ℝ) :=
    ⟨by simp [add_nonneg hy zero_le_one], fun hyy ↦ by simpa using congrArg (· 1) hyy⟩
  -- each of the four quantities is at most their sum `q`
  have h4 {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
      a ≤ a + b + c + d ∧ b ≤ a + b + c + d ∧ c ≤ a + b + c + d ∧ d ≤ a + b + c + d :=
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hP₁ : ∀ ρ ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ x‖ ≤ P ρ := fun ρ hρ x hx ↦
    (h4 (by positivity) (by positivity) (by positivity) (by positivity)).1.trans
      (hle ρ hρ hx (hshift x hx).1 (hshift x hx).2)
  have hP₂ : ∀ ρ ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ x‖ ≤ P ρ :=
    fun ρ hρ x hx ↦ (h4 (by positivity) (by positivity) (by positivity) (by positivity)).2.1.trans
      (hle ρ hρ hx (hshift x hx).1 (hshift x hx).2)
  have hP₃ : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ y -
        fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ z‖ ≤ P ρ * ‖y - z‖ ^ α :=
    fun ρ hρ y z hy hz ↦ norm_sub_le_of_div_le (F := fun x ↦
      fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ x) hα fun hyz ↦
      (h4 (by positivity) (by positivity) (by positivity) (by positivity)).2.2.1.trans
        (hle ρ hρ hy hz hyz)
  have hP₄ : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ y -
        fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ z‖ ≤
          P ρ * ‖y - z‖ ^ α :=
    fun ρ hρ y z hy hz ↦ norm_sub_le_of_div_le (F := fun x ↦
      fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ x) hα fun hyz ↦
      (h4 (by positivity) (by positivity) (by positivity) (by positivity)).2.2.2.trans
        (hle ρ hρ hy hz hyz)
  -- The closed inequality.
  set c := topConst α N Λ L R₁ Bω Gθ Qθ
  set C := topRate α Λ R₁ Mω Gθ Qθ
  have hc0 : 0 ≤ c := by simp only [c, topConst]; positivity
  have hC0 : 0 ≤ C := by simp only [C, topRate]; positivity
  have hstep : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → y ≠ z →
      q ρ y z ≤ c + C * ∫ σ in (0)..ρ, P σ := by
    intro ρ hρ y z hy hz hyz
    have hpos : 0 < ‖y - z‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyz)) α
    have b1 := h.norm_vorticityGradient_le hb hI hv hω hα hα1 hv₂ hreg hA hDu hΛ hd hPm hP₂ hρ hy
    have b2 := h.norm_hessian_le hb hI hv hω hα hα1 hv₂ hreg hA hDu hΛ hd hR₁0 hR₁ hBω hGθ hbL
      hPm hP0 hP₁ hP₃ hρ hy
    have b3 := h.norm_vorticityGradient_sub_le hb hI hv hω hα hα1 hv₂ hreg hA hDu hΛ hd hMω
      hPm hP0 hP₁ hP₄ hρ hy hz
    have b4 := h.norm_hessian_sub_le hb hI hv hω hα hα1 hv₂ hreg hA hDu hΛ hd hR₁0 hR₁ hBω hMω
      hGθ hQθ hbL hPm hP0 hP₁ hP₂ hP₃ hρ hy hz
    rw [← mul_assoc, ← div_le_iff₀ hpos] at b3 b4
    calc q ρ y z ≤ _ := add_le_add (add_le_add (add_le_add b1 b2) b3) b4
      _ = c + C * ∫ σ in (0)..ρ, P σ := by
        simp only [c, C, topConst, topRate, he1, he2]
        ring
  have hclosed : ∀ s ∈ Icc 0 b, P s ≤ c + C * ∫ σ in (0)..s, P σ := fun s hs ↦
    holderSup_le hs.1 fun ρ hρ y z hy hz hyz ↦
      (hstep ρ ⟨hρ.1, hρ.2.trans hs.2⟩ y z hy hz hyz).trans (by
        gcongr c + C * ?_
        exact integral_le_integral_of_monotoneOn hPm hP0 hρ.1 hρ.2 hs.2)
  have hgron := le_of_le_add_integral_of_monotoneOn hc0 hC0 hPm hclosed r hr
  have hT : P r ≤ topBound α N Λ L R₁ Bω Mω Gθ Qθ := by
    refine hgron.trans (mul_le_mul_of_nonneg_left ?_ hc0)
    have hrL : r ≤ L := hr.2.trans hbL
    gcongr
  have hα0 : 0 ≤ ‖y - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  exact ⟨(hP₁ r hr y hy).trans hT, (hP₂ r hr y hy).trans hT,
    (hP₃ r hr y z hy hz).trans (mul_le_mul_of_nonneg_right hT hα0),
    (hP₄ r hr y z hy hz).trans (mul_le_mul_of_nonneg_right hT hα0)⟩

end Top

end IsSolutionOn

/-- **The a priori estimate of the continuation criterion.** For data of the class
`IsHolderData … α R N` and a bound `A` of the velocity gradient with `∫₀^{t₁} A ≤ Λ`, every
time slice of a regular solution on `[0, t₁]`, `t₁ ≤ b`, is of the class `IsHolderData … α R' N'`
with `R'` and `N'` depending only on `α`, `R`, `N`, `Λ` and `b`. -/
theorem exists_holderData_bound {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (R N Λ b : ℝ) :
    ∃ R' N' : ℝ, ∀ (sol : VorticityStreamFields) (I : Set ℝ) (A : ℝ → ℝ),
      IsRegularSolutionOn sol I α → ∀ t₁, 0 < t₁ → t₁ ≤ b → Icc 0 t₁ ⊆ I →
      IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N →
      (∀ t ∈ Icc 0 t₁, ∀ x : ℝ^2, 0 ≤ x 1 →
        ‖fderivWithin ℝ (halfPlaneVelocity (fun y ↦ sol.vorticity y t)) H̄ x‖ ≤ A t) →
      ContinuousOn A (Icc 0 t₁) → ∫ t in (0)..t₁, A t ≤ Λ →
      ∀ t ∈ Icc 0 t₁,
        IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R' N' := by
  set E := Real.exp Λ
  set R₀ := max R 0
  set Bω := N + b * (N * E)
  set R₁ := R₀ + Bω * (1 + 2 * E ^ 2 * R₀ ^ 2) * b
  set T := topBound α N Λ b R₁ Bω (vorticityHolderBound α N Λ b) (N * E)
    (gradientHolderBound α N Λ b)
  refine ⟨R₁, max (max Bω (N * E)) (max N T), ?_⟩
  intro sol I A hsol t₁ ht₁ ht₁b hI hd₀ hDu' hA hΛ t ht
  have h := hsol.toIsSolutionOn
  have hd := hd₀.mono_radius (le_max_left R 0)
  have hR₀ : 0 ≤ R₀ := le_max_right R 0
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  obtain ⟨K, hv⟩ := h.exists_isC1FieldOn ht₁ hI
  have hDu : ∀ t ∈ Icc 0 t₁, ∀ x : ℝ^2, 0 ≤ x 1 → ‖velocityFieldDeriv sol t x‖ ≤ A t :=
    fun t ht x hx ↦ h.velocityFieldDeriv_eq ht₁ hI ht hx ▸ hDu' t ht x hx
  obtain ⟨Rq, Nq, hreg⟩ := hsol.holderData 0 t₁ hI
  obtain ⟨R₂, B, M, B₁, hω⟩ := h.exists_isC1VorticityHistory (M₁ := Nq) ht₁ hI hα.le hα1.le
    fun t ht y z hy hz ↦ (hreg t ht).holder_vorticity y z hy hz
  obtain ⟨K₁, K₂, hv₂⟩ := IsSolutionOn.isC2FieldOn_historyField hω hα hα1
  -- The lower-order bounds on `[0, t₁]`, with the constants of `[0, b]`.
  have hBt : N + t₁ * (N * E) ≤ Bω := by simp only [Bω]; gcongr
  have hBω : ∀ s ∈ Icc 0 t₁, ∀ x : ℝ^2, 0 ≤ x 1 → |sol.vorticity x s| ≤ Bω := fun s hs x hx ↦
    (h.abs_vorticity_le ht₁ hI hv hA hDu hΛ hd hs hx).trans
      ((by gcongr; exact hs.2 : N + s * (N * E) ≤ _).trans hBt)
  have hsupp : R₀ + (N + t₁ * (N * E)) * (1 + 2 * E ^ 2 * R₀ ^ 2) * t₁ ≤ R₁ := by
    have hBω0 : 0 ≤ Bω := (by positivity : 0 ≤ N + t₁ * (N * E)).trans hBt
    simp only [R₁]
    gcongr
  have hR₁0 : 0 ≤ R₁ := hR₀.trans ((le_add_of_nonneg_right (by positivity)).trans hsupp)
  have hR₁ : ∀ s ∈ Icc 0 t₁, ∀ x : ℝ^2, 0 ≤ x 1 → R₁ < ‖x‖ →
      sol.vorticity x s = 0 ∧ sol.temperature x s = 0 := fun s hs x hx hxR ↦
    h.eq_zero_of_norm ht₁ hI hv hA hDu hΛ hd hs hR₀ hx (hsupp.trans_lt hxR)
  have hfd (s : ℝ) (hs : s ∈ Icc 0 t₁) {x : ℝ^2} (hx : 0 ≤ x 1) :
      fderiv ℝ (fun y ↦ sol.temperature y s) x =
        fderivWithin ℝ (fun y ↦ sol.temperature y s) H̄ x :=
    IsSolutionOn.fderiv_eq_fderivWithin
      ((h.contDiff_temperature (hI hs)).differentiable one_ne_zero) hx
  have hGθ : ∀ s ∈ Icc 0 t₁, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderivWithin ℝ (fun x ↦ sol.temperature x s) H̄ x‖ ≤ N * E := fun s hs x hx ↦
    hfd s hs hx ▸ h.norm_fderiv_temperature_le ht₁ hI hv hA hDu hΛ hd hs hx
  have hMω : ∀ s ∈ Icc 0 t₁, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      |sol.vorticity y s - sol.vorticity z s| ≤ vorticityHolderBound α N Λ b * ‖y - z‖ ^ α :=
    fun s hs y z hy hz ↦
      (h.holder_bound ht₁ hI hv hA hDu hΛ hα hα1 hd hreg hs hy hz).1.trans
        (mul_le_mul_of_nonneg_right (vorticityHolderBound_le hα hα1 hN ht₁.le ht₁b)
          (Real.rpow_nonneg (norm_nonneg _) α))
  have hQθ : ∀ s ∈ Icc 0 t₁, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderivWithin ℝ (fun x ↦ sol.temperature x s) H̄ y -
        fderivWithin ℝ (fun x ↦ sol.temperature x s) H̄ z‖ ≤
          gradientHolderBound α N Λ b * ‖y - z‖ ^ α := fun s hs y z hy hz ↦ by
    rw [← hfd s hs hy, ← hfd s hs hz]
    exact (h.holder_bound ht₁ hI hv hA hDu hΛ hα hα1 hd hreg hs hy hz).2.trans
      (mul_le_mul_of_nonneg_right (gradientHolderBound_le hα hα1 hN ht₁.le ht₁b)
        (Real.rpow_nonneg (norm_nonneg _) α))
  -- The top-order bounds.
  have htop (y z : ℝ^2) (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :=
    h.top_bound ht₁ hI hv hω hα hα1 hv₂ hreg hA hDu hΛ hd hR₁0
      (fun s hs x hx hxR ↦ (hR₁ s hs x hx hxR).1) hBω hMω hGθ hQθ ht₁b ht hy hz
  have hT : T ≤ max (max Bω (N * E)) (max N T) := (le_max_right _ _).trans (le_max_right _ _)
  have hα0 (y z : ℝ^2) : 0 ≤ ‖y - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  exact
    { vorticity_contDiffOn := (hreg t ht).vorticity_contDiffOn
      temperature_contDiffOn := (hreg t ht).temperature_contDiffOn
      eq_zero := fun x hx hxR ↦ hR₁ t ht x hx hxR
      abs_vorticity_le := fun x hx ↦
        (hBω t ht x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
      norm_fderivWithin_vorticity_le := fun x hx ↦ (htop x x hx hx).1.trans hT
      holder_vorticity := fun y z hy hz ↦
        (htop y z hy hz).2.2.1.trans (mul_le_mul_of_nonneg_right hT (hα0 y z))
      abs_temperature_le := fun x hx ↦
        (h.abs_temperature_le hI hv hd ht hx).trans ((le_max_left _ _).trans (le_max_right _ _))
      norm_fderivWithin_temperature_le := fun x hx ↦
        (hGθ t ht x hx).trans ((le_max_right _ _).trans (le_max_left _ _))
      norm_fderivWithin_fderivWithin_temperature_le := fun x hx ↦ (htop x x hx hx).2.1.trans hT
      holder_temperature := fun y z hy hz ↦
        (htop y z hy hz).2.2.2.trans (mul_le_mul_of_nonneg_right hT (hα0 y z)) }

end Boussinesq.HalfPlane
