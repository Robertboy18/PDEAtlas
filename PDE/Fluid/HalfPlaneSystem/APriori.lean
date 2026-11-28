/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.APrioriTopBounds
public import PDE.Fluid.HalfPlaneSystem.Canonical
public import PDE.Fluid.Boussinesq.HalfPlane.APriori

/-!
# The a priori estimate of a half-plane system

A solution of a transport system with a nonlocal velocity can be continued as long as its highest
norms stay bounded. This module proves the four integral inequalities that control the gradient of
the vorticity, the Hessian of the temperature and their Hölder constants by the time integral of the
velocity gradient, for the half-plane system with a general velocity law. The inequality is not
closed here: the monotone bound `Y` below is a hypothesis, and `APrioriEstimate.lean` closes it.

Consider a solution on `[0, b]` of the half-plane system with the velocity law `U` (with the
Schauder estimate `IsHolderVelocityLaw U R₀ Ch` for the Hölder constants) and the forcing
coefficient `κ`, whose vorticity is a `C^{1,α}` history, whose slices are of the class
`IsHolderData` and whose velocity gradient on the closed half-plane `H̄` is bounded by `A t` with
`∫₀ᵇ A ≤ Λ`. The lower-order quantities (support, values, temperature gradient) and the Hölder
constants of the vorticity and of the temperature gradient are bounded by the transport of the data
(`APrioriLower.lean`, `APrioriHolder.lean`). The top-order quantities, the gradient of the vorticity
and the Hessian of the temperature with their Hölder constants, are bounded through their
transported equations along the trajectories of the field of the law (`APrioriTop.lean`,
`APrioriTopBounds.lean`).

Let `Y(s)` be a monotone bound of the four top-order quantities up to the time `s`. This module
bounds each of them at a time `r` by a constant plus a constant times `∫₀ʳ Y`. The reason is that
the second derivatives of the velocity enter only linearly, through the bounds `C 1 α (B + Y)` of
their size and of their Hölder constant, and the Hölder constant of the velocity gradient is of
lower order, `Ch α (M + B)`. The flow and its labels are `exp Λ`-Lipschitz, which gives the powers
of `exp Λ`. The four inequalities add up to `Y(s) ≤ c + C ∫₀ˢ Y` with `c = topConst` and
`C = topRate`, and Grönwall's inequality gives `topBound`. The constants are explicit but not
optimized. The support radius of the conclusion is the transported one; it may exceed `R₀`, in which
case the support bound of the class `IsSolutionOn` is the relevant one.

## Main results

Here `N` bounds the data, `Bω`, `Mω`, `Gθ`, `Qθ` are the lower-order bounds, and `b ≤ L`.

* `IsSolutionOn.norm_vorticityGradient_le`: `‖Dω_r‖ ≤ (N + Gθ Bκ₁ L + Bκ₀ ∫₀ʳ Y) exp Λ` on `H̄`.
* `IsSolutionOn.norm_hessian_le`: `‖D²θ_r‖ ≤ (N + Gθ C₁ Bω L + Gθ C₁ ∫₀ʳ Y) exp (2Λ)` on `H̄`,
  `C₁ = C 1 α`.
* `IsSolutionOn.norm_vorticityGradient_sub_le`, `IsSolutionOn.norm_hessian_sub_le`: the `α`-Hölder
  constants of `Dω_r` and of `D²θ_r` on `H̄`, of the same form.
* `IsSolutionOn.norm_lawFieldDeriv₂_le`, `IsSolutionOn.norm_lawFieldDeriv₂_sub_le`: the second
  derivatives of the field of the law at the time `ρ` are bounded by `C 1 α (Bω + Y ρ)` and are
  `α`-Hölder with the same constant.
* `IsSolutionOn.norm_flowOn_lawField_sub_le`, `IsSolutionOn.norm_label_lawField_sub_le`: the flow of
  the field of the law and its labels are `exp Λ`-Lipschitz on `H̄`.
* `topConst`, `topRate`, `topBound`: the constants `c`, `C` and the bound `c (1 + C L exp (C L))`.

`APrioriEstimate.lean` closes the inequality and proves the a priori estimate, and
`Continuation.lean` derives the continuation criterion from it. The library has the same estimate
for the Biot-Savart law of the half-plane and `κ = 1`
(`Boussinesq.HalfPlane.exists_holderData_bound`).
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE IncompressibleFlow PDE.Hyperbolic.Transport
  Boussinesq.HalfPlane
open scoped Topology NNReal

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The constant term `c` of the closed inequality `Y ≤ c + C ∫ Y` of the top-order bounds, with
`c₁ = C 1 α`, `E = exp Λ`, `B`, `G`, `Q` the bounds of the vorticity, of the temperature gradient
and of its Hölder constant, and `L` a bound of the length of the interval of times. -/
def topConst (c₁ : ℝ) (Bκ : ℕ → ℝ) (N Λ L B G Q : ℝ) : ℝ :=
  N * Real.exp Λ + G * Bκ 1 * L * Real.exp Λ + N * Real.exp Λ ^ 2 +
    G * c₁ * B * L * Real.exp Λ ^ 2 + N * Real.exp Λ ^ 2 +
    (Q * Bκ 1 + G * forcingHolderConst Bκ 1) * L * Real.exp Λ ^ 3 + N * Real.exp Λ ^ 3 +
    (Q + G) * c₁ * B * L * Real.exp Λ ^ 4

/-- The rate `C` of the closed inequality `Y ≤ c + C ∫ Y` of the top-order bounds, with
`c₁ = C 1 α`, `c = Ch α`, `E = exp Λ`, `B`, `M`, `G`, `Q` the bounds of the vorticity and of its
Hölder constant, of the temperature gradient and of its Hölder constant. -/
def topRate (c₁ c : ℝ) (Bκ : ℕ → ℝ) (Λ B M G Q : ℝ) : ℝ :=
  Bκ 0 * Real.exp Λ + G * c₁ * Real.exp Λ ^ 2 +
    (Bκ 0 + forcingHolderConst Bκ 0 + c * (M + B)) * Real.exp Λ ^ 3 +
    (2 * c * (M + B) + (Q + G) * c₁) * Real.exp Λ ^ 4

/-- The top-order bound `c (1 + C L exp (C L))`: a bound of the gradient of the vorticity, of the
Hessian of the temperature and of their `α`-Hölder constants on `[0, b]`, `b ≤ L`. -/
def topBound (c₁ c : ℝ) (Bκ : ℕ → ℝ) (N Λ L B M G Q : ℝ) : ℝ :=
  topConst c₁ Bκ N Λ L B G Q *
    (1 + topRate c₁ c Bκ Λ B M G Q * L * Real.exp (topRate c₁ c Bκ Λ B M G Q * L))

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}
  {Ch : ℝ → ℝ}

namespace IsSolutionOn

variable {sol : Fields} {I : Set ℝ} {b : ℝ}

set_option quotPrecheck false in
/-- The field of the law at the vorticity history. -/
local notation "𝐯" => lawField U fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- Its spatial derivative. -/
local notation "𝐃𝐯" => lawFieldDeriv U fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- Its second spatial derivative. -/
local notation "𝐃²𝐯" => lawFieldDeriv₂ U fun t x ↦ sol.vorticity x t

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

variable {α R B M B₁ M₁ Λ : ℝ} {K K₁ K₂ : ℝ≥0} {A : ℝ → ℝ}
  (hU : IsVelocityLaw U R₀ C) (hUh : IsHolderVelocityLaw U R₀ Ch)
  (h : IsSolutionOn U κ R₀ sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b K)
  (hω : IsC1VorticityHistory (fun t x ↦ sol.vorticity x t) 0 b α R B M B₁ M₁) (hR : R ≤ R₀)
  (hα : 0 < α) (hα1 : α < 1)
  (hv₂ : IsC2FieldOn (lawField U fun t x ↦ sol.vorticity x t)
    (lawFieldDeriv U fun t x ↦ sol.vorticity x t)
    (lawFieldDeriv₂ U fun t x ↦ sol.vorticity x t) 0 b K₁ K₂)
  (hA : ContinuousOn A (Icc 0 b))
  (hDu : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖velocityFieldDeriv U sol t x‖ ≤ A t)
  (hΛ : ∫ t in (0)..b, A t ≤ Λ)

include hU h hb hI hω hR hα hα1 hDu in
/-- The bound of the derivative of the field of the history on the closed half-plane. -/
theorem norm_lawFieldDeriv_le :
    ∀ ρ ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖𝐃𝐯 ρ x‖ ≤ A ρ := fun ρ hρ x hx ↦ by
  rw [← h.velocityFieldDeriv_eq_lawFieldDeriv hU hb hI hω hR hα hα1 hρ hx]
  exact hDu ρ hρ x hx

include hU h hb hI hv hω hR hv₂ hA hDu hΛ in
/-- The flow of the history is `exp Λ`-Lipschitz on the closed half-plane. -/
theorem norm_flowOn_lawField_sub_le {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) {a a' : ℝ^2} (ha : 0 ≤ a 1)
    (ha' : 0 ≤ a' 1) : ‖𝐗 ρ a - 𝐗 ρ a'‖ ≤ Real.exp Λ * ‖a - a'‖ := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  rw [← flowOn_eq_lawField hU hv hω hR hL hρ h0 ha, ← flowOn_eq_lawField hU hv hω hR hL hρ h0 ha']
  exact h.norm_trajectory_sub_le hU hb hI hv hA hDu hΛ hρ ha ha'

include hU hω hR hv₂ in
/-- The label of a point of the closed half-plane for the flow of the history lies in the
closed half-plane, and its trajectory passes through the point. -/
theorem label_lawField {r : ℝ} (hr : r ∈ Icc 0 b) (hb : 0 ≤ b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    0 ≤ (flowOn 𝐯 0 b 0 r y) 1 ∧ 𝐗 r (flowOn 𝐯 0 b 0 r y) = y := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  exact ⟨mapsTo_flowOn_lawField hU hω hR hL 0 h0 r hr hy, hL.flowOn_flowOn_self h0 hr y⟩

include hU h hb hI hv hω hR hv₂ hA hDu hΛ in
/-- The labels of the flow of the history are `exp Λ`-Lipschitz on the closed half-plane. -/
theorem norm_label_lawField_sub_le {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) : ‖flowOn 𝐯 0 b 0 r y - flowOn 𝐯 0 b 0 r z‖ ≤ Real.exp Λ * ‖y - z‖ := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  rw [← flowOn_eq_lawField hU hv hω hR hL h0 hr hy, ← flowOn_eq_lawField hU hv hω hR hL h0 hr hz]
  exact h.norm_label_sub_le hU hb hI hv hA hDu hΛ hr hy hz

include hU hUh h hb hI hω hR hα hα1 in
/-- The derivative of the field of the history is `α`-Hölder on the closed half-plane with
constant `Ch α (M + B)` when the vorticity is `α`-Hölder with constant `M` and bounded by `B`. -/
theorem norm_lawFieldDeriv_sub_le {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) {Mω Bω : ℝ}
    (hMω : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      |sol.vorticity y ρ - sol.vorticity z ρ| ≤ Mω * ‖y - z‖ ^ α)
    (hBω : ∀ y : ℝ^2, 0 ≤ y 1 → |sol.vorticity y ρ| ≤ Bω)
    {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    ‖𝐃𝐯 ρ x - 𝐃𝐯 ρ x'‖ ≤ Ch α * (Mω + Bω) * ‖x - x'‖ ^ α := by
  rw [← h.velocityFieldDeriv_eq_lawFieldDeriv hU hb hI hω hR hα hα1 hρ hx,
    ← h.velocityFieldDeriv_eq_lawFieldDeriv hU hb hI hω hR hα hα1 hρ hx']
  exact norm_velocityFieldDeriv_sub_le hU hUh h hb hI hα hα1 hρ hMω hBω hx hx'

include hU h hb hI hv hω hR hα hα1 hv₂ hA hDu hΛ in
/-- `‖X(ρ, a) - X(ρ, a')‖^α ≤ exp Λ ‖a - a'‖^α` for labels in the closed half-plane. -/
theorem rpow_norm_flowOn_sub_le {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) {a a' : ℝ^2} (ha : 0 ≤ a 1)
    (ha' : 0 ≤ a' 1) : ‖𝐗 ρ a - 𝐗 ρ a'‖ ^ α ≤ Real.exp Λ * ‖a - a'‖ ^ α :=
  (Real.rpow_le_rpow (norm_nonneg _)
    (h.norm_flowOn_lawField_sub_le hU hb hI hv hω hR hv₂ hA hDu hΛ hρ ha ha') hα.le).trans
    (mul_rpow_le_mul (Real.one_le_exp (zero_le_Λ hb hDu hΛ)) (norm_nonneg _) hα1.le)

include hU h hb hI hv hω hR hα hα1 hv₂ hA hDu hΛ in
/-- `‖Y(r, y) - Y(r, z)‖^α ≤ exp Λ ‖y - z‖^α` for the labels at the time `r`. -/
theorem rpow_norm_label_sub_le {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) :
    ‖flowOn 𝐯 0 b 0 r y - flowOn 𝐯 0 b 0 r z‖ ^ α ≤ Real.exp Λ * ‖y - z‖ ^ α :=
  (Real.rpow_le_rpow (norm_nonneg _)
    (h.norm_label_lawField_sub_le hU hb hI hv hω hR hv₂ hA hDu hΛ hr hy hz) hα.le).trans
    (mul_rpow_le_mul (Real.one_le_exp (zero_le_Λ hb hDu hΛ)) (norm_nonneg _) hα1.le)

end Flow

section Top

variable {α R B M B₁ M₁ Λ Rd N Rq Nq Bω Mω Gθ Qθ L : ℝ} {K K₁ K₂ : ℝ≥0} {A Y : ℝ → ℝ}
  (hU : IsVelocityLaw U R₀ C) (hUh : IsHolderVelocityLaw U R₀ Ch)
  (hκ : IsForcingCoefficient κ Bκ)
  (h : IsSolutionOn U κ R₀ sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b K)
  (hω : IsC1VorticityHistory (fun t x ↦ sol.vorticity x t) 0 b α R B M B₁ M₁) (hR : R ≤ R₀)
  (hα : 0 < α) (hα1 : α < 1)
  (hv₂ : IsC2FieldOn (lawField U fun t x ↦ sol.vorticity x t)
    (lawFieldDeriv U fun t x ↦ sol.vorticity x t)
    (lawFieldDeriv₂ U fun t x ↦ sol.vorticity x t) 0 b K₁ K₂)
  (hreg : ∀ t ∈ Icc 0 b,
    IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α Rq Nq)
  (hA : ContinuousOn A (Icc 0 b))
  (hDu : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖velocityFieldDeriv U sol t x‖ ≤ A t)
  (hΛ : ∫ t in (0)..b, A t ≤ Λ)
  (hd : IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α Rd N)
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

include h hI hBω hY₁ hY₃ in
/-- The level-one data of the vorticity at the time `ρ`, with the bound `Bω + Y ρ`, and a support
radius less than `R₀`. -/
theorem levelOne_data {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) :
    (∃ R' < R₀, ∀ y : ℝ^2, 0 ≤ y 1 → R' < ‖y‖ → sol.vorticity y ρ = 0) ∧
    (∀ j ≤ 1, ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖iteratedFDerivWithin ℝ j (fun x ↦ sol.vorticity x ρ) H̄ y‖ ≤ Bω + Y ρ) ∧
    ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ 1 (fun x ↦ sol.vorticity x ρ) H̄ y -
        iteratedFDerivWithin ℝ 1 (fun x ↦ sol.vorticity x ρ) H̄ z‖ ≤ (Bω + Y ρ) * ‖y - z‖ ^ α := by
  have hBω0 : 0 ≤ Bω := (abs_nonneg _).trans (hBω ρ hρ 0 (by simp))
  have hY0' : 0 ≤ Y ρ := (norm_nonneg _).trans (hY₁ ρ hρ 0 (by simp))
  refine ⟨h.exists_vorticity_eq_zero (hI hρ), fun j hj y hy ↦ ?_, fun y z hy hz ↦ ?_⟩
  · interval_cases j
    · rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
      exact (hBω ρ hρ y hy).trans (by linarith)
    · rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper y hy)]
      exact (hY₁ ρ hρ y hy).trans (by linarith)
  · rw [norm_iteratedFDerivWithin_one_sub _ hy hz]
    exact (hY₃ ρ hρ y z hy hz).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) α))

include hU h hI hω hR hα hα1 hreg hBω hY₁ hY₃ in
/-- **The bound of the second derivatives of the field** at the time `ρ`:
`‖D²v(ρ, x)‖ ≤ C 1 α (Bω + Y ρ)`. -/
theorem norm_lawFieldDeriv₂_le {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖𝐃²𝐯 ρ x‖ ≤ C 1 α * (Bω + Y ρ) := by
  obtain ⟨⟨R', hR', hz⟩, hN, hM⟩ := h.levelOne_data hI hBω hY₁ hY₃ hρ
  rw [lawFieldDeriv₂_eq hU hω hR hα hα1 hρ hx, ← norm_iteratedFDerivWithin_two _ hx]
  exact hU.norm_iteratedFDerivWithin_le (k := 1) le_rfl hα hα1 hR'.le
    (by exact_mod_cast (hreg ρ hρ).vorticity_contDiffOn) hz hN hM 2 le_rfl x hx

include hU h hI hω hR hα hα1 hreg hBω hY₁ hY₃ in
/-- **The Hölder bound of the second derivatives of the field** at the time `ρ`, with constant
`C 1 α (Bω + Y ρ)`. -/
theorem norm_lawFieldDeriv₂_sub_le {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) {x x' : ℝ^2} (hx : 0 ≤ x 1)
    (hx' : 0 ≤ x' 1) :
    ‖𝐃²𝐯 ρ x - 𝐃²𝐯 ρ x'‖ ≤ C 1 α * (Bω + Y ρ) * ‖x - x'‖ ^ α := by
  obtain ⟨⟨R', hR', hz⟩, hN, hM⟩ := h.levelOne_data hI hBω hY₁ hY₃ hρ
  have hh := hU.holder_iteratedFDerivWithin (k := 1) le_rfl hα hα1 hR'.le
    (by exact_mod_cast (hreg ρ hρ).vorticity_contDiffOn) hz hN hM x x' hx hx'
  rw [norm_iteratedFDerivWithin_succ_sub _ hx hx' 1, norm_iteratedFDerivWithin_one_sub _ hx hx']
    at hh
  rw [lawFieldDeriv₂_eq hU hω hR hα hα1 hρ hx, lawFieldDeriv₂_eq hU hω hR hα hα1 hρ hx']
  exact hh

include hU hκ h hb hI hv hω hR hα hα1 hv₂ hreg hA hDu hΛ hd hGθ hbL hYm hY₂ in
/-- **The gradient of the vorticity at the time `r`:**
`‖Dω_r‖ ≤ (N + Gθ Bκ₁ L + Bκ₀ ∫₀ʳ Y) exp Λ` on the closed half-plane. It is one of the four
inequalities that close the top-order estimate. Proof: Grönwall's inequality for the gradient
along the trajectory through `y`, whose forcing `κ D²θ[·, e₀] + ∂₀θ Dκ` is at most
`Bκ₀ Y + Gθ Bκ₁`. -/
theorem norm_vorticityGradient_le {r : ℝ} (hr : r ∈ Icc 0 b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖fderivWithin ℝ (fun x ↦ sol.vorticity x r) H̄ y‖ ≤
      (N + Gθ * Bκ 1 * L + Bκ 0 * ∫ ρ in (0)..r, Y ρ) * Real.exp (1 * Λ) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  obtain ⟨ha, hya⟩ := label_lawField hU hω hR hv₂ hr hb.le hy
  set a := flowOn 𝐯 0 b 0 r y
  have hsub : Icc 0 r ⊆ Icc 0 b := Icc_subset_Icc le_rfl hr.2
  have hGθ0 : 0 ≤ Gθ := (norm_nonneg _).trans (hGθ 0 h0 0 (by simp))
  have hB1 : 0 ≤ Bκ 1 := hκ.bound_nonneg 1
  have hB0 : 0 ≤ Bκ 0 := hκ.bound_nonneg 0
  have hgm : ∀ ρ ∈ Icc 0 r, |κ (𝐗 ρ a)| * ‖𝐇 ρ a‖ + ‖𝐆 ρ a‖ * ‖fderiv ℝ κ (𝐗 ρ a)‖ ≤
      Gθ * Bκ 1 + Bκ 0 * Y ρ := by
    intro ρ hρ
    have hρ' := hsub hρ
    have hX := mapsTo_flowOn_lawField hU hω hR hL ρ hρ' 0 h0 ha
    have e1 : |κ (𝐗 ρ a)| * ‖𝐇 ρ a‖ ≤ Bκ 0 * Y ρ :=
      mul_le_mul (hκ.abs_le _) (hY₂ ρ hρ' _ hX) (ContinuousLinearMap.opNorm_nonneg _) hB0
    have e2 : ‖𝐆 ρ a‖ * ‖fderiv ℝ κ (𝐗 ρ a)‖ ≤ Gθ * Bκ 1 :=
      mul_le_mul (hGθ ρ hρ' _ hX) (hκ.norm_fderiv_le _) (norm_nonneg _) hGθ0
    linarith
  have key := h.norm_vorticityGradient_flowOn_le hU hκ hb hI hv hω hR hα hα1 hv₂ hreg hA
    (h.norm_lawFieldDeriv_le hU hb hI hω hR hα hα1 hDu) hΛ ha hr
    (intervalIntegrable_add_mul hYm hr) hgm
  rw [hya] at key
  have hN := hd.norm_fderivWithin_vorticity_le a ha
  have hint := integral_add_mul_le (C := Bκ 0) hYm (by positivity : 0 ≤ Gθ * Bκ 1) hr
  have hbL' : Gθ * Bκ 1 * b ≤ Gθ * Bκ 1 * L := mul_le_mul_of_nonneg_left hbL (by positivity)
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  linarith

include hU h hb hI hv hω hR hα hα1 hv₂ hreg hA hDu hΛ hd hBω hGθ hbL hYm hY₁ hY₃ in
/-- **The Hessian of the temperature at the time `r`:**
`‖D²θ_r‖ ≤ (N + Gθ C₁ Bω L + Gθ C₁ ∫₀ʳ Y) exp (2Λ)` on the closed half-plane, `C₁ = C 1 α`.
Proof: Grönwall's inequality for the Hessian along the trajectory through `y`, whose forcing
`Dθ ∘ D²u` is at most `Gθ C₁ (Bω + Y)` by the bound of the second derivatives of the field. -/
theorem norm_hessian_le {r : ℝ} (hr : r ∈ Icc 0 b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ y‖ ≤
      (N + Gθ * C 1 α * Bω * L + Gθ * C 1 α * ∫ ρ in (0)..r, Y ρ) * Real.exp (2 * Λ) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  obtain ⟨ha, hya⟩ := label_lawField hU hω hR hv₂ hr hb.le hy
  set a := flowOn 𝐯 0 b 0 r y
  set k := C 1 α
  have hk : 0 ≤ k := hU.const_nonneg 1 α
  have hGθ0 : 0 ≤ Gθ := (norm_nonneg _).trans (hGθ 0 h0 0 (by simp))
  have hBω0 : 0 ≤ Bω := (abs_nonneg _).trans (hBω 0 h0 0 (by simp))
  have hsub : Icc 0 r ⊆ Icc 0 b := Icc_subset_Icc le_rfl hr.2
  have hgm : ∀ ρ ∈ Icc 0 r,
      ‖𝐆 ρ a‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖ ≤ Gθ * k * Bω + Gθ * k * Y ρ := by
    intro ρ hρ
    have hρ' := hsub hρ
    have hX := mapsTo_flowOn_lawField hU hω hR hL ρ hρ' 0 h0 ha
    calc ‖𝐆 ρ a‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖ ≤ Gθ * (k * (Bω + Y ρ)) :=
          mul_le_mul (hGθ ρ hρ' _ hX)
            (h.norm_lawFieldDeriv₂_le hU hI hω hR hα hα1 hreg hBω hY₁ hY₃ hρ' hX)
            (ContinuousLinearMap.opNorm_nonneg _) hGθ0
      _ = Gθ * k * Bω + Gθ * k * Y ρ := by ring
  have key := h.norm_hessian_flowOn_le hU hb hI hv hω hR hv₂ hreg hA
    (h.norm_lawFieldDeriv_le hU hb hI hω hR hα hα1 hDu) hΛ ha hr
    (intervalIntegrable_add_mul hYm hr) hgm
  rw [hya] at key
  have hN := hd.norm_fderivWithin_fderivWithin_temperature_le a ha
  have hint := integral_add_mul_le (C := Gθ * k) hYm (by positivity : 0 ≤ Gθ * k * Bω) hr
  have hbL' : Gθ * k * Bω * b ≤ Gθ * k * Bω * L := mul_le_mul_of_nonneg_left hbL (by positivity)
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  linarith

include hU hUh hκ h hb hI hv hω hR hα hα1 hv₂ hreg hA hDu hΛ hd hBω hMω hGθ hQθ hbL hYm hY0 hY₁
  hY₂ hY₄ in
/-- **The Hölder constant of the gradient of the vorticity at the time `r`:** with
`K₁ = Qθ Bκ₁ + Gθ max (Bκ 2) (2 Bκ 1)` and
`C₄ = Bκ₀ + max (Bκ 1) (2 Bκ 0) + Ch α (Mω + Bω)`, the gradient is `α`-Hölder on the closed
half-plane with constant `(N + exp Λ (K₁ L + C₄ ∫₀ʳ Y)) exp Λ exp Λ`. Proof: Grönwall's
inequality for the difference of the gradients along the trajectories of two labels. Every term
of the forcing is a product with one Hölder difference, and the flow and the labels are
`exp Λ`-Lipschitz. -/
theorem norm_vorticityGradient_sub_le {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) :
    ‖fderivWithin ℝ (fun x ↦ sol.vorticity x r) H̄ y -
        fderivWithin ℝ (fun x ↦ sol.vorticity x r) H̄ z‖ ≤
      (N + Real.exp Λ * ((Qθ * Bκ 1 + Gθ * forcingHolderConst Bκ 1) * L +
        (Bκ 0 + forcingHolderConst Bκ 0 + Ch α * (Mω + Bω)) * ∫ ρ in (0)..r, Y ρ)) *
        Real.exp (1 * Λ) * (Real.exp Λ * ‖y - z‖ ^ α) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  obtain ⟨ha, hya⟩ := label_lawField hU hω hR hv₂ hr hb.le hy
  obtain ⟨ha', hza⟩ := label_lawField hU hω hR hv₂ hr hb.le hz
  have hlab := h.rpow_norm_label_sub_le hU hb hI hv hω hR hα hα1 hv₂ hA hDu hΛ hr hy hz
  set a := flowOn 𝐯 0 b 0 r y
  set a' := flowOn 𝐯 0 b 0 r z
  set c := Ch α
  set E := Real.exp Λ
  set Hκ := forcingHolderConst Bκ 0
  set Hκ' := forcingHolderConst Bκ 1
  have hc : 0 ≤ c := hUh.const_nonneg hα hα1
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hGθ0 : 0 ≤ Gθ := (norm_nonneg _).trans (hGθ 0 h0 0 (by simp))
  have hBω0 : 0 ≤ Bω := (abs_nonneg _).trans (hBω 0 h0 0 (by simp))
  have hMω0 : 0 ≤ Mω := nonneg_of_norm_sub_le (F := fun x ↦ sol.vorticity x 0) (α := α)
    fun y z hy hz ↦ by rw [Real.norm_eq_abs]; exact hMω 0 h0 y z hy hz
  have hQθ0 : 0 ≤ Qθ := nonneg_of_norm_sub_le (hQθ 0 h0)
  have hB0 : 0 ≤ Bκ 0 := hκ.bound_nonneg 0
  have hB1 : 0 ≤ Bκ 1 := hκ.bound_nonneg 1
  have hHκ : 0 ≤ Hκ := hκ.forcingHolderConst_nonneg 0
  have hHκ' : 0 ≤ Hκ' := hκ.forcingHolderConst_nonneg 1
  have hL0 : 0 ≤ L := hb.le.trans hbL
  set d := E * ‖a - a'‖ ^ α
  have hd0 : 0 ≤ d := by positivity
  set K₁ := Qθ * Bκ 1 + Gθ * Hκ'
  set C₄ := Bκ 0 + Hκ + c * (Mω + Bω)
  have hK₁ : 0 ≤ K₁ := by positivity
  have hC₄ : 0 ≤ C₄ := by positivity
  have hsub : Icc 0 r ⊆ Icc 0 b := Icc_subset_Icc le_rfl hr.2
  -- The forcing of the difference of the gradients at the labels `a`, `a'` is at most
  -- `d (K₁ + C₄ Y)`, with `d = exp Λ ‖a - a'‖^α` the bound of the distance of the two particles
  -- to the power `α`: each product has one factor that is a Hölder difference.
  have hgm : ∀ ρ ∈ Icc 0 r,
      |κ (𝐗 ρ a)| * ‖𝐇 ρ a - 𝐇 ρ a'‖ + |κ (𝐗 ρ a) - κ (𝐗 ρ a')| * ‖𝐇 ρ a'‖ +
        ‖𝐆 ρ a - 𝐆 ρ a'‖ * ‖fderiv ℝ κ (𝐗 ρ a)‖ +
        ‖𝐆 ρ a'‖ * ‖fderiv ℝ κ (𝐗 ρ a) - fderiv ℝ κ (𝐗 ρ a')‖ +
        ‖𝐙 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖ ≤ d * K₁ + d * C₄ * Y ρ := by
    intro ρ hρ
    have hρ' := hsub hρ
    have hX := mapsTo_flowOn_lawField hU hω hR hL ρ hρ' 0 h0 ha
    have hX' := mapsTo_flowOn_lawField hU hω hR hL ρ hρ' 0 h0 ha'
    have hδ := h.rpow_norm_flowOn_sub_le hU hb hI hv hω hR hα hα1 hv₂ hA hDu hΛ hρ' ha ha'
    have hYρ := hY0 ρ hρ'
    have e1 : |κ (𝐗 ρ a)| * ‖𝐇 ρ a - 𝐇 ρ a'‖ ≤ Bκ 0 * (Y ρ * d) :=
      mul_le_mul (hκ.abs_le _) ((hY₄ ρ hρ' _ _ hX hX').trans
        (mul_le_mul_of_nonneg_left hδ hYρ)) (ContinuousLinearMap.opNorm_nonneg _) hB0
    have e2 : |κ (𝐗 ρ a) - κ (𝐗 ρ a')| * ‖𝐇 ρ a'‖ ≤ (Hκ * d) * Y ρ :=
      mul_le_mul ((hκ.abs_sub_le_rpow hα.le hα1.le _ _).trans
        (mul_le_mul_of_nonneg_left hδ hHκ)) (hY₂ ρ hρ' _ hX') (ContinuousLinearMap.opNorm_nonneg _)
        (by positivity)
    have e3 : ‖𝐆 ρ a - 𝐆 ρ a'‖ * ‖fderiv ℝ κ (𝐗 ρ a)‖ ≤ (Qθ * d) * Bκ 1 :=
      mul_le_mul ((hQθ ρ hρ' _ _ hX hX').trans (mul_le_mul_of_nonneg_left hδ hQθ0))
        (hκ.norm_fderiv_le _) (norm_nonneg _) (by positivity)
    have e4 : ‖𝐆 ρ a'‖ * ‖fderiv ℝ κ (𝐗 ρ a) - fderiv ℝ κ (𝐗 ρ a')‖ ≤ Gθ * (Hκ' * d) :=
      mul_le_mul (hGθ ρ hρ' _ hX') ((hκ.norm_fderiv_sub_le_rpow hα.le hα1.le _ _).trans
        (mul_le_mul_of_nonneg_left hδ hHκ')) (norm_nonneg _) hGθ0
    have e5 : ‖𝐙 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖ ≤ Y ρ * (c * (Mω + Bω) * d) :=
      mul_le_mul (hY₁ ρ hρ' _ hX')
        ((h.norm_lawFieldDeriv_sub_le hU hUh hb hI hω hR hα hα1 hρ' (hMω ρ hρ') (hBω ρ hρ')
          hX hX').trans (mul_le_mul_of_nonneg_left hδ (by positivity)))
        (norm_nonneg _) hYρ
    calc _ ≤ Bκ 0 * (Y ρ * d) + (Hκ * d) * Y ρ + (Qθ * d) * Bκ 1 + Gθ * (Hκ' * d) +
          Y ρ * (c * (Mω + Bω) * d) := by linarith
      _ = d * K₁ + d * C₄ * Y ρ := by simp only [K₁, C₄]; ring
  -- Grönwall's inequality along the two trajectories.
  have key := h.norm_vorticityGradient_flowOn_sub_le hU hκ hb hI hv hω hR hα hα1 hv₂ hreg hA
    (h.norm_lawFieldDeriv_le hU hb hI hω hR hα hα1 hDu) hΛ ha ha' hr
    (intervalIntegrable_add_mul hYm hr) hgm
  rw [hya, hza] at key
  -- The gradient of the datum is Hölder at the labels, and the labels are Hölder in `y`, `z`.
  have hdata := hd.holder_vorticity a a' ha ha'
  have hint := integral_add_mul_le (C := d * C₄) hYm (by positivity : 0 ≤ d * K₁) hr
  have hbL' : d * K₁ * b ≤ d * K₁ * L := mul_le_mul_of_nonneg_left hbL (by positivity)
  have hIY : 0 ≤ ∫ ρ in (0)..r, Y ρ :=
    intervalIntegral.integral_nonneg hr.1 fun ρ hρ ↦ hY0 ρ (hsub hρ)
  have hc0 : 0 ≤ (N + E * (K₁ * L + C₄ * ∫ ρ in (0)..r, Y ρ)) * Real.exp (1 * Λ) := by
    positivity
  calc _ ≤ _ := key
    _ ≤ (N * ‖a - a'‖ ^ α + (d * K₁ * L + d * C₄ * ∫ ρ in (0)..r, Y ρ)) *
          Real.exp (1 * Λ) :=
        mul_le_mul_of_nonneg_right (add_le_add hdata (hint.trans (by linarith)))
          (Real.exp_pos _).le
    _ = (N + E * (K₁ * L + C₄ * ∫ ρ in (0)..r, Y ρ)) * Real.exp (1 * Λ) * ‖a - a'‖ ^ α := by
        simp only [d]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlab hc0

include hU hUh h hb hI hv hω hR hα hα1 hv₂ hreg hA hDu hΛ hd hBω hMω hGθ hQθ hbL hYm hY0 hY₁
  hY₂ hY₃ in
/-- **The Hölder constant of the Hessian of the temperature at the time `r`:** with
`K₀ = (Qθ + Gθ) C₁ Bω` and `C₃ = 2 Ch α (Mω + Bω) + (Qθ + Gθ) C₁`, `C₁ = C 1 α`, the Hessian is
`α`-Hölder on the closed half-plane with constant `(N + exp Λ (K₀ L + C₃ ∫₀ʳ Y)) exp (2Λ) exp Λ`.
Proof: as for the gradient of the vorticity. The forcing of the difference has the terms
`H (Du(X) - Du(X'))`, `(G - G') D²u(X)` and `G' (D²u(X) - D²u(X'))`, bounded by the Schauder
estimate and by the Hölder bound of the second derivatives of the field. -/
theorem norm_hessian_sub_le {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) :
    ‖fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ y -
        fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ z‖ ≤
      (N + Real.exp Λ * ((Qθ + Gθ) * C 1 α * Bω * L +
        (2 * Ch α * (Mω + Bω) + (Qθ + Gθ) * C 1 α) * ∫ ρ in (0)..r, Y ρ)) * Real.exp (2 * Λ) *
        (Real.exp Λ * ‖y - z‖ ^ α) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hL := hv₂.toIsC1FieldOn.isLipschitzFieldOn
  obtain ⟨ha, hya⟩ := label_lawField hU hω hR hv₂ hr hb.le hy
  obtain ⟨ha', hza⟩ := label_lawField hU hω hR hv₂ hr hb.le hz
  have hlab := h.rpow_norm_label_sub_le hU hb hI hv hω hR hα hα1 hv₂ hA hDu hΛ hr hy hz
  set a := flowOn 𝐯 0 b 0 r y
  set a' := flowOn 𝐯 0 b 0 r z
  set k := C 1 α
  set c := Ch α
  set E := Real.exp Λ
  have hk : 0 ≤ k := hU.const_nonneg 1 α
  have hc : 0 ≤ c := hUh.const_nonneg hα hα1
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
  set K₀ := (Qθ + Gθ) * k * Bω
  set C₃ := 2 * c * (Mω + Bω) + (Qθ + Gθ) * k
  have hK₀ : 0 ≤ K₀ := by positivity
  have hC₃ : 0 ≤ C₃ := by positivity
  have hsub : Icc 0 r ⊆ Icc 0 b := Icc_subset_Icc le_rfl hr.2
  -- The forcing of the difference of the Hessians at the labels `a`, `a'` is at most
  -- `d (K₀ + C₃ Y)`, with `d = exp Λ ‖a - a'‖^α`: each product has one factor that is a Hölder
  -- difference.
  have hgm : ∀ ρ ∈ Icc 0 r,
      2 * ‖𝐇 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖ + ‖𝐆 ρ a - 𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖ +
        ‖𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a) - 𝐃²𝐯 ρ (𝐗 ρ a')‖ ≤ d * K₀ + d * C₃ * Y ρ := by
    intro ρ hρ
    have hρ' := hsub hρ
    have hX := mapsTo_flowOn_lawField hU hω hR hL ρ hρ' 0 h0 ha
    have hX' := mapsTo_flowOn_lawField hU hω hR hL ρ hρ' 0 h0 ha'
    have hδ := h.rpow_norm_flowOn_sub_le hU hb hI hv hω hR hα hα1 hv₂ hA hDu hΛ hρ' ha ha'
    have hYρ := hY0 ρ hρ'
    have e1 : ‖𝐇 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖ ≤ Y ρ * (c * (Mω + Bω) * d) :=
      mul_le_mul (hY₂ ρ hρ' _ hX')
        ((h.norm_lawFieldDeriv_sub_le hU hUh hb hI hω hR hα hα1 hρ' (hMω ρ hρ') (hBω ρ hρ')
          hX hX').trans (mul_le_mul_of_nonneg_left hδ (by positivity)))
        (norm_nonneg _) hYρ
    have e2 : ‖𝐆 ρ a - 𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖ ≤ (Qθ * d) * (k * (Bω + Y ρ)) :=
      mul_le_mul ((hQθ ρ hρ' _ _ hX hX').trans (mul_le_mul_of_nonneg_left hδ hQθ0))
        (h.norm_lawFieldDeriv₂_le hU hI hω hR hα hα1 hreg hBω hY₁ hY₃ hρ' hX)
        (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
    have e3 : ‖𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a) - 𝐃²𝐯 ρ (𝐗 ρ a')‖ ≤ Gθ * (k * (Bω + Y ρ) * d) :=
      mul_le_mul (hGθ ρ hρ' _ hX')
        ((h.norm_lawFieldDeriv₂_sub_le hU hI hω hR hα hα1 hreg hBω hY₁ hY₃ hρ' hX hX').trans
          (mul_le_mul_of_nonneg_left hδ (by positivity)))
        (ContinuousLinearMap.opNorm_nonneg _) hGθ0
    calc 2 * ‖𝐇 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖ +
          ‖𝐆 ρ a - 𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖ + ‖𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a) - 𝐃²𝐯 ρ (𝐗 ρ a')‖
        = 2 * (‖𝐇 ρ a'‖ * ‖𝐃𝐯 ρ (𝐗 ρ a) - 𝐃𝐯 ρ (𝐗 ρ a')‖) +
          ‖𝐆 ρ a - 𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a)‖ +
          ‖𝐆 ρ a'‖ * ‖𝐃²𝐯 ρ (𝐗 ρ a) - 𝐃²𝐯 ρ (𝐗 ρ a')‖ := by ring
      _ ≤ 2 * (Y ρ * (c * (Mω + Bω) * d)) + (Qθ * d) * (k * (Bω + Y ρ)) +
          Gθ * (k * (Bω + Y ρ) * d) := add_le_add (add_le_add (by linarith) e2) e3
      _ = d * K₀ + d * C₃ * Y ρ := by simp only [K₀, C₃]; ring
  -- Grönwall's inequality along the two trajectories.
  have key := h.norm_hessian_flowOn_sub_le hU hb hI hv hω hR hv₂ hreg hA
    (h.norm_lawFieldDeriv_le hU hb hI hω hR hα hα1 hDu) hΛ ha ha' hr
    (intervalIntegrable_add_mul hYm hr) hgm
  rw [hya, hza] at key
  -- The Hessian of the datum is Hölder at the labels, and the labels are Hölder in `y`, `z`.
  have hdata := hd.holder_temperature a a' ha ha'
  have hint := integral_add_mul_le (C := d * C₃) hYm (by positivity : 0 ≤ d * K₀) hr
  have hbL' : d * K₀ * b ≤ d * K₀ * L := mul_le_mul_of_nonneg_left hbL (by positivity)
  have hIY : 0 ≤ ∫ ρ in (0)..r, Y ρ :=
    intervalIntegral.integral_nonneg hr.1 fun ρ hρ ↦ hY0 ρ (hsub hρ)
  have hc0 : 0 ≤ (N + E * (K₀ * L + C₃ * ∫ ρ in (0)..r, Y ρ)) * Real.exp (2 * Λ) := by
    positivity
  calc _ ≤ _ := key
    _ ≤ (N * ‖a - a'‖ ^ α + (d * K₀ * L + d * C₃ * ∫ ρ in (0)..r, Y ρ)) *
          Real.exp (2 * Λ) :=
        mul_le_mul_of_nonneg_right (add_le_add hdata (hint.trans (by linarith)))
          (Real.exp_pos _).le
    _ = (N + E * (K₀ * L + C₃ * ∫ ρ in (0)..r, Y ρ)) * Real.exp (2 * Λ) * ‖a - a'‖ ^ α := by
        simp only [d]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlab hc0

end Top

end IsSolutionOn

end HalfPlaneSystem
