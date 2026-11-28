/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.APrioriLower
public import PDE.Fluid.Boussinesq.HalfPlane.APrioriHolder
import PDE.Analysis.Calculus.SliceDerivative
import PDE.Analysis.Calculus.HolderInterpolation

/-!
# Hölder bounds of the vorticity and of the temperature gradient

The velocity gradient of a transport system is not Lipschitz in general, so the Hölder constants of
the transported quantities are not bounded by the flow alone. This module bounds the Hölder
constants of the vorticity and of the temperature gradient by the time integral of the velocity
gradient, under a Schauder estimate of the velocity law.

Let `sol` solve the half-plane system with the velocity law `U` and the forcing coefficient `κ` on
`[0, b]`, with data of the class `IsHolderData … α R N`, `‖Du(t)‖ ≤ A t` on the closed half-plane
and `∫₀ᵇ A ≤ Λ`. The law is assumed to satisfy the Schauder estimate `IsHolderVelocityLaw U R₀ Ch`:
the derivative of the field of an `α`-Hölder datum with constant `M`, bounded by `B`, is `α`-Hölder
with constant `Ch α (M + B)`. The slices are assumed to be of the class `IsHolderData` with some
bounds; this hypothesis is qualitative: it makes the running suprema finite and does not enter the
constants, which are not optimized.

Along a trajectory the temperature gradient `G(a, r) = ∇θ(X(r, a), r)` equals `∇θ₀(a) ∘ W(r, a)`
with the inverse first variation `W`, so it solves `∂ᵣ G = -G ∘ Du(X)`
(`IsSolutionOn.hasDerivWithinAt_gradient`). For two labels the difference therefore obeys a linear
equation whose forcing is `G(a') ∘ (Du(X(a)) - Du(X(a')))`, controlled by the Hölder constant of the
vorticity through the Schauder estimate; in turn the vorticity along trajectories is the initial
vorticity plus the time integral of `κ ∂₀θ` (`IsSolutionOn.norm_vorticity_trajectory_sub_le`), whose
differences are controlled by the Hölder constant of the temperature gradient and the Hölder
constant `max (Bκ 1) (2 Bκ 0)` of `κ`. With the running suprema of the two Hölder quotients, which
are monotone in time, the coupled inequalities close by Grönwall's inequality for monotone
functions.

## Main results

* `IsHolderVelocityLaw`: the Schauder estimate of a velocity law, with constants `Ch α`.
* `isHolderVelocityLaw_halfPlaneVelocity`: the half-plane Biot-Savart law, the law of the Boussinesq
  system, satisfies it with `Ch α = 844/(α(1-α))`, for every radius `R₀`.
* `forcingHolderConst`, `IsForcingCoefficient.abs_sub_le_rpow`,
  `IsForcingCoefficient.norm_fderiv_sub_le_rpow`: for `α ∈ [0, 1]`, a forcing coefficient and its
  derivative are `α`-Hölder with the constants `max (Bκ 1) (2 Bκ 0)` and `max (Bκ 2) (2 Bκ 1)`.
* `IsSolutionOn.norm_velocityFieldDeriv_sub_le`: the velocity gradient of a solution is `α`-Hölder
  with constant `Ch α (M + B)` at a time where the vorticity is `α`-Hölder with constant `M` and
  bounded by `B`.
* `IsSolutionOn.norm_fderiv_temperature_sub_le`, `IsSolutionOn.abs_vorticity_sub_le`: the two
  coupled inequalities, for monotone bounds `M t` and `Q t` of the two Hölder constants.
* `IsSolutionOn.holder_bound`: at every time of `[0, b]`, `b ≤ L`, the vorticity is `α`-Hölder on
  the closed half-plane with constant `vorticityHolderBound (Ch α) Bκ N Λ L` and the temperature
  gradient with constant `gradientHolderBound (Ch α) Bκ N Λ L`.
* `vorticityBound`, `vorticityHolderBound`, `gradientHolderBound`: the bounds.

`APriori.lean` uses the Schauder estimate and the Hölder constants of the coefficient in the
top-order inequalities, and `APrioriEstimate.lean` uses `IsSolutionOn.holder_bound` in the a priori
estimate. `IsHolderVelocityLaw` is a hypothesis of the continuation criterion (`Continuation.lean`)
and of the theorem on maximal solutions (`PersistenceMaximal.lean`). For the Biot-Savart law the
library has `Boussinesq.HalfPlane.IsSolutionOn.holder_bound`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE IncompressibleFlow Boussinesq.HalfPlane
open scoped Topology NNReal

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- **The Schauder estimate of a velocity law** up to the radius `R₀`, with the constants
`Ch α`: for data continuous on the closed half-plane `H̄`, `α`-Hölder there with constant `M`,
bounded by `B` and vanishing there outside a disc of radius `R ≤ R₀`, the derivative within `H̄`
of the field is `α`-Hölder on `H̄` with constant `Ch α (M + B)`. -/
structure IsHolderVelocityLaw (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (R₀ : ℝ) (Ch : ℝ → ℝ) : Prop where
  /-- The constants are nonnegative. -/
  const_nonneg : ∀ {α : ℝ}, 0 < α → α < 1 → 0 ≤ Ch α
  /-- The Hölder bound of the derivative of the field. -/
  norm_fderivWithin_sub_le : ∀ {f : ℝ^2 → ℝ} {R B M α : ℝ}, 0 < α → α < 1 → R ≤ R₀ →
    ContinuousOn f H̄ → (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) →
    (∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α) →
    (∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ B) → ∀ x x' : ℝ^2, 0 ≤ x 1 → 0 ≤ x' 1 →
      ‖fderivWithin ℝ (U f) H̄ x - fderivWithin ℝ (U f) H̄ x'‖ ≤ Ch α * (M + B) * ‖x - x'‖ ^ α

/-- The half-plane Biot-Savart law satisfies the Schauder estimate with the constants
`844/(α(1-α))`, for every radius. -/
theorem isHolderVelocityLaw_halfPlaneVelocity (R₀ : ℝ) :
    IsHolderVelocityLaw halfPlaneVelocity R₀ fun α ↦ 844 / (α * (1 - α)) where
  const_nonneg hα hα1 := div_nonneg (by norm_num) (mul_nonneg hα.le (by linarith))
  norm_fderivWithin_sub_le {f R B M α} hα hα1 _ hf hR hM hB x x' hx hx' := by
    have hC : 0 ≤ 844 / (α * (1 - α)) := div_nonneg (by norm_num) (mul_nonneg hα.le (by linarith))
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (by simp))
    rw [← dist_eq_norm]
    refine (dist_fderivWithin_halfPlaneVelocity_le hf hR hα hα1 hM hx hx').trans ?_
    gcongr
    linarith

/-- The `α`-Hölder constant `max (Bκ (k + 1)) (2 Bκ k)` of the derivative of order `k` of a
forcing coefficient. -/
def forcingHolderConst (Bκ : ℕ → ℝ) (k : ℕ) : ℝ :=
  max (Bκ (k + 1)) (2 * Bκ k)

namespace IsForcingCoefficient

variable {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ} {α : ℝ}

/-- The coefficient is `α`-Hölder with constant `max (Bκ 1) (2 Bκ 0)`. -/
theorem abs_sub_le_rpow (hκ : IsForcingCoefficient κ Bκ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (p q : ℝ^2) : |κ p - κ q| ≤ forcingHolderConst Bκ 0 * ‖p - q‖ ^ α := by
  rw [← Real.norm_eq_abs, ← dist_eq_norm]
  exact PDE.Analysis.norm_sub_le_max_mul_rpow (S := univ)
    (fun x _ y _ ↦ by rw [Real.norm_eq_abs, dist_eq_norm]; exact hκ.abs_sub_le x y)
    (fun x _ ↦ by rw [Real.norm_eq_abs]; exact hκ.abs_le x) hα0 hα1 (mem_univ p) (mem_univ q)

/-- The derivative of the coefficient is `α`-Hölder with constant `max (Bκ 2) (2 Bκ 1)`. -/
theorem norm_fderiv_sub_le_rpow (hκ : IsForcingCoefficient κ Bκ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (p q : ℝ^2) :
    ‖fderiv ℝ κ p - fderiv ℝ κ q‖ ≤ forcingHolderConst Bκ 1 * ‖p - q‖ ^ α := by
  have h := PDE.Analysis.norm_sub_le_max_mul_rpow (S := univ) (f := fderiv ℝ κ)
    (fun x _ y _ ↦ by rw [dist_eq_norm]; exact hκ.norm_fderiv_sub_le x y)
    (fun x _ ↦ hκ.norm_fderiv_le x) hα0 hα1 (mem_univ p) (mem_univ q)
  rwa [dist_eq_norm] at h

/-- The Hölder constants of the coefficient are nonnegative. -/
theorem forcingHolderConst_nonneg (hκ : IsForcingCoefficient κ Bκ) (k : ℕ) :
    0 ≤ forcingHolderConst Bκ k :=
  (hκ.bound_nonneg _).trans (le_max_left _ _)

end IsForcingCoefficient

/-- The bound `N + L Bκ₀ N exp Λ` of the vorticity on `[0, b]`, `b ≤ L`. -/
def vorticityBound (Bκ : ℕ → ℝ) (N Λ L : ℝ) : ℝ :=
  N + L * (Bκ 0 * (N * Real.exp Λ))

/-- The constant term `2 N E² + N c E⁴ L B` of the bound of the Hölder constant of the
temperature gradient, `c = Ch α`, `E = exp Λ`, `B = vorticityBound`. -/
def gradientHolderConst (c : ℝ) (Bκ : ℕ → ℝ) (N Λ L : ℝ) : ℝ :=
  2 * N * Real.exp Λ ^ 2 + N * c * Real.exp Λ ^ 4 * L * vorticityBound Bκ N Λ L

/-- The constant term `2 N E + max (Bκ 1) (2 Bκ 0) N E³ L` of the bound of the Hölder constant of
the vorticity, `E = exp Λ`. -/
def vorticityHolderConst (Bκ : ℕ → ℝ) (N Λ L : ℝ) : ℝ :=
  2 * N * Real.exp Λ + forcingHolderConst Bκ 0 * N * Real.exp Λ ^ 3 * L

/-- The bound `c' (1 + C L exp (C L))` of the `α`-Hölder constant of the vorticity on `[0, b]`,
`b ≤ L`, with `c' = m + Bκ₀ E² L q`, `C = Bκ₀ E² L N c E⁴`, `m = vorticityHolderConst`,
`q = gradientHolderConst`, `c = Ch α`, `E = exp Λ`. -/
def vorticityHolderBound (c : ℝ) (Bκ : ℕ → ℝ) (N Λ L : ℝ) : ℝ :=
  (vorticityHolderConst Bκ N Λ L + Bκ 0 * Real.exp Λ ^ 2 * L * gradientHolderConst c Bκ N Λ L) *
    (1 + Bκ 0 * Real.exp Λ ^ 2 * L * (N * c * Real.exp Λ ^ 4) * L *
      Real.exp (Bκ 0 * Real.exp Λ ^ 2 * L * (N * c * Real.exp Λ ^ 4) * L))

/-- The bound `q + N c E⁴ L V` of the `α`-Hölder constant of the temperature gradient on
`[0, b]`, `b ≤ L`, with `q = gradientHolderConst`, `V = vorticityHolderBound`, `c = Ch α`,
`E = exp Λ`. -/
def gradientHolderBound (c : ℝ) (Bκ : ℕ → ℝ) (N Λ L : ℝ) : ℝ :=
  gradientHolderConst c Bκ N Λ L +
    N * c * Real.exp Λ ^ 4 * L * vorticityHolderBound c Bκ N Λ L

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}
  {Ch : ℝ → ℝ}

namespace IsSolutionOn

variable {sol : Fields} {I : Set ℝ} {b Λ : ℝ} {K : ℝ≥0} {A : ℝ → ℝ}

section Gradient

variable (hU : IsVelocityLaw U R₀ C) (h : IsSolutionOn U κ R₀ sol I) (hb : 0 < b)
  (hI : Icc 0 b ⊆ I) (hv : IsC1FieldOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b K)

include hU h hb hI hv in
/-- **The temperature gradient along a trajectory** is the initial gradient at the label composed
with the inverse first variation. -/
theorem fderiv_temperature_trajectory {r : ℝ} (hr : r ∈ Icc 0 b) {a : ℝ^2} (ha : 0 ≤ a 1) :
    fderiv ℝ (fun y ↦ sol.temperature y r) (trajectory U sol b r a) =
      (fderiv ℝ (fun y ↦ sol.temperature y 0) a).comp
        (variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b 0 r
          (trajectory U sol b r a)) := by
  have hL := hv.isLipschitzFieldOn
  have h1 := h.fderiv_temperature_eq hU hb hI hv hr (h.trajectory_mem hU hI hL hb.le hr ha)
  rwa [show label U sol b (trajectory U sol b r a) r = a from
    hL.flowOn_flowOn_self hr ⟨le_rfl, hb.le⟩ a] at h1

include hb hv in
/-- **The equation of the temperature gradient along a trajectory:**
`∂ᵣ (∇θ₀(a) ∘ W(r, a)) = -(∇θ₀(a) ∘ W(r, a)) ∘ Du(r, X(r, a))`. -/
theorem hasDerivWithinAt_gradient (L : ℝ^2 →L[ℝ] ℝ) (a : ℝ^2) {r : ℝ} (hr : r ∈ Icc 0 b) :
    HasDerivWithinAt (fun ρ ↦ L.comp (variationOn (velocityField U sol)
        (velocityFieldDeriv U sol) 0 b 0 ρ (trajectory U sol b ρ a)))
      (-(L.comp (variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b 0 r
        (trajectory U sol b r a))).comp (velocityFieldDeriv U sol r (trajectory U sol b r a)))
      (Icc 0 b) r := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hW := hv.hasDerivWithinAt_variationOn_inverse hr h0 a
  have hc := (hasDerivWithinAt_const r (Icc 0 b) L).clm_comp hW
  simpa [trajectory, ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_assoc] using hc

include hb hv in
/-- The temperature gradient along a trajectory, in the form `∇θ₀(a) ∘ W(r, a)`, is continuous
in time. -/
theorem continuousOn_gradient (L : ℝ^2 →L[ℝ] ℝ) (a : ℝ^2) :
    ContinuousOn (fun ρ ↦ L.comp (variationOn (velocityField U sol) (velocityFieldDeriv U sol)
      0 b 0 ρ (trajectory U sol b ρ a))) (Icc 0 b) := fun _ hr ↦
  (hasDerivWithinAt_gradient hb hv L a hr).continuousWithinAt

include hU h hb hI hv in
/-- **Two labels: the vorticity.** Along the trajectories from `a` and `a'`, the difference of
the vorticities is at most the initial difference plus the time integral of the difference of
the forcings `κ ∂₀θ`. -/
theorem norm_vorticity_trajectory_sub_le (hκ : Continuous κ) {a a' : ℝ^2} (ha : 0 ≤ a 1)
    (ha' : 0 ≤ a' 1) {s : ℝ} (hs : s ∈ Icc 0 b) :
    |sol.vorticity (trajectory U sol b s a) s - sol.vorticity (trajectory U sol b s a') s| ≤
      |sol.vorticity a 0 - sol.vorticity a' 0| +
        ∫ r in (0)..s, |κ (trajectory U sol b r a) *
            (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory U sol b r a) -
          κ (trajectory U sol b r a') *
            (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory U sol b r a')| := by
  have hsub : Icc 0 s ⊆ Icc 0 b := Icc_subset_Icc le_rfl hs.2
  rw [h.vorticity_trajectory hU hκ hb hI hv ha hs, h.vorticity_trajectory hU hκ hb hI hv ha' hs]
  set f : ℝ^2 → ℝ → ℝ := fun c r ↦
    κ (trajectory U sol b r c) *
      (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory U sol b r c)
  have hfc (c : ℝ^2) : ContinuousOn (f c) (Icc 0 b) :=
    h.continuousOn_forcing_trajectory hκ hb hI hv c
  have hf (c : ℝ^2) : IntervalIntegrable (f c) volume 0 s :=
    ((hfc c).mono hsub).intervalIntegrable_of_Icc hs.1
  have hsplit : (sol.vorticity a 0 + ∫ r in (0)..s, f a r) - (sol.vorticity a' 0 +
      ∫ r in (0)..s, f a' r) =
        (sol.vorticity a 0 - sol.vorticity a' 0) + ∫ r in (0)..s, (f a r - f a' r) := by
    rw [intervalIntegral.integral_sub (hf a) (hf a')]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [← Real.norm_eq_abs]
  exact intervalIntegral.norm_integral_le_integral_norm hs.1

/-- **Hölder bound of the velocity gradient** at a time of `[0, b]` from an `α`-Hölder bound
`M` and a bound `B` of the vorticity on the closed half-plane. -/
theorem norm_velocityFieldDeriv_sub_le (hU : IsVelocityLaw U R₀ C)
    (hUh : IsHolderVelocityLaw U R₀ Ch) (h : IsSolutionOn U κ R₀ sol I) (hb : 0 < b)
    (hI : Icc 0 b ⊆ I) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {r : ℝ} (hr : r ∈ Icc 0 b) {M B : ℝ}
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      |sol.vorticity y r - sol.vorticity z r| ≤ M * ‖y - z‖ ^ α)
    (hB : ∀ y : ℝ^2, 0 ≤ y 1 → |sol.vorticity y r| ≤ B) {x y : ℝ^2} (hx : 0 ≤ x 1)
    (hy : 0 ≤ y 1) :
    ‖velocityFieldDeriv U sol r x - velocityFieldDeriv U sol r y‖ ≤
      Ch α * (M + B) * ‖x - y‖ ^ α := by
  obtain ⟨R', hR', hz⟩ := h.exists_vorticity_eq_zero (hI hr)
  rw [h.velocityFieldDeriv_eq hU hb hI hr hx, h.velocityFieldDeriv_eq hU hb hI hr hy]
  exact hUh.norm_fderivWithin_sub_le hα hα1 hR'.le
    (h.contDiff_vorticity (hI hr)).continuous.continuousOn hz hM hB x y hx hy

end Gradient

section Holder

variable {α R N L : ℝ} (hU : IsVelocityLaw U R₀ C) (hUh : IsHolderVelocityLaw U R₀ Ch)
  (hκ : IsForcingCoefficient κ Bκ)
  (h : IsSolutionOn U κ R₀ sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b K)
  (hA : ContinuousOn A (Icc 0 b))
  (hDu : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖velocityFieldDeriv U sol t x‖ ≤ A t)
  (hΛ : ∫ t in (0)..b, A t ≤ Λ)
  (hd : IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N)

include hU h hb hI hv hA hDu hΛ in
/-- **Two labels: the temperature gradients.** Along the trajectories from `a` and `a'`,
`‖∇θ(X(s, a), s) - ∇θ(X(s, a'), s)‖` is at most
`(‖∇θ₀(a) - ∇θ₀(a')‖ + ∫₀ˢ ‖∇θ₀(a')‖ exp Λ ‖Du(X(r, a)) - Du(X(r, a'))‖ dr) exp Λ`. -/
theorem norm_gradient_sub_le {a a' : ℝ^2} (ha : 0 ≤ a 1) (ha' : 0 ≤ a' 1) {s : ℝ}
    (hs : s ∈ Icc 0 b) :
    ‖fderiv ℝ (fun y ↦ sol.temperature y s) (trajectory U sol b s a) -
        fderiv ℝ (fun y ↦ sol.temperature y s) (trajectory U sol b s a')‖ ≤
      (‖fderiv ℝ (fun y ↦ sol.temperature y 0) a - fderiv ℝ (fun y ↦ sol.temperature y 0) a'‖ +
        ∫ r in (0)..s, ‖fderiv ℝ (fun y ↦ sol.temperature y 0) a'‖ * Real.exp Λ *
          ‖velocityFieldDeriv U sol r (trajectory U sol b r a) -
            velocityFieldDeriv U sol r (trajectory U sol b r a')‖) * Real.exp Λ := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hsub : Icc 0 s ⊆ Icc 0 b := Icc_subset_Icc le_rfl hs.2
  set L := fderiv ℝ (fun y ↦ sol.temperature y 0) a
  set L' := fderiv ℝ (fun y ↦ sol.temperature y 0) a'
  set W : ℝ^2 → ℝ → ℝ^2 →L[ℝ] ℝ^2 := fun c ρ ↦
    variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b 0 ρ (trajectory U sol b ρ c)
  set Du : ℝ^2 → ℝ → ℝ^2 →L[ℝ] ℝ^2 := fun c ρ ↦
    velocityFieldDeriv U sol ρ (trajectory U sol b ρ c)
  set F : ℝ → ℝ^2 →L[ℝ] ℝ := fun ρ ↦ L.comp (W a ρ) - L'.comp (W a' ρ)
  set g : ℝ → ℝ := fun ρ ↦ ‖L'.comp (W a' ρ)‖ * ‖Du a ρ - Du a' ρ‖
  have hDuc (c : ℝ^2) : ContinuousOn (Du c) (Icc 0 b) := hv.continuousOn_deriv_flowOn h0 c
  have hF : ∀ ρ ∈ Icc 0 s, HasDerivWithinAt F
      (-(L.comp (W a ρ)).comp (Du a ρ) + (L'.comp (W a' ρ)).comp (Du a' ρ)) (Icc 0 s) ρ := by
    intro ρ hρ
    have h1 := (hasDerivWithinAt_gradient hb hv L a (hsub hρ)).mono hsub
    have h2 := (hasDerivWithinAt_gradient hb hv L' a' (hsub hρ)).mono hsub
    convert h1.sub h2 using 1
    simp only [W, Du, sub_neg_eq_add]
  have hg : ContinuousOn g (Icc 0 s) :=
    (((continuousOn_gradient hb hv L' a').mono hsub).norm.mul
      (((hDuc a).sub (hDuc a')).mono hsub).norm)
  have hbound : ∀ ρ ∈ Icc 0 s,
      ‖-(L.comp (W a ρ)).comp (Du a ρ) + (L'.comp (W a' ρ)).comp (Du a' ρ)‖ ≤
        A ρ * ‖F ρ‖ + g ρ := by
    intro ρ hρ
    have hXa := h.trajectory_mem hU hI hL hb.le (hsub hρ) ha
    have hsplit : -(L.comp (W a ρ)).comp (Du a ρ) + (L'.comp (W a' ρ)).comp (Du a' ρ) =
        -(F ρ).comp (Du a ρ) - (L'.comp (W a' ρ)).comp (Du a ρ - Du a' ρ) := by
      simp only [F, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
      abel
    rw [hsplit]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (ContinuousLinearMap.opNorm_comp_le _ _))
    rw [norm_neg]
    refine ((F ρ).opNorm_comp_le _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hDu ρ (hsub hρ) _ hXa) (norm_nonneg _)
  have hgron := norm_le_mul_exp_integral (f := F) (A := A) (g := g) (δ := ‖F 0‖) hF
    (hA.mono hsub) (fun ρ hρ ↦ nonneg_of_bound hDu (hsub hρ)) hg
    (fun _ _ ↦ by positivity) le_rfl hbound s ⟨hs.1, le_rfl⟩
  have hW0 (c : ℝ^2) : W c 0 = ContinuousLinearMap.id ℝ (ℝ^2) := by
    simp only [W, trajectory_zero hL hb.le]
    exact hv.variationOn_self h0 c
  have hF0 : F 0 = L - L' := by simp [F, hW0]
  have hFs : F s = fderiv ℝ (fun y ↦ sol.temperature y s) (trajectory U sol b s a) -
      fderiv ℝ (fun y ↦ sol.temperature y s) (trajectory U sol b s a') := by
    rw [h.fderiv_temperature_trajectory hU hb hI hv hs ha,
      h.fderiv_temperature_trajectory hU hb hI hv hs ha']
  have hint : ∫ ρ in (0)..s, g ρ ≤ ∫ ρ in (0)..s, ‖L'‖ * Real.exp Λ * ‖Du a ρ - Du a' ρ‖ := by
    refine intervalIntegral.integral_mono_on hs.1 (hg.intervalIntegrable_of_Icc hs.1)
      ((continuousOn_const.mul (((hDuc a).sub (hDuc a')).mono hsub).norm).intervalIntegrable_of_Icc
        hs.1) fun ρ hρ ↦ ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (L'.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact h.norm_inverseVariation_le hU hb hI hv hA hDu hΛ (hsub hρ)
      (h.trajectory_mem hU hI hL hb.le (hsub hρ) ha')
  have hexp : Real.exp (∫ ρ in (0)..s, A ρ) ≤ Real.exp Λ :=
    Real.exp_le_exp.mpr (integral_le hb hA hDu hΛ hs)
  rw [hF0, hFs] at hgron
  have hint0 : 0 ≤ ∫ ρ in (0)..s, g ρ :=
    intervalIntegral.integral_nonneg hs.1 fun _ _ ↦ by positivity
  calc _ ≤ (‖L - L'‖ + ∫ ρ in (0)..s, g ρ) * Real.exp (∫ ρ in (0)..s, A ρ) := hgron
    _ ≤ (‖L - L'‖ + ∫ ρ in (0)..s, ‖L'‖ * Real.exp Λ * ‖Du a ρ - Du a' ρ‖) * Real.exp Λ :=
        mul_le_mul (add_le_add le_rfl hint) hexp (Real.exp_pos _).le
          (by linarith [norm_nonneg (L - L')])

include hU hUh h hb hI hv hA hDu hΛ in
/-- **Step A: the Hölder constant of the temperature gradient.** If `M t` is a monotone,
nonnegative `α`-Hölder bound and `B` a bound of the vorticity on the closed half-plane at every
time of `[0, b]`, then at time `r` the temperature gradient is `α`-Hölder there with constant
`2N exp(2Λ) + N c exp(4Λ) (∫₀ʳ M + r B)`, `c = Ch α`. -/
theorem norm_fderiv_temperature_sub_le (hα : 0 < α) (hα1 : α < 1) (hd : IsHolderData
      (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N)
    {M : ℝ → ℝ} (hMm : MonotoneOn M (Icc 0 b)) (hM0 : ∀ ρ ∈ Icc 0 b, 0 ≤ M ρ)
    (hM : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      |sol.vorticity y ρ - sol.vorticity z ρ| ≤ M ρ * ‖y - z‖ ^ α)
    {B : ℝ} (hB : ∀ ρ ∈ Icc 0 b, ∀ y : ℝ^2, 0 ≤ y 1 → |sol.vorticity y ρ| ≤ B)
    {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    ‖fderiv ℝ (fun x ↦ sol.temperature x r) y - fderiv ℝ (fun x ↦ sol.temperature x r) z‖ ≤
      (2 * N * Real.exp Λ ^ 2 + N * Ch α * Real.exp Λ ^ 4 *
        ((∫ ρ in (0)..r, M ρ) + r * B)) * ‖y - z‖ ^ α := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 h0 0 (by simp))
  set E := Real.exp Λ
  have hE1 : 1 ≤ E := Real.one_le_exp (zero_le_Λ hb hDu hΛ)
  set c := Ch α
  have hc : 0 ≤ c := hUh.const_nonneg hα hα1
  have hsub : Icc 0 r ⊆ Icc 0 b := Icc_subset_Icc le_rfl hr.2
  -- The labels `a`, `a'` of `y`, `z` at the time `r`.
  set a := label U sol b y r
  set a' := label U sol b z r
  have ha : 0 ≤ a 1 := h.label_mem hU hI hL hb.le hr hy
  have ha' : 0 ≤ a' 1 := h.label_mem hU hI hL hb.le hr hz
  have hya : trajectory U sol b r a = y := trajectory_label hL hb.le hr y
  have hza : trajectory U sol b r a' = z := trajectory_label hL hb.le hr z
  have hθ₀d : Differentiable ℝ (fun x ↦ sol.temperature x 0) :=
    (h.contDiff_temperature (hI h0)).differentiable one_ne_zero
  have hfd {x : ℝ^2} (hx : 0 ≤ x 1) : fderiv ℝ (fun x ↦ sol.temperature x 0) x =
      fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄ x :=
    ((hθ₀d x).fderivWithin (uniqueDiffOn_closedUpper x hx)).symm
  have hθ₀a : ‖fderiv ℝ (fun x ↦ sol.temperature x 0) a'‖ ≤ N := by
    rw [hfd ha']
    exact hd.norm_fderivWithin_temperature_le a' ha'
  have hdata : ‖fderiv ℝ (fun x ↦ sol.temperature x 0) a -
      fderiv ℝ (fun x ↦ sol.temperature x 0) a'‖ ≤ 2 * N * ‖a - a'‖ ^ α := by
    rw [hfd ha, hfd ha']
    exact hd.norm_fderivWithin_temperature_sub_le hα.le hα1.le ha ha'
  have haa : ‖a - a'‖ ^ α ≤ E * ‖y - z‖ ^ α :=
    (Real.rpow_le_rpow (norm_nonneg _) (h.norm_label_sub_le hU hb hI hv hA hDu hΛ hr hy hz)
      hα.le).trans (mul_rpow_le_mul hE1 (norm_nonneg _) hα1.le)
  set Du : ℝ^2 → ℝ → ℝ^2 →L[ℝ] ℝ^2 := fun c ρ ↦
    velocityFieldDeriv U sol ρ (trajectory U sol b ρ c)
  have hDuc (c : ℝ^2) : ContinuousOn (Du c) (Icc 0 b) := hv.continuousOn_deriv_flowOn h0 c
  have hMi : IntervalIntegrable M volume 0 r :=
    (hMm.mono (by rw [uIcc_of_le hr.1]; exact hsub)).intervalIntegrable
  -- The forcing: the Schauder estimate of the velocity gradient at the two particles, whose
  -- distance to the power `α` is at most `exp Λ ‖a - a'‖^α`.
  have hint : ∫ ρ in (0)..r, ‖fderiv ℝ (fun x ↦ sol.temperature x 0) a'‖ * E *
      ‖Du a ρ - Du a' ρ‖ ≤ ∫ ρ in (0)..r, (N * c * E ^ 2 * ‖a - a'‖ ^ α) * (M ρ + B) := by
    refine intervalIntegral.integral_mono_on hr.1
      ((continuousOn_const.mul (((hDuc a).sub (hDuc a')).mono hsub).norm).intervalIntegrable_of_Icc
        hr.1)
      ((hMi.add intervalIntegrable_const).const_mul _) fun ρ hρ ↦ ?_
    have hρ' := hsub hρ
    have hX := h.norm_trajectory_sub_le hU hb hI hv hA hDu hΛ hρ' ha ha'
    have hXα : ‖trajectory U sol b ρ a - trajectory U sol b ρ a'‖ ^ α ≤ E * ‖a - a'‖ ^ α :=
      (Real.rpow_le_rpow (norm_nonneg _) hX hα.le).trans
        (mul_rpow_le_mul hE1 (norm_nonneg _) hα1.le)
    have hDuab := norm_velocityFieldDeriv_sub_le hU hUh h hb hI hα hα1 hρ' (hM ρ hρ')
      (hB ρ hρ') (h.trajectory_mem hU hI hL hb.le hρ' ha) (h.trajectory_mem hU hI hL hb.le hρ' ha')
    have hMρ := hM0 ρ hρ'
    calc ‖fderiv ℝ (fun x ↦ sol.temperature x 0) a'‖ * E * ‖Du a ρ - Du a' ρ‖
        ≤ N * E * (c * (M ρ + B) * (E * ‖a - a'‖ ^ α)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hθ₀a (by positivity)) ?_ (norm_nonneg _)
            (by positivity)
          exact hDuab.trans (mul_le_mul_of_nonneg_left hXα (by positivity))
      _ = N * c * E ^ 2 * ‖a - a'‖ ^ α * (M ρ + B) := by ring
  have hsplit : ∫ ρ in (0)..r, (N * c * E ^ 2 * ‖a - a'‖ ^ α) * (M ρ + B) =
      (N * c * E ^ 2 * ‖a - a'‖ ^ α) * ((∫ ρ in (0)..r, M ρ) + r * B) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hMi
      intervalIntegrable_const, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  -- The bound along the two trajectories, then from the labels back to `y`, `z`.
  have hkey := h.norm_gradient_sub_le hU hb hI hv hA hDu hΛ ha ha' hr
  rw [hya, hza] at hkey
  have hI0 : 0 ≤ (∫ ρ in (0)..r, M ρ) + r * B :=
    add_nonneg (intervalIntegral.integral_nonneg hr.1 fun ρ hρ ↦ hM0 ρ (hsub hρ))
      (mul_nonneg hr.1 hB0)
  calc _ ≤ (‖fderiv ℝ (fun x ↦ sol.temperature x 0) a -
        fderiv ℝ (fun x ↦ sol.temperature x 0) a'‖ +
        ∫ ρ in (0)..r, ‖fderiv ℝ (fun x ↦ sol.temperature x 0) a'‖ * E *
          ‖Du a ρ - Du a' ρ‖) * E := hkey
    _ ≤ (2 * N * ‖a - a'‖ ^ α + (N * c * E ^ 2 * ‖a - a'‖ ^ α) *
          ((∫ ρ in (0)..r, M ρ) + r * B)) * E :=
        mul_le_mul_of_nonneg_right (add_le_add hdata (hint.trans hsplit.le)) (by positivity)
    _ = (2 * N + N * c * E ^ 2 * ((∫ ρ in (0)..r, M ρ) + r * B)) * E * ‖a - a'‖ ^ α := by
        ring
    _ ≤ (2 * N + N * c * E ^ 2 * ((∫ ρ in (0)..r, M ρ) + r * B)) * E * (E * ‖y - z‖ ^ α) :=
        mul_le_mul_of_nonneg_left haa (by positivity)
    _ = _ := by ring

include hU hκ h hb hI hv hA hDu hΛ in
/-- **Step B: the Hölder constant of the vorticity.** If `Q t` is a monotone, nonnegative
`α`-Hölder bound of the temperature gradient on the closed half-plane at every time of `[0, b]`,
then at time `r` the vorticity is `α`-Hölder there with constant
`2N exp Λ + max (Bκ 1) (2 Bκ 0) N exp (3Λ) r + Bκ₀ exp (2Λ) ∫₀ʳ Q`. -/
theorem abs_vorticity_sub_le (hα : 0 < α) (hα1 : α < 1) (hd : IsHolderData
      (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N)
    {Q : ℝ → ℝ} (hQm : MonotoneOn Q (Icc 0 b)) (hQ0 : ∀ ρ ∈ Icc 0 b, 0 ≤ Q ρ)
    (hQ : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderiv ℝ (fun x ↦ sol.temperature x ρ) y - fderiv ℝ (fun x ↦ sol.temperature x ρ) z‖ ≤
        Q ρ * ‖y - z‖ ^ α)
    {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    |sol.vorticity y r - sol.vorticity z r| ≤
      (2 * N * Real.exp Λ + forcingHolderConst Bκ 0 * N * Real.exp Λ ^ 3 * r +
        Bκ 0 * Real.exp Λ ^ 2 * ∫ ρ in (0)..r, Q ρ) * ‖y - z‖ ^ α := by
  have hL := hv.isLipschitzFieldOn
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  set E := Real.exp Λ
  have hE1 : 1 ≤ E := Real.one_le_exp (zero_le_Λ hb hDu hΛ)
  set Hκ := forcingHolderConst Bκ 0
  have hHκ : 0 ≤ Hκ := hκ.forcingHolderConst_nonneg 0
  have hB0 : 0 ≤ Bκ 0 := hκ.bound_nonneg 0
  have hsub : Icc 0 r ⊆ Icc 0 b := Icc_subset_Icc le_rfl hr.2
  -- The labels `a`, `a'` of `y`, `z` at the time `r`.
  set a := label U sol b y r
  set a' := label U sol b z r
  have ha : 0 ≤ a 1 := h.label_mem hU hI hL hb.le hr hy
  have ha' : 0 ≤ a' 1 := h.label_mem hU hI hL hb.le hr hz
  have hya : trajectory U sol b r a = y := trajectory_label hL hb.le hr y
  have hza : trajectory U sol b r a' = z := trajectory_label hL hb.le hr z
  have haa : ‖a - a'‖ ^ α ≤ E * ‖y - z‖ ^ α :=
    (Real.rpow_le_rpow (norm_nonneg _) (h.norm_label_sub_le hU hb hI hv hA hDu hΛ hr hy hz)
      hα.le).trans (mul_rpow_le_mul hE1 (norm_nonneg _) hα1.le)
  set f : ℝ^2 → ℝ → ℝ := fun c ρ ↦
    κ (trajectory U sol b ρ c) *
      (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y ρ)) (trajectory U sol b ρ c)
  have hfc (c : ℝ^2) : ContinuousOn (f c) (Icc 0 b) :=
    h.continuousOn_forcing_trajectory hκ.contDiff_one.continuous hb hI hv c
  have hQi : IntervalIntegrable Q volume 0 r :=
    (hQm.mono (by rw [uIcc_of_le hr.1]; exact hsub)).intervalIntegrable
  have he : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by simp
  -- The difference of the forcings `κ ∂₀θ` at the two particles: `κ` times a Hölder difference
  -- of `∂₀θ`, plus a Hölder difference of `κ` times `∂₀θ`.
  have hint : ∫ ρ in (0)..r, |f a ρ - f a' ρ| ≤
      ∫ ρ in (0)..r, (E * ‖a - a'‖ ^ α) * (Bκ 0 * Q ρ + Hκ * (N * E)) := by
    refine intervalIntegral.integral_mono_on hr.1
      ((((hfc a).sub (hfc a')).mono hsub).abs.intervalIntegrable_of_Icc hr.1)
      (((hQi.const_mul _).add intervalIntegrable_const).const_mul _) fun ρ hρ ↦ ?_
    have hρ' := hsub hρ
    set p := trajectory U sol b ρ a
    set q := trajectory U sol b ρ a'
    have hp := h.trajectory_mem hU hI hL hb.le hρ' ha
    have hq := h.trajectory_mem hU hI hL hb.le hρ' ha'
    have hX := h.norm_trajectory_sub_le hU hb hI hv hA hDu hΛ hρ' ha ha'
    have hXα : ‖p - q‖ ^ α ≤ E * ‖a - a'‖ ^ α :=
      (Real.rpow_le_rpow (norm_nonneg _) hX hα.le).trans
        (mul_rpow_le_mul hE1 (norm_nonneg _) hα1.le)
    have hg : |(∂[(0 : Fin 2)] (fun y ↦ sol.temperature y ρ)) p -
        (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y ρ)) q| ≤ Q ρ * ‖p - q‖ ^ α := by
      simp only [PDE.partialDeriv]
      rw [← Real.norm_eq_abs, ← sub_apply]
      refine ((ContinuousLinearMap.le_opNorm _ _).trans_eq (by rw [he, mul_one])).trans ?_
      exact hQ ρ hρ' p q hp hq
    have hgq : |(∂[(0 : Fin 2)] (fun y ↦ sol.temperature y ρ)) q| ≤ N * E := by
      simp only [PDE.partialDeriv]
      rw [← Real.norm_eq_abs]
      refine ((ContinuousLinearMap.le_opNorm _ _).trans_eq (by rw [he, mul_one])).trans ?_
      exact h.norm_fderiv_temperature_le hU hb hI hv hA hDu hΛ hd hρ' hq
    have hsplit : f a ρ - f a' ρ = κ p * ((∂[(0 : Fin 2)] (fun y ↦ sol.temperature y ρ)) p -
        (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y ρ)) q) +
        (κ p - κ q) * (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y ρ)) q := by
      simp only [f, p, q]
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |κ p| * |(∂[(0 : Fin 2)] (fun y ↦ sol.temperature y ρ)) p -
        (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y ρ)) q| ≤ Bκ 0 * (Q ρ * (E * ‖a - a'‖ ^ α)) :=
      mul_le_mul (hκ.abs_le p) (hg.trans (mul_le_mul_of_nonneg_left hXα (hQ0 ρ hρ')))
        (abs_nonneg _) hB0
    have h2 : |κ p - κ q| * |(∂[(0 : Fin 2)] (fun y ↦ sol.temperature y ρ)) q| ≤
        Hκ * (E * ‖a - a'‖ ^ α) * (N * E) :=
      mul_le_mul ((hκ.abs_sub_le_rpow hα.le hα1.le p q).trans
        (mul_le_mul_of_nonneg_left hXα hHκ)) hgq (abs_nonneg _) (by positivity)
    calc _ ≤ Bκ 0 * (Q ρ * (E * ‖a - a'‖ ^ α)) + Hκ * (E * ‖a - a'‖ ^ α) * (N * E) :=
          add_le_add h1 h2
      _ = (E * ‖a - a'‖ ^ α) * (Bκ 0 * Q ρ + Hκ * (N * E)) := by ring
  have hsplit : ∫ ρ in (0)..r, (E * ‖a - a'‖ ^ α) * (Bκ 0 * Q ρ + Hκ * (N * E)) =
      (E * ‖a - a'‖ ^ α) * (Bκ 0 * (∫ ρ in (0)..r, Q ρ) + r * (Hκ * (N * E))) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hQi.const_mul _)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  -- The vorticity along the two trajectories, then from the labels back to `y`, `z`.
  have hkey := h.norm_vorticity_trajectory_sub_le hU hb hI hv hκ.contDiff_one.continuous ha ha' hr
  rw [hya, hza] at hkey
  have hdata := hd.abs_vorticity_sub_le hα.le hα1.le ha ha'
  have hI0 : 0 ≤ ∫ ρ in (0)..r, Q ρ :=
    intervalIntegral.integral_nonneg hr.1 fun ρ hρ ↦ hQ0 ρ (hsub hρ)
  have hc0 : 0 ≤ 2 * N + E * (Bκ 0 * (∫ ρ in (0)..r, Q ρ) + r * (Hκ * (N * E))) := by
    have := hr.1
    positivity
  calc _ ≤ |sol.vorticity a 0 - sol.vorticity a' 0| + ∫ ρ in (0)..r, |f a ρ - f a' ρ| := hkey
    _ ≤ 2 * N * ‖a - a'‖ ^ α + (E * ‖a - a'‖ ^ α) *
          (Bκ 0 * (∫ ρ in (0)..r, Q ρ) + r * (Hκ * (N * E))) :=
        add_le_add hdata (hint.trans hsplit.le)
    _ = (2 * N + E * (Bκ 0 * (∫ ρ in (0)..r, Q ρ) + r * (Hκ * (N * E)))) * ‖a - a'‖ ^ α := by
        ring
    _ ≤ (2 * N + E * (Bκ 0 * (∫ ρ in (0)..r, Q ρ) + r * (Hκ * (N * E)))) * (E * ‖y - z‖ ^ α) :=
        mul_le_mul_of_nonneg_left haa hc0
    _ = _ := by ring

include hU hUh hκ h hb hI hv hA hDu hΛ in
/-- **Hölder bounds of the vorticity and of the temperature gradient.** For a solution on
`[0, b]`, `b ≤ L`, whose slices are data of the class `IsHolderData` with some bounds (`hreg`, a
qualitative hypothesis), with data at time `0` of the class `IsHolderData … α R N`, `‖Du‖ ≤ A` on
the closed half-plane and `∫₀ᵇ A ≤ Λ`, at every time of `[0, b]` the vorticity is `α`-Hölder on
the closed half-plane with constant `vorticityHolderBound (Ch α) Bκ N Λ L` and the temperature
gradient with constant `gradientHolderBound (Ch α) Bκ N Λ L`. These are the Hölder bounds of
lower order in the a priori estimate. Proof: the running suprema `M`, `Q` of the two Hölder
quotients satisfy `Q ≤ q + q' ∫ M` (Step A) and `M ≤ m + m' ∫ Q` (Step B), hence
`M ≤ c' + C' ∫ M`, and Grönwall's inequality for monotone functions bounds `M`, then `Q`. -/
theorem holder_bound {Rq Nq : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hd : IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N)
    (hreg : ∀ t ∈ Icc 0 b,
      IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α Rq Nq)
    (hbL : b ≤ L) {s : ℝ} (hs : s ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    |sol.vorticity y s - sol.vorticity z s| ≤
        vorticityHolderBound (Ch α) Bκ N Λ L * ‖y - z‖ ^ α ∧
      ‖fderiv ℝ (fun x ↦ sol.temperature x s) y - fderiv ℝ (fun x ↦ sol.temperature x s) z‖ ≤
        gradientHolderBound (Ch α) Bκ N Λ L * ‖y - z‖ ^ α := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have hL0 : 0 ≤ L := hb.le.trans hbL
  set E := Real.exp Λ
  have hE1 : 1 ≤ E := Real.one_le_exp (zero_le_Λ hb hDu hΛ)
  set c := Ch α
  have hc : 0 ≤ c := hUh.const_nonneg hα hα1
  have hB0 : 0 ≤ Bκ 0 := hκ.bound_nonneg 0
  have hHκ : 0 ≤ forcingHolderConst Bκ 0 := hκ.forcingHolderConst_nonneg 0
  set Bω := vorticityBound Bκ N Λ L
  have hBω : ∀ ρ ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → |sol.vorticity x ρ| ≤ Bω := fun ρ hρ x hx ↦
    (h.abs_vorticity_le hU hκ hb hI hv hA hDu hΛ hd hρ hx).trans (by
      have := mul_le_mul_of_nonneg_right (hρ.2.trans hbL)
        (mul_nonneg hB0 (mul_nonneg hN (Real.exp_pos Λ).le))
      simp only [Bω, vorticityBound]
      linarith)
  have hBω0 : 0 ≤ Bω := (abs_nonneg _).trans (hBω 0 ⟨le_rfl, hb.le⟩ 0 (by simp))
  set qa := gradientHolderConst c Bκ N Λ L
  set qb := N * c * E ^ 4
  set ma := vorticityHolderConst Bκ N Λ L
  set mb := Bκ 0 * E ^ 2
  have hqa : qa = 2 * N * E ^ 2 + qb * L * Bω := by
    simp only [qa, qb, gradientHolderConst, Bω, E]
  have hma : ma = 2 * N * E + forcingHolderConst Bκ 0 * N * E ^ 3 * L := rfl
  have hqb0 : 0 ≤ qb := by positivity
  have hmb0 : 0 ≤ mb := by positivity
  have hqa0 : 0 ≤ qa := by rw [hqa]; positivity
  have hma0 : 0 ≤ ma := by rw [hma]; positivity
  set qω : ℝ → ℝ^2 → ℝ^2 → ℝ := fun r y z ↦
    ‖sol.vorticity y r - sol.vorticity z r‖ / ‖y - z‖ ^ α
  set qθ : ℝ → ℝ^2 → ℝ^2 → ℝ := fun r y z ↦
    ‖fderiv ℝ (fun x ↦ sol.temperature x r) y - fderiv ℝ (fun x ↦ sol.temperature x r) z‖ /
      ‖y - z‖ ^ α
  have hdiv {u v : ℝ} {y z : ℝ^2} (hyz : y ≠ z) (huv : u ≤ v * ‖y - z‖ ^ α) :
      u / ‖y - z‖ ^ α ≤ v :=
    (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyz)) α)).mpr huv
  have hqω : ∀ r ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → y ≠ z → qω r y z ≤ 2 * Nq :=
    fun r hr y z hy hz hyz ↦ hdiv hyz (by
      rw [Real.norm_eq_abs]
      exact (hreg r hr).abs_vorticity_sub_le hα.le hα1.le hy hz)
  have hfd (r : ℝ) (hr : r ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
      fderiv ℝ (fun x ↦ sol.temperature x r) x =
        fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄ x :=
    ((((h.contDiff_temperature (hI hr)).differentiable one_ne_zero) x).fderivWithin
      (uniqueDiffOn_closedUpper x hx)).symm
  have hqθ : ∀ r ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → y ≠ z → qθ r y z ≤ 2 * Nq :=
    fun r hr y z hy hz hyz ↦ hdiv hyz (by
      rw [hfd r hr hy, hfd r hr hz]
      exact (hreg r hr).norm_fderivWithin_temperature_sub_le hα.le hα1.le hy hz)
  set Mω := holderSup qω
  set Qθ := holderSup qθ
  have hqω0 : ∀ r y z, 0 ≤ qω r y z := fun _ _ _ ↦ by positivity
  have hqθ0 : ∀ r y z, 0 ≤ qθ r y z := fun _ _ _ ↦ by positivity
  have hMm : MonotoneOn Mω (Icc 0 b) := monotoneOn_holderSup hqω
  have hQm : MonotoneOn Qθ (Icc 0 b) := monotoneOn_holderSup hqθ
  have hM0 : ∀ ρ ∈ Icc 0 b, 0 ≤ Mω ρ := fun ρ hρ ↦ holderSup_nonneg hqω0 hqω hρ
  have hQ0 : ∀ ρ ∈ Icc 0 b, 0 ≤ Qθ ρ := fun ρ hρ ↦ holderSup_nonneg hqθ0 hqθ hρ
  have hMω : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      |sol.vorticity y ρ - sol.vorticity z ρ| ≤ Mω ρ * ‖y - z‖ ^ α := fun ρ hρ y z hy hz ↦ by
    rw [← Real.norm_eq_abs]
    exact norm_sub_le_of_div_le (F := fun x ↦ sol.vorticity x ρ) hα fun hyz ↦
      le_holderSup hqω hρ.2 ⟨hρ.1, le_rfl⟩ hy hz hyz
  have hQθ : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderiv ℝ (fun x ↦ sol.temperature x ρ) y - fderiv ℝ (fun x ↦ sol.temperature x ρ) z‖ ≤
        Qθ ρ * ‖y - z‖ ^ α := fun ρ hρ y z hy hz ↦
    norm_sub_le_of_div_le (F := fun x ↦ fderiv ℝ (fun x ↦ sol.temperature x ρ) x) hα
      fun hyz ↦ le_holderSup hqθ hρ.2 ⟨hρ.1, le_rfl⟩ hy hz hyz
  -- Step A: the temperature gradient.
  have hA' : ∀ r ∈ Icc 0 b, Qθ r ≤ qa + qb * ∫ ρ in (0)..r, Mω ρ :=
    fun r hr ↦ holderSup_le hr.1 fun ρ hρ y z hy hz hyz ↦ by
      have hρ' : ρ ∈ Icc 0 b := ⟨hρ.1, hρ.2.trans hr.2⟩
      refine hdiv hyz ((h.norm_fderiv_temperature_sub_le hU hUh hb hI hv hA hDu hΛ hα hα1 hd
        hMm hM0 hMω hBω hρ' hy hz).trans (mul_le_mul_of_nonneg_right ?_ (by positivity)))
      have h1 := integral_le_integral_of_monotoneOn hMm hM0 hρ.1 hρ.2 hr.2
      have h2 : ρ * Bω ≤ L * Bω := mul_le_mul_of_nonneg_right (hρ'.2.trans hbL) hBω0
      rw [hqa]
      have h3 : qb * ((∫ σ in (0)..ρ, Mω σ) + ρ * Bω) ≤
          qb * ((∫ σ in (0)..r, Mω σ) + L * Bω) :=
        mul_le_mul_of_nonneg_left (by linarith) hqb0
      simp only [qb] at h3 ⊢
      nlinarith
  -- Step B: the vorticity.
  have hB' : ∀ r ∈ Icc 0 b, Mω r ≤ ma + mb * ∫ ρ in (0)..r, Qθ ρ :=
    fun r hr ↦ holderSup_le hr.1 fun ρ hρ y z hy hz hyz ↦ by
      have hρ' : ρ ∈ Icc 0 b := ⟨hρ.1, hρ.2.trans hr.2⟩
      refine hdiv hyz ?_
      rw [Real.norm_eq_abs]
      refine (h.abs_vorticity_sub_le hU hκ hb hI hv hA hDu hΛ hα hα1 hd hQm hQ0 hQθ hρ' hy
        hz).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have h1 := integral_le_integral_of_monotoneOn hQm hQ0 hρ.1 hρ.2 hr.2
      have h2 : forcingHolderConst Bκ 0 * N * E ^ 3 * ρ ≤
          forcingHolderConst Bκ 0 * N * E ^ 3 * L :=
        mul_le_mul_of_nonneg_left (hρ'.2.trans hbL) (by positivity)
      have h3 : mb * ∫ σ in (0)..ρ, Qθ σ ≤ mb * ∫ σ in (0)..r, Qθ σ :=
        mul_le_mul_of_nonneg_left h1 hmb0
      rw [hma]
      simp only [mb] at h3
      linarith
  -- Step C: the closed inequality for the vorticity.
  set c' := ma + mb * L * qa
  set C' := mb * L * qb
  have hC0 : 0 ≤ C' := by positivity
  have hc0 : 0 ≤ c' := by positivity
  have hclosed : ∀ r ∈ Icc 0 b, Mω r ≤ c' + C' * ∫ ρ in (0)..r, Mω ρ := fun r hr ↦ by
    have hIM : 0 ≤ ∫ ρ in (0)..r, Mω ρ :=
      intervalIntegral.integral_nonneg hr.1 fun ρ hρ ↦ hM0 ρ ⟨hρ.1, hρ.2.trans hr.2⟩
    have hIQ : ∫ ρ in (0)..r, Qθ ρ ≤ L * (qa + qb * ∫ ρ in (0)..r, Mω ρ) := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (f := Qθ) (a := 0) (b := r)
        (C := qa + qb * ∫ ρ in (0)..r, Mω ρ) fun ρ hρ ↦ by
          rw [uIoc_of_le hr.1] at hρ
          have hρ' : ρ ∈ Icc 0 b := ⟨hρ.1.le, hρ.2.trans hr.2⟩
          rw [Real.norm_eq_abs, abs_of_nonneg (hQ0 ρ hρ')]
          refine (hA' ρ hρ').trans ?_
          have := integral_le_integral_of_monotoneOn hMm hM0 hρ.1.le hρ.2 hr.2
          have := mul_le_mul_of_nonneg_left this hqb0
          linarith
      rw [sub_zero, abs_of_nonneg hr.1] at h1
      have h2 : (qa + qb * ∫ ρ in (0)..r, Mω ρ) * r ≤ (qa + qb * ∫ ρ in (0)..r, Mω ρ) * L :=
        mul_le_mul_of_nonneg_left (hr.2.trans hbL) (by positivity)
      calc ∫ ρ in (0)..r, Qθ ρ ≤ ‖∫ ρ in (0)..r, Qθ ρ‖ := le_abs_self _
        _ ≤ _ := by linarith
    calc Mω r ≤ ma + mb * ∫ ρ in (0)..r, Qθ ρ := hB' r hr
      _ ≤ ma + mb * (L * (qa + qb * ∫ ρ in (0)..r, Mω ρ)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hIQ hmb0)
      _ = c' + C' * ∫ ρ in (0)..r, Mω ρ := by simp only [c', C']; ring
  -- Step D: Grönwall.
  have hgron := le_of_le_add_integral_of_monotoneOn hc0 hC0 hMm hclosed
  have hMb : ∀ r ∈ Icc 0 b, Mω r ≤ vorticityHolderBound c Bκ N Λ L := fun r hr ↦ by
    refine (hgron r hr).trans ?_
    have hrL : r ≤ L := hr.2.trans hbL
    have hmono : C' * r * Real.exp (C' * r) ≤ C' * L * Real.exp (C' * L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hrL hC0)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrL hC0)) (Real.exp_pos _).le
        (mul_nonneg hC0 hL0)
    have hv : vorticityHolderBound c Bκ N Λ L = c' * (1 + C' * L * Real.exp (C' * L)) := by
      simp only [vorticityHolderBound, c', C', ma, mb, qa, qb, E]
    rw [hv]
    exact mul_le_mul_of_nonneg_left (by linarith) hc0
  have hQb : Qθ s ≤ gradientHolderBound c Bκ N Λ L := by
    refine (hA' s hs).trans ?_
    have hI : ∫ ρ in (0)..s, Mω ρ ≤ L * vorticityHolderBound c Bκ N Λ L := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (f := Mω) (a := 0) (b := s)
        (C := vorticityHolderBound c Bκ N Λ L) fun ρ hρ ↦ by
          rw [uIoc_of_le hs.1] at hρ
          have hρ' : ρ ∈ Icc 0 b := ⟨hρ.1.le, hρ.2.trans hs.2⟩
          rw [Real.norm_eq_abs, abs_of_nonneg (hM0 ρ hρ')]
          exact hMb ρ hρ'
      rw [sub_zero, abs_of_nonneg hs.1] at h1
      have hV0 : 0 ≤ vorticityHolderBound c Bκ N Λ L := (hM0 s hs).trans (hMb s hs)
      calc ∫ ρ in (0)..s, Mω ρ ≤ ‖∫ ρ in (0)..s, Mω ρ‖ := le_abs_self _
        _ ≤ vorticityHolderBound c Bκ N Λ L * s := h1
        _ ≤ vorticityHolderBound c Bκ N Λ L * L :=
            mul_le_mul_of_nonneg_left (hs.2.trans hbL) hV0
        _ = L * vorticityHolderBound c Bκ N Λ L := by ring
    have hg : gradientHolderBound c Bκ N Λ L = qa + qb * (L * vorticityHolderBound c Bκ N Λ L) := by
      simp only [gradientHolderBound, qa, qb, E]; ring
    rw [hg]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hI hqb0)
  refine ⟨(hMω s hs y z hy hz).trans
    (mul_le_mul_of_nonneg_right (hMb s hs) (by positivity)), (hQθ s hs y z hy hz).trans
    (mul_le_mul_of_nonneg_right hQb (by positivity))⟩

end Holder

end IsSolutionOn

end HalfPlaneSystem
