/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.APrioriLower
import PDE.Analysis.Calculus.HolderInterpolation

/-!
# Hölder bounds of the vorticity and of the temperature gradient

Let `sol` solve the half-plane Boussinesq system on `[0, b]`, with `‖Du(t)‖ ≤ A(t)` on the closed
half-plane and `∫₀ᵇ A ≤ Λ`. We bound the `α`-Hölder constants of the vorticity and of the
temperature gradient on `[0, b]` in terms of the data, with `A` entering only through `Λ`. Together
with the lower-order bounds such as `IsSolutionOn.norm_label_sub_le`, these bounds enter the a
priori estimate behind the continuation criterion.

## Main definitions

* `holderSup`: the running supremum over `r ∈ [0, s]` and `y ≠ z ∈ H̄` of a family of quotients.
* `vorticityHolderBound`: the bound `c (1 + C b exp (C b))` of the `α`-Hölder constant of the
  vorticity on `[0, b]`.
* `gradientHolderBound`: the bound of the `α`-Hölder constant of the temperature gradient on
  `[0, b]`.

## Main results

* `IsSolutionOn.holder_bound`: the `α`-Hölder constants of `ω(t)` and of `∇θ(t)` on the closed
  half-plane are bounded by explicit functions of `N`, `α`, `Λ` and `b` (`vorticityHolderBound`,
  `gradientHolderBound`), for every time of `[0, b]`.
* `IsSolutionOn.hasDerivWithinAt_gradient`: along a trajectory
  `∂ᵣ (∇θ₀(a) ∘ W(r, a)) = -(∇θ₀(a) ∘ W(r, a)) ∘ Du(r, X(r, a))`.
* `IsSolutionOn.norm_gradient_sub_le`: the difference of the temperature gradients along the
  trajectories from two labels.
* `IsSolutionOn.norm_vorticity_trajectory_sub_le`: the difference of the vorticities along the
  trajectories from two labels.
* `IsSolutionOn.norm_fderiv_temperature_sub_le`: a monotone Hölder bound of the vorticity gives
  one of the temperature gradient.
* `IsSolutionOn.abs_vorticity_sub_le`: a monotone Hölder bound of the temperature gradient gives
  one of the vorticity.

## How it works

Along the trajectory `X(r, a)` from a label `a`, the temperature gradient `G(a, r) = ∇θ(X(r, a), r)`
equals `∇θ₀(a) ∘ W(r, a)` with the inverse first variation `W` (`fderiv_temperature_trajectory`), so
it solves `∂ᵣ G = -G ∘ Du(X)` (`hasDerivWithinAt_gradient`). For two labels the difference obeys a
linear equation forced by `G(a') ∘ (Du(X(a)) - Du(X(a')))` (`norm_gradient_sub_le`). The Hölder
bound `844/(α(1-α))` of `Du` in terms of the vorticity (`norm_velocityFieldDeriv_sub_le`) turns this
into a bound of the Hölder constant of the temperature gradient by that of the vorticity
(`norm_fderiv_temperature_sub_le`). The vorticity along a trajectory is the initial vorticity plus
the time integral of `∂₀θ` (`norm_vorticity_trajectory_sub_le`), which gives the converse bound
(`abs_vorticity_sub_le`). We apply both bounds to the running suprema of the two Hölder quotients
(`holderSup`), which are monotone in time. Substituting the first into the second gives
`M(r) ≤ c + C ∫₀ʳ M` for the running supremum `M` of the vorticity quotients, and Grönwall's
inequality for monotone functions (`le_of_le_add_integral_of_monotoneOn`) bounds `M` by
`vorticityHolderBound`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE IncompressibleFlow
open scoped Topology NNReal
open SobolevSpace

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### Running suprema of Hölder quotients -/

/-- The running supremum `sup {q r y z | r ∈ [0, s], y ≠ z ∈ H̄}` of a family of quotients. -/
def holderSup (q : ℝ → ℝ^2 → ℝ^2 → ℝ) (s : ℝ) : ℝ :=
  sSup {x | ∃ r ∈ Icc 0 s, ∃ y z : ℝ^2, 0 ≤ y 1 ∧ 0 ≤ z 1 ∧ y ≠ z ∧ x = q r y z}

section HolderSup

variable {q : ℝ → ℝ^2 → ℝ^2 → ℝ} {b M s : ℝ}

/-- The points `0` and `e₁` of the closed half-plane are distinct. -/
theorem zero_ne_single_one : (0 : ℝ^2) ≠ EuclideanSpace.single 1 1 := by
  intro h
  have := congrArg (fun y : ℝ^2 ↦ y 1) h
  simp at this

/-- For `s ≥ 0` the set of quotients whose supremum is `holderSup q s` is nonempty. -/
theorem holderSup_nonempty (hs : 0 ≤ s) :
    {x | ∃ r ∈ Icc 0 s, ∃ y z : ℝ^2, 0 ≤ y 1 ∧ 0 ≤ z 1 ∧ y ≠ z ∧ x = q r y z}.Nonempty :=
  ⟨_, 0, ⟨le_rfl, hs⟩, 0, EuclideanSpace.single 1 1, by simp, by simp, zero_ne_single_one, rfl⟩

/-- If the quotients are at most `M` for the times of `[0, b]`, the set whose supremum is
`holderSup q s` is bounded above for `s ≤ b`. -/
theorem holderSup_bddAbove
    (hM : ∀ r ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → y ≠ z → q r y z ≤ M) (hs : s ≤ b) :
    BddAbove {x | ∃ r ∈ Icc 0 s, ∃ y z : ℝ^2, 0 ≤ y 1 ∧ 0 ≤ z 1 ∧ y ≠ z ∧ x = q r y z} :=
  ⟨M, by
    rintro x ⟨r, hr, y, z, hy, hz, hyz, rfl⟩
    exact hM r ⟨hr.1, hr.2.trans hs⟩ y z hy hz hyz⟩

/-- Every quotient up to time `s` is at most the running supremum. -/
theorem le_holderSup
    (hM : ∀ r ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → y ≠ z → q r y z ≤ M) (hs : s ≤ b)
    {r : ℝ} (hr : r ∈ Icc 0 s) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) (hyz : y ≠ z) :
    q r y z ≤ holderSup q s :=
  le_csSup (holderSup_bddAbove hM hs) ⟨r, hr, y, z, hy, hz, hyz, rfl⟩

/-- A common bound of the quotients up to time `s` bounds the running supremum. -/
theorem holderSup_le {C : ℝ} (hs : 0 ≤ s)
    (hC : ∀ r ∈ Icc 0 s, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → y ≠ z → q r y z ≤ C) :
    holderSup q s ≤ C :=
  csSup_le (holderSup_nonempty hs) (by
    rintro x ⟨r, hr, y, z, hy, hz, hyz, rfl⟩
    exact hC r hr y z hy hz hyz)

/-- The running supremum is monotone. -/
theorem monotoneOn_holderSup
    (hM : ∀ r ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → y ≠ z → q r y z ≤ M) :
    MonotoneOn (holderSup q) (Icc 0 b) := fun s hs t ht hst ↦
  csSup_le_csSup (holderSup_bddAbove hM ht.2) (holderSup_nonempty hs.1) (by
    rintro x ⟨r, hr, y, z, hy, hz, hyz, rfl⟩
    exact ⟨r, ⟨hr.1, hr.2.trans hst⟩, y, z, hy, hz, hyz, rfl⟩)

/-- The running supremum of nonnegative quotients is nonnegative. -/
theorem holderSup_nonneg (hq : ∀ r y z, 0 ≤ q r y z)
    (hM : ∀ r ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → y ≠ z → q r y z ≤ M)
    (hs : s ∈ Icc 0 b) : 0 ≤ holderSup q s :=
  (hq 0 0 (EuclideanSpace.single 1 1)).trans
    (le_holderSup hM hs.2 ⟨le_rfl, hs.1⟩ (by simp) (by simp) zero_ne_single_one)

end HolderSup

/-- A bound of the Hölder quotients `‖F y - F z‖ / ‖y - z‖^α` for `y ≠ z` is a Hölder bound. -/
theorem norm_sub_le_of_div_le {E : Type*} [SeminormedAddCommGroup E] {F : ℝ^2 → E}
    {α M : ℝ} (hα : 0 < α) {y z : ℝ^2}
    (h : y ≠ z → ‖F y - F z‖ / ‖y - z‖ ^ α ≤ M) : ‖F y - F z‖ ≤ M * ‖y - z‖ ^ α := by
  by_cases hyz : y = z
  · subst hyz
    rw [sub_self, sub_self, norm_zero, norm_zero, Real.zero_rpow hα.ne', mul_zero]
  · have hpos : 0 < ‖y - z‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyz)) α
    exact (div_le_iff₀ hpos).mp (h hyz)

/-- `(E x)^α ≤ E x^α` for `E ≥ 1`, `x ≥ 0` and `α ≤ 1`. -/
theorem mul_rpow_le_mul {E x α : ℝ} (hE : 1 ≤ E) (hx : 0 ≤ x) (hα1 : α ≤ 1) :
    (E * x) ^ α ≤ E * x ^ α := by
  rw [Real.mul_rpow (zero_le_one.trans hE) hx]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hx α)
  calc E ^ α ≤ E ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hE hα1
    _ = E := Real.rpow_one E

/-- The bound of the `α`-Hölder constant of the vorticity on `[0, b]`:
`c (1 + C b exp (C b))` with `c = 2NE(1 + E³b)`, `C = N (844/(α(1-α))) E⁶ b`, `E = exp Λ`. -/
def vorticityHolderBound (α N Λ b : ℝ) : ℝ :=
  2 * N * Real.exp Λ * (1 + Real.exp Λ ^ 3 * b) *
    (1 + N * (844 / (α * (1 - α))) * Real.exp Λ ^ 6 * b * b *
      Real.exp (N * (844 / (α * (1 - α))) * Real.exp Λ ^ 6 * b * b))

/-- The bound of the `α`-Hölder constant of the temperature gradient on `[0, b]`:
`2NE² + N (844/(α(1-α))) E⁴ b · vorticityHolderBound`, `E = exp Λ`. -/
def gradientHolderBound (α N Λ b : ℝ) : ℝ :=
  2 * N * Real.exp Λ ^ 2 +
    N * (844 / (α * (1 - α))) * Real.exp Λ ^ 4 * (b * vorticityHolderBound α N Λ b)

/-- For a nonnegative function monotone on `[0, b]`, `∫₀^ρ M ≤ ∫₀^r M` for `0 ≤ ρ ≤ r ≤ b`. -/
theorem integral_le_integral_of_monotoneOn {M : ℝ → ℝ} {b ρ r : ℝ}
    (hM : MonotoneOn M (Icc 0 b)) (hM0 : ∀ t ∈ Icc 0 b, 0 ≤ M t) (hρ : 0 ≤ ρ) (hρr : ρ ≤ r)
    (hr : r ≤ b) : ∫ t in (0)..ρ, M t ≤ ∫ t in (0)..r, M t := by
  have hr0 : 0 ≤ r := hρ.trans hρr
  refine intervalIntegral.integral_mono_interval le_rfl hρ hρr ?_
    ((hM.mono (by rw [uIcc_of_le hr0]; exact Icc_subset_Icc le_rfl hr)).intervalIntegrable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hM0 t ⟨ht.1.le, ht.2.trans hr⟩

namespace IsHolderData

variable {ω₀ θ₀ : ℝ^2 → ℝ} {α R N : ℝ}

/-- A function bounded by `M` and `L`-Lipschitz on the closed half-plane with `L ≤ M` is
`α`-Hölder there with constant `2M`. -/
theorem norm_sub_le_two_mul_rpow {E : Type*} [SeminormedAddCommGroup E] {f : ℝ^2 → E}
    {L M : ℝ} (hL : ∀ x ∈ H̄, ∀ y ∈ H̄, ‖f x - f y‖ ≤ L * ‖x - y‖) (hM : ∀ x ∈ H̄, ‖f x‖ ≤ M)
    (hLM : L ≤ M) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖f x - f y‖ ≤ 2 * M * ‖x - y‖ ^ α := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx)
  have h := PDE.Analysis.norm_sub_le_max_mul_rpow (S := H̄) (f := f) (L := L) (M := M)
    (fun a ha c hc ↦ by rw [dist_eq_norm]; exact hL a ha c hc) hM hα0 hα1 hx hy
  rw [dist_eq_norm, max_eq_right (by linarith)] at h
  exact h

/-- The vorticity datum is `α`-Hölder on the closed half-plane with constant `2N`. -/
theorem abs_vorticity_sub_le (hd : IsHolderData ω₀ θ₀ α R N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) : |ω₀ x - ω₀ y| ≤ 2 * N * ‖x - y‖ ^ α := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le x hx)
  rw [← Real.norm_eq_abs]
  refine norm_sub_le_two_mul_rpow (L := N) (fun a ha c hc ↦ ?_)
    (fun a ha ↦ by rw [Real.norm_eq_abs]; exact hd.abs_vorticity_le a ha) le_rfl hα0 hα1 hx hy
  have h := PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_fderivWithin_le
    (hd.vorticity_contDiffOn.differentiableOn one_ne_zero)
    (fun z hz ↦ hd.norm_fderivWithin_vorticity_le z hz) hc ha
  exact h

/-- The gradient of the temperature datum is `α`-Hölder on the closed half-plane with constant
`2N`. -/
theorem norm_fderivWithin_temperature_sub_le (hd : IsHolderData ω₀ θ₀ α R N) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖fderivWithin ℝ θ₀ H̄ x - fderivWithin ℝ θ₀ H̄ y‖ ≤ 2 * N * ‖x - y‖ ^ α := by
  have hD : DifferentiableOn ℝ (fderivWithin ℝ θ₀ H̄) H̄ :=
    (hd.temperature_contDiffOn.fderivWithin uniqueDiffOn_closedUpper
      (by norm_num)).differentiableOn one_ne_zero
  refine norm_sub_le_two_mul_rpow (L := N) (fun a ha c hc ↦ ?_)
    (fun a ha ↦ hd.norm_fderivWithin_temperature_le a ha) le_rfl hα0 hα1 hx hy
  exact PDE.Analysis.convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_fderivWithin_le hD
    (fun z hz ↦ hd.norm_fderivWithin_fderivWithin_temperature_le z hz) hc ha

end IsHolderData

namespace IsSolutionOn

variable {sol : VorticityStreamFields} {I : Set ℝ} {b Λ : ℝ} {K : ℝ≥0} {A : ℝ → ℝ}

section Gradient

variable (h : IsSolutionOn sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField sol) (velocityFieldDeriv sol) 0 b K)

include h hb hI hv in
/-- **The temperature gradient along a trajectory** is the initial gradient at the label composed
with the inverse first variation. -/
theorem fderiv_temperature_trajectory {r : ℝ} (hr : r ∈ Icc 0 b) {a : ℝ^2} (ha : 0 ≤ a 1) :
    fderiv ℝ (fun y ↦ sol.temperature y r) (trajectory sol b r a) =
      (fderiv ℝ (fun y ↦ sol.temperature y 0) a).comp
        (variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b 0 r
          (trajectory sol b r a)) := by
  have hL := hv.isLipschitzFieldOn
  have h1 := h.fderiv_temperature_eq hb hI hv hr (h.trajectory_mem hI hL hr ha)
  rwa [show label sol b (trajectory sol b r a) r = a from
    hL.flowOn_flowOn_self hr ⟨le_rfl, hb.le⟩ a] at h1

omit h hI in
include hb hv in
/-- **The equation of the temperature gradient along a trajectory:**
`∂ᵣ (∇θ₀(a) ∘ W(r, a)) = -(∇θ₀(a) ∘ W(r, a)) ∘ Du(r, X(r, a))`. -/
theorem hasDerivWithinAt_gradient (L : ℝ^2 →L[ℝ] ℝ) (a : ℝ^2) {r : ℝ} (hr : r ∈ Icc 0 b) :
    HasDerivWithinAt (fun ρ ↦ L.comp (variationOn (velocityField sol) (velocityFieldDeriv sol)
        0 b 0 ρ (trajectory sol b ρ a)))
      (-(L.comp (variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b 0 r
        (trajectory sol b r a))).comp (velocityFieldDeriv sol r (trajectory sol b r a)))
      (Icc 0 b) r := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hW := hv.hasDerivWithinAt_variationOn_inverse hr h0 a
  have hc := (hasDerivWithinAt_const r (Icc 0 b) L).clm_comp hW
  simpa [trajectory, ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_assoc] using hc

omit h hI in
include hb hv in
/-- The temperature gradient along a trajectory, in the form `∇θ₀(a) ∘ W(r, a)`, is continuous
in time. -/
theorem continuousOn_gradient (L : ℝ^2 →L[ℝ] ℝ) (a : ℝ^2) :
    ContinuousOn (fun ρ ↦ L.comp (variationOn (velocityField sol) (velocityFieldDeriv sol)
      0 b 0 ρ (trajectory sol b ρ a))) (Icc 0 b) := fun _ hr ↦
  (hasDerivWithinAt_gradient hb hv L a hr).continuousWithinAt

include h hb hI hv in
/-- The temperature gradient along a trajectory from the closed half-plane is continuous in
time. -/
theorem continuousOn_fderiv_temperature_trajectory {a : ℝ^2} (ha : 0 ≤ a 1) :
    ContinuousOn (fun r ↦ fderiv ℝ (fun y ↦ sol.temperature y r) (trajectory sol b r a))
      (Icc 0 b) :=
  (continuousOn_gradient hb hv (fderiv ℝ (fun y ↦ sol.temperature y 0) a) a).congr
    fun _ hr ↦ h.fderiv_temperature_trajectory hb hI hv hr ha

include h hb hI hv in
/-- **Two labels: the vorticity.** Along the trajectories from `a` and `a'`, the difference of
the vorticities is at most the initial difference plus the time integral of the difference of the
temperature gradients. -/
theorem norm_vorticity_trajectory_sub_le {a a' : ℝ^2} (ha : 0 ≤ a 1) (ha' : 0 ≤ a' 1) {s : ℝ}
    (hs : s ∈ Icc 0 b) :
    |sol.vorticity (trajectory sol b s a) s - sol.vorticity (trajectory sol b s a') s| ≤
      |sol.vorticity a 0 - sol.vorticity a' 0| +
        ∫ r in (0)..s, ‖fderiv ℝ (fun y ↦ sol.temperature y r) (trajectory sol b r a) -
          fderiv ℝ (fun y ↦ sol.temperature y r) (trajectory sol b r a')‖ := by
  have hsub : Icc 0 s ⊆ Icc 0 b := Icc_subset_Icc le_rfl hs.2
  rw [h.vorticity_trajectory hb hI hv ha hs, h.vorticity_trajectory hb hI hv ha' hs]
  set f : ℝ^2 → ℝ → ℝ := fun c r ↦
    (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory sol b r c)
  have hf (c : ℝ^2) : IntervalIntegrable (f c) volume 0 s :=
    ((h.continuousOn_partialDeriv_temperature_trajectory hb hI hv c).mono
      hsub).intervalIntegrable_of_Icc hs.1
  have hD : ContinuousOn (fun r ↦ ‖fderiv ℝ (fun y ↦ sol.temperature y r) (trajectory sol b r a) -
      fderiv ℝ (fun y ↦ sol.temperature y r) (trajectory sol b r a')‖) (Icc 0 s) :=
    (((h.continuousOn_fderiv_temperature_trajectory hb hI hv ha).sub
      (h.continuousOn_fderiv_temperature_trajectory hb hI hv ha')).mono hsub).norm
  have hsplit : (sol.vorticity a 0 + ∫ r in (0)..s, f a r) - (sol.vorticity a' 0 +
      ∫ r in (0)..s, f a' r) =
        (sol.vorticity a 0 - sol.vorticity a' 0) + ∫ r in (0)..s, (f a r - f a' r) := by
    rw [intervalIntegral.integral_sub (hf a) (hf a')]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_integral_norm hs.1).trans ?_
  refine intervalIntegral.integral_mono_on hs.1 ((hf a).sub (hf a')).norm
    (hD.intervalIntegrable_of_Icc hs.1) fun r _ ↦ ?_
  have he : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by simp
  simp only [f, PDE.partialDeriv]
  rw [← sub_apply]
  exact (ContinuousLinearMap.le_opNorm _ _).trans_eq (by rw [he, mul_one])

include h hb hI in
/-- **Hölder bound of the velocity gradient** at a time of `[0, b]` from an `α`-Hölder bound
`M` of the vorticity on the closed half-plane. -/
theorem norm_velocityFieldDeriv_sub_le {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {r : ℝ}
    (hr : r ∈ Icc 0 b) {M : ℝ}
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      |sol.vorticity y r - sol.vorticity z r| ≤ M * ‖y - z‖ ^ α)
    {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖velocityFieldDeriv sol r x - velocityFieldDeriv sol r y‖ ≤
      844 / (α * (1 - α)) * M * ‖x - y‖ ^ α := by
  obtain ⟨R₀, hR₀⟩ := h.exists_vorticity_eq_zero (hI hr)
  rw [h.velocityFieldDeriv_eq hb hI hr hx, h.velocityFieldDeriv_eq hb hI hr hy, ← dist_eq_norm]
  exact dist_fderivWithin_halfPlaneVelocity_le
    (h.contDiff_vorticity (hI hr)).continuous.continuousOn hR₀ hα hα1 hM hx hy

end Gradient

section Holder

variable {α R N : ℝ}
  (h : IsSolutionOn sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField sol) (velocityFieldDeriv sol) 0 b K)
  (hA : ContinuousOn A (Icc 0 b))
  (hDu : ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖velocityFieldDeriv sol t x‖ ≤ A t)
  (hΛ : ∫ t in (0)..b, A t ≤ Λ)

include h hb hI hv hA hDu hΛ in
/-- **Two labels: the temperature gradients.** Along the trajectories from `a` and `a'`,
`‖∇θ(X(s, a), s) - ∇θ(X(s, a'), s)‖` is at most
`(‖∇θ₀(a) - ∇θ₀(a')‖ + ∫₀ˢ ‖∇θ₀(a')‖ exp Λ ‖Du(X(r, a)) - Du(X(r, a'))‖ dr) exp Λ`. -/
theorem norm_gradient_sub_le {a a' : ℝ^2} (ha : 0 ≤ a 1) (ha' : 0 ≤ a' 1) {s : ℝ}
    (hs : s ∈ Icc 0 b) :
    ‖fderiv ℝ (fun y ↦ sol.temperature y s) (trajectory sol b s a) -
        fderiv ℝ (fun y ↦ sol.temperature y s) (trajectory sol b s a')‖ ≤
      (‖fderiv ℝ (fun y ↦ sol.temperature y 0) a - fderiv ℝ (fun y ↦ sol.temperature y 0) a'‖ +
        ∫ r in (0)..s, ‖fderiv ℝ (fun y ↦ sol.temperature y 0) a'‖ * Real.exp Λ *
          ‖velocityFieldDeriv sol r (trajectory sol b r a) -
            velocityFieldDeriv sol r (trajectory sol b r a')‖) * Real.exp Λ := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hsub : Icc 0 s ⊆ Icc 0 b := Icc_subset_Icc le_rfl hs.2
  set L := fderiv ℝ (fun y ↦ sol.temperature y 0) a
  set L' := fderiv ℝ (fun y ↦ sol.temperature y 0) a'
  set W : ℝ^2 → ℝ → ℝ^2 →L[ℝ] ℝ^2 := fun c ρ ↦
    variationOn (velocityField sol) (velocityFieldDeriv sol) 0 b 0 ρ (trajectory sol b ρ c)
  set Du : ℝ^2 → ℝ → ℝ^2 →L[ℝ] ℝ^2 := fun c ρ ↦
    velocityFieldDeriv sol ρ (trajectory sol b ρ c)
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
    have hXa := h.trajectory_mem hI hL (hsub hρ) ha
    have hsplit : -(L.comp (W a ρ)).comp (Du a ρ) + (L'.comp (W a' ρ)).comp (Du a' ρ) =
        -(F ρ).comp (Du a ρ) - (L'.comp (W a' ρ)).comp (Du a ρ - Du a' ρ) := by
      simp only [F, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
      abel
    rw [hsplit]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (ContinuousLinearMap.opNorm_comp_le _ _))
    rw [norm_neg]
    exact ((F ρ).opNorm_comp_le _).trans
      ((mul_le_mul_of_nonneg_left (hDu ρ (hsub hρ) _ hXa) (norm_nonneg _)).trans_eq (mul_comm _ _))
  have hgron := norm_le_mul_exp_integral (f := F) (A := A) (g := g) (δ := ‖F 0‖) hF
    (hA.mono hsub) (fun ρ hρ ↦ nonneg_of_bound hDu (hsub hρ)) hg
    (fun _ _ ↦ by positivity) le_rfl hbound s ⟨hs.1, le_rfl⟩
  have hW0 (c : ℝ^2) : W c 0 = ContinuousLinearMap.id ℝ (ℝ^2) := by
    simp only [W, trajectory_zero hL hb.le]
    exact hv.variationOn_self h0 c
  have hF0 : F 0 = L - L' := by simp [F, hW0]
  have hFs : F s = fderiv ℝ (fun y ↦ sol.temperature y s) (trajectory sol b s a) -
      fderiv ℝ (fun y ↦ sol.temperature y s) (trajectory sol b s a') := by
    rw [h.fderiv_temperature_trajectory hb hI hv hs ha,
      h.fderiv_temperature_trajectory hb hI hv hs ha']
  have hint : ∫ ρ in (0)..s, g ρ ≤ ∫ ρ in (0)..s, ‖L'‖ * Real.exp Λ * ‖Du a ρ - Du a' ρ‖ := by
    refine intervalIntegral.integral_mono_on hs.1 (hg.intervalIntegrable_of_Icc hs.1)
      ((continuousOn_const.mul (((hDuc a).sub (hDuc a')).mono hsub).norm).intervalIntegrable_of_Icc
        hs.1) fun ρ hρ ↦ ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (L'.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact h.norm_inverseVariation_le hb hI hv hA hDu hΛ (hsub hρ)
      (h.trajectory_mem hI hL (hsub hρ) ha')
  have hexp : Real.exp (∫ ρ in (0)..s, A ρ) ≤ Real.exp Λ :=
    Real.exp_le_exp.mpr (integral_le hb hA hDu hΛ hs)
  rw [hF0, hFs] at hgron
  have hint0 : 0 ≤ ∫ ρ in (0)..s, g ρ :=
    intervalIntegral.integral_nonneg hs.1 fun _ _ ↦ by positivity
  exact hgron.trans (mul_le_mul (add_le_add le_rfl hint) hexp (Real.exp_pos _).le
    (by linarith [norm_nonneg (L - L')]))

omit h hI hv hA in
include hb hDu hΛ in
/-- `Λ ≥ 0`. -/
theorem zero_le_Λ : 0 ≤ Λ :=
  (intervalIntegral.integral_nonneg hb.le fun _ ht ↦ nonneg_of_bound hDu ht).trans hΛ

include h hb hI hv hA hDu hΛ in
/-- **Step A: the Hölder constant of the temperature gradient.** If `M t` is a monotone,
nonnegative `α`-Hölder bound of the vorticity on the closed half-plane at every time of `[0, b]`,
then at time `r` the temperature gradient is `α`-Hölder there with constant
`2N exp(2Λ) + N (844/(α(1-α))) exp(4Λ) ∫₀ʳ M`. -/
theorem norm_fderiv_temperature_sub_le {α R N : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hd : IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N)
    {M : ℝ → ℝ} (hMm : MonotoneOn M (Icc 0 b)) (hM0 : ∀ ρ ∈ Icc 0 b, 0 ≤ M ρ)
    (hM : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      |sol.vorticity y ρ - sol.vorticity z ρ| ≤ M ρ * ‖y - z‖ ^ α)
    {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    ‖fderiv ℝ (fun x ↦ sol.temperature x r) y - fderiv ℝ (fun x ↦ sol.temperature x r) z‖ ≤
      (2 * N * Real.exp Λ ^ 2 + N * (844 / (α * (1 - α))) * Real.exp Λ ^ 4 *
        ∫ ρ in (0)..r, M ρ) * ‖y - z‖ ^ α := by
  have hL := hv.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  set E := Real.exp Λ
  have hE1 : 1 ≤ E := Real.one_le_exp (zero_le_Λ hb hDu hΛ)
  set Cα := 844 / (α * (1 - α))
  have hCα : 0 ≤ Cα := div_nonneg (by norm_num) (mul_nonneg hα.le (by linarith))
  have hsub : Icc 0 r ⊆ Icc 0 b := Icc_subset_Icc le_rfl hr.2
  set a := label sol b y r
  set a' := label sol b z r
  have ha : 0 ≤ a 1 := h.label_mem hI hL hr hy
  have ha' : 0 ≤ a' 1 := h.label_mem hI hL hr hz
  have hya : trajectory sol b r a = y := trajectory_label hL hr y
  have hza : trajectory sol b r a' = z := trajectory_label hL hr z
  have hθ₀d : Differentiable ℝ (fun x ↦ sol.temperature x 0) :=
    (h.contDiff_temperature (hI h0)).differentiable one_ne_zero
  have hθ₀a : ‖fderiv ℝ (fun x ↦ sol.temperature x 0) a'‖ ≤ N := by
    rw [fderiv_eq_fderivWithin hθ₀d ha']
    exact hd.norm_fderivWithin_temperature_le a' ha'
  have hdata : ‖fderiv ℝ (fun x ↦ sol.temperature x 0) a -
      fderiv ℝ (fun x ↦ sol.temperature x 0) a'‖ ≤ 2 * N * ‖a - a'‖ ^ α := by
    rw [fderiv_eq_fderivWithin hθ₀d ha, fderiv_eq_fderivWithin hθ₀d ha']
    exact hd.norm_fderivWithin_temperature_sub_le hα.le hα1.le ha ha'
  have haa : ‖a - a'‖ ^ α ≤ E * ‖y - z‖ ^ α :=
    (Real.rpow_le_rpow (norm_nonneg _) (h.norm_label_sub_le hb hI hv hA hDu hΛ hr hy hz)
      hα.le).trans (mul_rpow_le_mul hE1 (norm_nonneg _) hα1.le)
  set Du : ℝ^2 → ℝ → ℝ^2 →L[ℝ] ℝ^2 := fun c ρ ↦
    velocityFieldDeriv sol ρ (trajectory sol b ρ c)
  have hDuc (c : ℝ^2) : ContinuousOn (Du c) (Icc 0 b) := hv.continuousOn_deriv_flowOn h0 c
  have hint : ∫ ρ in (0)..r, ‖fderiv ℝ (fun x ↦ sol.temperature x 0) a'‖ * E *
      ‖Du a ρ - Du a' ρ‖ ≤ (N * Cα * E ^ 2 * ‖a - a'‖ ^ α) * ∫ ρ in (0)..r, M ρ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hr.1
      ((continuousOn_const.mul (((hDuc a).sub (hDuc a')).mono hsub).norm).intervalIntegrable_of_Icc
        hr.1)
      (((hMm.mono (by rw [uIcc_of_le hr.1]; exact hsub)).intervalIntegrable).const_mul _)
      fun ρ hρ ↦ ?_
    have hρ' := hsub hρ
    have hX := h.norm_trajectory_sub_le hb hI hv hA hDu hΛ hρ' ha ha'
    have hXα : ‖trajectory sol b ρ a - trajectory sol b ρ a'‖ ^ α ≤ E * ‖a - a'‖ ^ α :=
      (Real.rpow_le_rpow (norm_nonneg _) hX hα.le).trans
        (mul_rpow_le_mul hE1 (norm_nonneg _) hα1.le)
    have hDuab := h.norm_velocityFieldDeriv_sub_le hb hI hα hα1 hρ' (hM ρ hρ')
      (h.trajectory_mem hI hL hρ' ha) (h.trajectory_mem hI hL hρ' ha')
    have hMρ := hM0 ρ hρ'
    exact (mul_le_mul (mul_le_mul_of_nonneg_right hθ₀a (by positivity))
      (hDuab.trans (mul_le_mul_of_nonneg_left hXα (by positivity))) (norm_nonneg _)
      (by positivity)).trans_eq (by ring)
  have hkey := h.norm_gradient_sub_le hb hI hv hA hDu hΛ ha ha' hr
  rw [hya, hza] at hkey
  have hI0 : 0 ≤ ∫ ρ in (0)..r, M ρ :=
    intervalIntegral.integral_nonneg hr.1 fun ρ hρ ↦ hM0 ρ (hsub hρ)
  have hc0 : 0 ≤ (2 * N + N * Cα * E ^ 2 * ∫ ρ in (0)..r, M ρ) * E := by positivity
  linarith [mul_le_mul_of_nonneg_right (add_le_add hdata hint) (zero_le_one.trans hE1),
    mul_le_mul_of_nonneg_left haa hc0]

include h hb hI hv hA hDu hΛ in
/-- **Step B: the Hölder constant of the vorticity.** If `Q t` is a monotone, nonnegative
`α`-Hölder bound of the temperature gradient on the closed half-plane at every time of `[0, b]`,
then at time `r` the vorticity is `α`-Hölder there with constant
`2N exp Λ + exp (2Λ) ∫₀ʳ Q`. -/
theorem abs_vorticity_sub_le {α R N : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hd : IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N)
    {Q : ℝ → ℝ} (hQm : MonotoneOn Q (Icc 0 b)) (hQ0 : ∀ ρ ∈ Icc 0 b, 0 ≤ Q ρ)
    (hQ : ∀ ρ ∈ Icc 0 b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderiv ℝ (fun x ↦ sol.temperature x ρ) y - fderiv ℝ (fun x ↦ sol.temperature x ρ) z‖ ≤
        Q ρ * ‖y - z‖ ^ α)
    {r : ℝ} (hr : r ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    |sol.vorticity y r - sol.vorticity z r| ≤
      (2 * N * Real.exp Λ + Real.exp Λ ^ 2 * ∫ ρ in (0)..r, Q ρ) * ‖y - z‖ ^ α := by
  have hL := hv.isLipschitzFieldOn
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  set E := Real.exp Λ
  have hE1 : 1 ≤ E := Real.one_le_exp (zero_le_Λ hb hDu hΛ)
  have hsub : Icc 0 r ⊆ Icc 0 b := Icc_subset_Icc le_rfl hr.2
  set a := label sol b y r
  set a' := label sol b z r
  have ha : 0 ≤ a 1 := h.label_mem hI hL hr hy
  have ha' : 0 ≤ a' 1 := h.label_mem hI hL hr hz
  have hya : trajectory sol b r a = y := trajectory_label hL hr y
  have hza : trajectory sol b r a' = z := trajectory_label hL hr z
  have haa : ‖a - a'‖ ^ α ≤ E * ‖y - z‖ ^ α :=
    (Real.rpow_le_rpow (norm_nonneg _) (h.norm_label_sub_le hb hI hv hA hDu hΛ hr hy hz)
      hα.le).trans (mul_rpow_le_mul hE1 (norm_nonneg _) hα1.le)
  have hD : ContinuousOn (fun ρ ↦ ‖fderiv ℝ (fun y ↦ sol.temperature y ρ)
      (trajectory sol b ρ a) - fderiv ℝ (fun y ↦ sol.temperature y ρ)
        (trajectory sol b ρ a')‖) (Icc 0 r) :=
    (((h.continuousOn_fderiv_temperature_trajectory hb hI hv ha).sub
      (h.continuousOn_fderiv_temperature_trajectory hb hI hv ha')).mono hsub).norm
  have hint : ∫ ρ in (0)..r, ‖fderiv ℝ (fun y ↦ sol.temperature y ρ) (trajectory sol b ρ a) -
      fderiv ℝ (fun y ↦ sol.temperature y ρ) (trajectory sol b ρ a')‖ ≤
        (E * ‖a - a'‖ ^ α) * ∫ ρ in (0)..r, Q ρ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hr.1 (hD.intervalIntegrable_of_Icc hr.1)
      (((hQm.mono (by rw [uIcc_of_le hr.1]; exact hsub)).intervalIntegrable).const_mul _)
      fun ρ hρ ↦ ?_
    have hρ' := hsub hρ
    have hX := h.norm_trajectory_sub_le hb hI hv hA hDu hΛ hρ' ha ha'
    have hXα : ‖trajectory sol b ρ a - trajectory sol b ρ a'‖ ^ α ≤ E * ‖a - a'‖ ^ α :=
      (Real.rpow_le_rpow (norm_nonneg _) hX hα.le).trans
        (mul_rpow_le_mul hE1 (norm_nonneg _) hα1.le)
    exact ((hQ ρ hρ' _ _ (h.trajectory_mem hI hL hρ' ha)
      (h.trajectory_mem hI hL hρ' ha')).trans
        (mul_le_mul_of_nonneg_left hXα (hQ0 ρ hρ'))).trans_eq (by ring)
  have hkey := h.norm_vorticity_trajectory_sub_le hb hI hv ha ha' hr
  rw [hya, hza] at hkey
  have hdata := hd.abs_vorticity_sub_le hα.le hα1.le ha ha'
  have hI0 : 0 ≤ ∫ ρ in (0)..r, Q ρ :=
    intervalIntegral.integral_nonneg hr.1 fun ρ hρ ↦ hQ0 ρ (hsub hρ)
  have hc0 : 0 ≤ 2 * N + E * ∫ ρ in (0)..r, Q ρ := by positivity
  linarith [mul_le_mul_of_nonneg_left haa hc0]

include h hb hI hv hA hDu hΛ in
/-- **Hölder bounds of the vorticity and of the temperature gradient.** For a solution on
`[0, b]` whose slices are data of the class `IsHolderData` with some bounds (`hreg`, a
qualitative hypothesis), with data at time `0` of the class `IsHolderData … α R N`, `‖Du‖ ≤ A` on
the closed half-plane and `∫₀ᵇ A ≤ Λ`, at every time of `[0, b]` the vorticity is `α`-Hölder on
the closed half-plane with constant `vorticityHolderBound α N Λ b` and the temperature gradient
with constant `gradientHolderBound α N Λ b`, which depend only on `α`, `N`, `Λ` and `b`. -/
theorem holder_bound {α R N Rq Nq : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hd : IsHolderData (fun x ↦ sol.vorticity x 0) (fun x ↦ sol.temperature x 0) α R N)
    (hreg : ∀ t ∈ Icc 0 b,
      IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α Rq Nq)
    {s : ℝ} (hs : s ∈ Icc 0 b) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    |sol.vorticity y s - sol.vorticity z s| ≤ vorticityHolderBound α N Λ b * ‖y - z‖ ^ α ∧
      ‖fderiv ℝ (fun x ↦ sol.temperature x s) y - fderiv ℝ (fun x ↦ sol.temperature x s) z‖ ≤
        gradientHolderBound α N Λ b * ‖y - z‖ ^ α := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  set E := Real.exp Λ
  have hE1 : 1 ≤ E := Real.one_le_exp (zero_le_Λ hb hDu hΛ)
  set Cα := 844 / (α * (1 - α))
  have hCα : 0 ≤ Cα := div_nonneg (by norm_num) (mul_nonneg hα.le (by linarith))
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
    fderiv_eq_fderivWithin ((h.contDiff_temperature (hI hr)).differentiable one_ne_zero) hx
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
  have hA' : ∀ r ∈ Icc 0 b, Qθ r ≤ 2 * N * E ^ 2 + N * Cα * E ^ 4 * ∫ ρ in (0)..r, Mω ρ :=
    fun r hr ↦ holderSup_le hr.1 fun ρ hρ y z hy hz hyz ↦ by
      have hρ' : ρ ∈ Icc 0 b := ⟨hρ.1, hρ.2.trans hr.2⟩
      refine hdiv hyz ((h.norm_fderiv_temperature_sub_le hb hI hv hA hDu hΛ hα hα1 hd hMm hM0
        hMω hρ' hy hz).trans (mul_le_mul_of_nonneg_right ?_ (by positivity)))
      gcongr 2 * N * E ^ 2 + N * Cα * E ^ 4 * ?_
      exact integral_le_integral_of_monotoneOn hMm hM0 hρ.1 hρ.2 hr.2
  -- Step B: the vorticity.
  have hB' : ∀ r ∈ Icc 0 b, Mω r ≤ 2 * N * E + E ^ 2 * ∫ ρ in (0)..r, Qθ ρ :=
    fun r hr ↦ holderSup_le hr.1 fun ρ hρ y z hy hz hyz ↦ by
      have hρ' : ρ ∈ Icc 0 b := ⟨hρ.1, hρ.2.trans hr.2⟩
      refine hdiv hyz ?_
      rw [Real.norm_eq_abs]
      refine (h.abs_vorticity_sub_le hb hI hv hA hDu hΛ hα hα1 hd hQm hQ0 hQθ hρ' hy hz).trans
        (mul_le_mul_of_nonneg_right ?_ (by positivity))
      gcongr 2 * N * E + E ^ 2 * ?_
      exact integral_le_integral_of_monotoneOn hQm hQ0 hρ.1 hρ.2 hr.2
  -- Step C: the closed inequality for the vorticity.
  set c := 2 * N * E * (1 + E ^ 3 * b)
  set C := N * Cα * E ^ 6 * b
  have hC0 : 0 ≤ C := by positivity
  have hc0 : 0 ≤ c := by positivity
  -- `∫₀ʳ f ≤ b V` for a nonnegative `f ≤ V` on `(0, r]`
  have hintb {f : ℝ → ℝ} {V r : ℝ} (hr : r ∈ Icc 0 b) (hf0 : ∀ ρ ∈ Icc 0 b, 0 ≤ f ρ)
      (hV : 0 ≤ V) (hf : ∀ ρ ∈ Ioc 0 r, f ρ ≤ V) : ∫ ρ in (0)..r, f ρ ≤ b * V := by
    calc ∫ ρ in (0)..r, f ρ ≤ ‖∫ ρ in (0)..r, f ρ‖ := le_abs_self _
      _ ≤ V * |r - 0| := intervalIntegral.norm_integral_le_of_norm_le_const fun ρ hρ ↦ by
          rw [uIoc_of_le hr.1] at hρ
          rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ρ ⟨hρ.1.le, hρ.2.trans hr.2⟩)]
          exact hf ρ hρ
      _ ≤ b * V := by rw [sub_zero, abs_of_nonneg hr.1, mul_comm]; gcongr; exact hr.2
  have hclosed : ∀ r ∈ Icc 0 b, Mω r ≤ c + C * ∫ ρ in (0)..r, Mω ρ := fun r hr ↦ by
    have hIM : 0 ≤ ∫ ρ in (0)..r, Mω ρ :=
      intervalIntegral.integral_nonneg hr.1 fun ρ hρ ↦ hM0 ρ ⟨hρ.1, hρ.2.trans hr.2⟩
    have hIQ : ∫ ρ in (0)..r, Qθ ρ ≤ b * (2 * N * E ^ 2 + N * Cα * E ^ 4 * ∫ ρ in (0)..r, Mω ρ) :=
      hintb hr hQ0 (by positivity) fun ρ hρ ↦ (hA' ρ ⟨hρ.1.le, hρ.2.trans hr.2⟩).trans (by
        gcongr 2 * N * E ^ 2 + N * Cα * E ^ 4 * ?_
        exact integral_le_integral_of_monotoneOn hMm hM0 hρ.1.le hρ.2 hr.2)
    calc Mω r ≤ 2 * N * E + E ^ 2 * ∫ ρ in (0)..r, Qθ ρ := hB' r hr
      _ ≤ 2 * N * E + E ^ 2 * (b * (2 * N * E ^ 2 + N * Cα * E ^ 4 * ∫ ρ in (0)..r, Mω ρ)) := by
          gcongr
      _ = c + C * ∫ ρ in (0)..r, Mω ρ := by simp only [c, C]; ring
  -- Step D: Grönwall.
  have hgron := le_of_le_add_integral_of_monotoneOn hc0 hC0 hMm hclosed
  have hMb : ∀ r ∈ Icc 0 b, Mω r ≤ vorticityHolderBound α N Λ b := fun r hr ↦ by
    have hv : vorticityHolderBound α N Λ b = c * (1 + C * b * Real.exp (C * b)) := rfl
    refine (hgron r hr).trans (hv ▸ mul_le_mul_of_nonneg_left ?_ hc0)
    have hrb : r ≤ b := hr.2
    gcongr
  have hQb : Qθ s ≤ gradientHolderBound α N Λ b := by
    have hg : gradientHolderBound α N Λ b =
        2 * N * E ^ 2 + N * Cα * E ^ 4 * (b * vorticityHolderBound α N Λ b) := rfl
    refine (hA' s hs).trans (hg ▸ ?_)
    gcongr 2 * N * E ^ 2 + N * Cα * E ^ 4 * ?_
    exact hintb hs hM0 ((hM0 s hs).trans (hMb s hs)) fun ρ hρ ↦ hMb ρ ⟨hρ.1.le, hρ.2.trans hs.2⟩
  refine ⟨(hMω s hs y z hy hz).trans
    (mul_le_mul_of_nonneg_right (hMb s hs) (by positivity)), (hQθ s hs y z hy hz).trans
    (mul_le_mul_of_nonneg_right hQb (by positivity))⟩

end Holder

end IsSolutionOn

end Boussinesq.HalfPlane
