/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy
public import PDE.Hyperbolic.ConservationLaw.Riemann.Data
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Burgers Riemann profiles

We formalize explicit shock and rarefaction profiles for the
one-dimensional inviscid Burgers equation

`u_t + u * u_x = 0`

and prove:

* the Rankine–Hugoniot speed for the Burgers flux `f(u)=u^2/2` is `(uL+uR)/2`;
* the Lax shock inequalities for Burgers;
* the self-similar rarefaction profile `u(t,x)=x/t` satisfies the Burgers PDE away from `t=0`;
* the piecewise-constant shock profile satisfies the Burgers PDE on each strict side of the
  shock.

## Main declarations

* `flux`, `shockSpeed`: the Burgers flux and the speed `(uL + uR)/2`.
  Initial data use the shared `PDE.Hyperbolic.ConservationLaw.riemannData`.
* `rarefactionProfile`, `shockProfile`, `riemannSolution`: the explicit profiles and the unified
  solution, which is the shock for `uR < uL` and the rarefaction otherwise.
* `rankineHugoniot_shockSpeed`, `laxShock_admissible_shockSpeed_iff`: the jump condition and the
  Lax inequalities, the latter holding exactly on the decreasing branch.
* `pde_ratio`, `pde_rarefaction_fan`, `pde_shock_left`, `pde_shock_right`: the pointwise
  classical equation away from the singular sets.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1, equations (12) and (17), Examples 1 and 2; §3.4.4,
  Theorem 4, equations (54)-(56).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv)

namespace BurgersEquation.Riemann

noncomputable section

open scoped BigOperators
open scoped Topology
open PDE.Common PDE.Hyperbolic.ConservationLaw

/-- The Burgers flux `f(u)=u^2/2`. -/
noncomputable def flux (u : ℝ) : ℝ := u ^ 2 / 2

/-- The derivative of the Burgers flux is the identity. -/
theorem deriv_flux (u : ℝ) : deriv flux u = u := by
  cas

/-- Shock speed `(uL + uR) / 2`. -/
noncomputable def shockSpeed (uL uR : ℝ) : ℝ := (uL + uR) / 2

/-- The Burgers shock speed is the Rankine–Hugoniot speed for distinct states. -/
theorem rankineHugoniotSpeed_eq_shockSpeed {uL uR : ℝ} (h : uR ≠ uL) :
    PDE.Hyperbolic.ConservationLaw.Scalar.rankineHugoniotSpeed flux uL uR = shockSpeed uL uR := by
  unfold PDE.Hyperbolic.ConservationLaw.Scalar.rankineHugoniotSpeed flux shockSpeed
  cas

/-- The Burgers shock speed satisfies the Rankine–Hugoniot jump condition. -/
theorem rankineHugoniot_shockSpeed (uL uR : ℝ) :
    PDE.Hyperbolic.ConservationLaw.Scalar.RankineHugoniot flux uL uR (shockSpeed uL uR) := by
  unfold PDE.Hyperbolic.ConservationLaw.Scalar.RankineHugoniot flux shockSpeed
  cas

/-- The mean shock speed lies strictly between decreasing end states. -/
theorem shockSpeed_mem_Ioo {uL uR : ℝ} (h : uR < uL) :
    shockSpeed uL uR ∈ Set.Ioo uR uL := by
  unfold shockSpeed
  constructor <;> linarith

/-- Self-similar profile `u(t,x)=x/t`.

At `t = 0` the totalized inverse gives the value zero. -/
noncomputable def ratio (x : ℝ^2) : ℝ :=
  x 1 * (x 0)⁻¹

/-- Rarefaction profile for `uL ≤ uR`: constant outside the fan, and `x/t` inside.

The pointwise PDE holds away from `t = 0` in the interior of the fan. -/
noncomputable def rarefactionProfile (uL uR : ℝ) : ℝ^2 → ℝ :=
  fun x ↦
    let ξ := ratio x
    if ξ < uL then uL else if uR < ξ then uR else ξ

/-- A rarefaction profile with equal end states is constant: the fan has zero width, so the
clamping returns `u` everywhere. -/
@[simp]
theorem rarefactionProfile_self (u : ℝ) :
    rarefactionProfile u u = fun _ : ℝ^2 ↦ u := by
  funext x
  by_cases hlt : ratio x < u
  · simp [rarefactionProfile, hlt]
  · have hle : u ≤ ratio x := le_of_not_gt hlt
    by_cases hgt : u < ratio x
    · simp [rarefactionProfile, hlt, hgt]
    · have heq : ratio x = u := le_antisymm (le_of_not_gt hgt) hle
      simp [rarefactionProfile, heq]

/-- A rarefaction profile is bounded by the larger of its end states in absolute value. -/
theorem norm_rarefactionProfile_le {uL uR : ℝ} (x : ℝ^2) :
    ‖rarefactionProfile uL uR x‖ ≤ max ‖uL‖ ‖uR‖ := by
  by_cases hL : ratio x < uL
  · rw [rarefactionProfile, ite_eq_left hL]
    exact le_max_left ‖uL‖ ‖uR‖
  · by_cases hR : uR < ratio x
    · rw [rarefactionProfile, ite_eq_right hL, ite_eq_left hR]
      exact le_max_right ‖uL‖ ‖uR‖
    · have hrange : uL ≤ ratio x ∧ ratio x ≤ uR := ⟨le_of_not_gt hL, le_of_not_gt hR⟩
      simpa [rarefactionProfile, hL, hR, Real.norm_eq_abs] using
        abs_le_max_abs_abs hrange.1 hrange.2

/-- In the left constant region of a rarefaction profile, the value is the left state. -/
theorem rarefactionProfile_eq_left {uL uR : ℝ} {x : ℝ^2} (h : ratio x < uL) :
    rarefactionProfile uL uR x = uL := by
  simp [rarefactionProfile, h]

/-- In the right constant region of an increasing rarefaction profile, the value is the right
state. The hypothesis `uL ≤ uR` covers constant data and the rarefaction case of Evans, §3.4.4,
Theorem 4(ii). -/
theorem rarefactionProfile_eq_right {uL uR : ℝ} (hLR : uL ≤ uR) {x : ℝ^2} (h : uR < ratio x) :
    rarefactionProfile uL uR x = uR := by
  have hnotLeft : ¬ ratio x < uL := not_lt_of_ge (le_trans hLR (le_of_lt h))
  simp [rarefactionProfile, hnotLeft, h]

/-- Inside the rarefaction fan, the profile equals the self-similar ratio `x/t`. -/
theorem rarefactionProfile_eq_ratio {uL uR : ℝ} {x : ℝ^2} (hL : uL ≤ ratio x) (hR : ratio x ≤ uR) :
    rarefactionProfile uL uR x = ratio x := by
  have hnotLeft : ¬ ratio x < uL := not_lt_of_ge hL
  have hnotRight : ¬ uR < ratio x := not_lt_of_ge hR
  simp [rarefactionProfile, hnotLeft, hnotRight]

private theorem partialDeriv_ratio_time (x : ℝ^2) (ht : x 0 ≠ 0) :
    (∂[(0 : Fin 2)] ratio) x = -(x 1) * (x 0)⁻¹ * (x 0)⁻¹ := by
  cas

private theorem partialDeriv_ratio_space (x : ℝ^2) (ht : x 0 ≠ 0) :
    (∂[(1 : Fin 2)] ratio) x = (x 0)⁻¹ := by
  cas

/-- The self-similar ratio is `C¹` away from the hyperplane `t = 0`. -/
theorem contDiffAt_ratio {x : ℝ^2} (ht : x 0 ≠ 0) :
    ContDiffAt ℝ 1 ratio x := by
  have hspace :
      ContDiffAt ℝ 1 (fun y : ℝ^2 ↦ y 1) x := by
    cas
  have htime :
      ContDiffAt ℝ 1 (fun y : ℝ^2 ↦ y 0) x := by
    cas
  change ContDiffAt ℝ 1 (fun y : ℝ^2 ↦ y 1 * (y 0)⁻¹) x
  exact hspace.mul (htime.inv ht)

/-- The self-similar ratio is differentiable away from the hyperplane
`t = 0`. -/
theorem differentiableAt_ratio {x : ℝ^2} (ht : x 0 ≠ 0) :
    DifferentiableAt ℝ ratio x :=
  (contDiffAt_ratio ht).differentiableAt_one

/-- The self-similar profile `u(t,x)=x/t` satisfies the Burgers PDE wherever `t ≠ 0`. -/
theorem pde_ratio (x : ℝ^2) (ht : x 0 ≠ 0) :
    (∂[(0 : Fin 2)] ratio) x + ratio x * (∂[(1 : Fin 2)] ratio) x = 0 := by
  rw [partialDeriv_ratio_time x ht, partialDeriv_ratio_space x ht]
  unfold ratio
  cas

/-- Differentiating the Burgers flux after the self-similar ratio gives the
quasilinear spatial term. -/
theorem partialDeriv_flux_ratio (i : Fin 2) (x : ℝ^2) (ht : x 0 ≠ 0) :
    (∂[i] (fun y : ℝ^2 ↦ flux (ratio y))) x = ratio x * (∂[i] ratio) x := by
  match i with
  | 0 =>
    rw [partialDeriv_ratio_time x ht]
    cas
  | 1 =>
    rw [partialDeriv_ratio_space x ht]
    cas

/-- The self-similar ratio satisfies Burgers' conservation form away from
`t = 0`. -/
theorem conservation_ratio (x : ℝ^2) (ht : x 0 ≠ 0) :
    (∂[(0 : Fin 2)] ratio) x + (∂[(1 : Fin 2)] (fun y : ℝ^2 ↦ flux (ratio y))) x = 0 := by
  rw [partialDeriv_flux_ratio (1 : Fin 2) x ht]
  exact pde_ratio x ht

/-- Burgers PDE holds in the interior of the rarefaction fan, where the profile equals `ratio`. -/
theorem pde_rarefaction_fan {uL uR : ℝ} {x : ℝ^2} (ht : x 0 ≠ 0)
    (hx : uL < ratio x ∧ ratio x < uR) :
    (∂[(0 : Fin 2)] (rarefactionProfile uL uR)) x +
        rarefactionProfile uL uR x * (∂[(1 : Fin 2)] (rarefactionProfile uL uR)) x = 0 := by
  -- `ratio` is continuous at `x` (since `t ≠ 0`), hence the strict inequalities persist locally.
  have hcont1 : ContinuousAt (fun y : ℝ^2 ↦ y (1 : Fin 2)) x :=
    by
      simpa only [EuclideanSpace.coe_proj] using
        (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).continuous.continuousAt
  have hcont0 : ContinuousAt (fun y : ℝ^2 ↦ y (0 : Fin 2)) x :=
    by
      simpa only [EuclideanSpace.coe_proj] using
        (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).continuous.continuousAt
  have hcontInv : ContinuousAt (fun y : ℝ^2 ↦ (y (0 : Fin 2))⁻¹) x := (hcont0.inv₀ ht)
  have hcontRatio : ContinuousAt ratio x := by
    rw [show ratio =
        (fun y : ℝ^2 ↦ y (1 : Fin 2)) * fun y : ℝ^2 ↦ (y (0 : Fin 2))⁻¹ by
          rfl]
    exact hcont1.mul hcontInv
  have htIoo : Set.Ioo uL uR ∈ 𝓝 (ratio x) := (isOpen_Ioo.mem_nhds hx)
  have hmem : ∀ᶠ y : ℝ^2 in 𝓝 x, ratio y ∈ Set.Ioo uL uR := hcontRatio.preimage_mem_nhds htIoo
  have hEq : rarefactionProfile uL uR =ᶠ[𝓝 x] ratio := by
    refine hmem.mono ?_
    intro y hy
    have hnotLeft : ¬ ratio y < uL := not_lt_of_ge (le_of_lt hy.1)
    have hnotRight : ¬ uR < ratio y := not_lt_of_ge (le_of_lt hy.2)
    simp [rarefactionProfile, hnotLeft, hnotRight]
  have hfderiv : fderiv ℝ (rarefactionProfile uL uR) x = fderiv ℝ ratio x := hEq.fderiv_eq
  have hpd0 : (∂[(0 : Fin 2)] (rarefactionProfile uL uR)) x =
      (∂[(0 : Fin 2)] ratio) x := by
    unfold partialDeriv
    simp [hfderiv]
  have hpd1 : (∂[(1 : Fin 2)] (rarefactionProfile uL uR)) x =
      (∂[(1 : Fin 2)] ratio) x := by
    unfold partialDeriv
    simp [hfderiv]
  have hxVal : rarefactionProfile uL uR x = ratio x := by
    have hnotLeft : ¬ ratio x < uL := not_lt_of_ge (le_of_lt hx.1)
    have hnotRight : ¬ uR < ratio x := not_lt_of_ge (le_of_lt hx.2)
    simp [rarefactionProfile, hnotLeft, hnotRight]
  simpa [hpd0, hpd1, hxVal] using (pde_ratio (x := x) ht)

/-- The Burgers shock speed is Lax-admissible on the decreasing-state branch. -/
theorem laxShock_admissible_shockSpeed {uL uR : ℝ} (h : uR < uL) :
    PDE.Hyperbolic.ConservationLaw.Scalar.LaxShock (fun r : ℝ ↦ r) uL uR (shockSpeed uL uR) := by
  exact shockSpeed_mem_Ioo h

/-- For Burgers, Lax admissibility of the named shock speed is exactly the
decreasing-state shock branch of the Riemann problem. -/
theorem laxShock_admissible_shockSpeed_iff {uL uR : ℝ} :
    PDE.Hyperbolic.ConservationLaw.Scalar.LaxShock
      (fun r : ℝ ↦ r) uL uR (shockSpeed uL uR) ↔ uR < uL := by
  constructor
  · intro h
    exact PDE.Hyperbolic.ConservationLaw.Scalar.LaxShock.right_state_lt_left_state strictMono_id h
  · exact laxShock_admissible_shockSpeed

/-- Piecewise-constant shock profile, with the right state chosen on the shock line.

Classical PDE theorems are stated only on the strict left/right regions; weak solution theorems
handle the shock line separately through Rankine–Hugoniot. -/
noncomputable def shockProfile (uL uR : ℝ) : ℝ^2 → ℝ :=
  fun x ↦ if x 1 < shockSpeed uL uR * x 0 then uL else uR

/-- A shock profile with equal states is constant. -/
@[simp]
theorem shockProfile_self (u : ℝ) :
    shockProfile u u = fun _ : ℝ^2 ↦ u := by
  funext x
  simp [shockProfile]

/-- The Burgers shock profile has the prescribed Riemann trace on the initial line `t = 0`.
The right state is used at `x = 0`, matching the convention in `riemannData`. -/
theorem shockProfile_initial_trace {uL uR : ℝ} {x : ℝ^2} (ht : x 0 = 0) :
    shockProfile uL uR x = riemannData uL uR (x 1) := by
  by_cases hx : x 1 < 0
  · have hleft : x 1 < shockSpeed uL uR * x 0 := by
      simpa [ht] using hx
    simp [shockProfile, riemannData, hleft, hx]
  · have hright : ¬ x 1 < shockSpeed uL uR * x 0 := by
      simpa [ht] using hx
    simp [shockProfile, riemannData, hright, hx]

private theorem isOpen_shockLeft (uL uR : ℝ) :
    IsOpen {x : ℝ^2 | x 1 < shockSpeed uL uR * x 0} := by
  -- `x ↦ x₁` and `x ↦ s*x₀` are continuous, so `{x | x₁ < s*x₀}` is open.
  refine isOpen_lt ?_ ?_
  · simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).continuous
  · have : Continuous fun x : ℝ^2 ↦ shockSpeed uL uR * x (0 : Fin 2) :=
        continuous_const.mul <| by
          simpa only [EuclideanSpace.coe_proj] using
            (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).continuous
    simpa using this

private theorem isOpen_shockRight (uL uR : ℝ) :
    IsOpen {x : ℝ^2 | shockSpeed uL uR * x 0 < x 1} := by
  refine isOpen_lt ?_ ?_
  · have : Continuous fun x : ℝ^2 ↦ shockSpeed uL uR * x (0 : Fin 2) :=
        continuous_const.mul <| by
          simpa only [EuclideanSpace.coe_proj] using
            (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).continuous
    simpa using this
  · simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).continuous

/-- On the strict-left region, `shockProfile` is locally constant `uL`. -/
private theorem shockProfile_eventuallyEq_left {uL uR : ℝ} {x : ℝ^2}
    (hx : x 1 < shockSpeed uL uR * x 0) :
    shockProfile uL uR =ᶠ[𝓝 x] fun _ : ℝ^2 ↦ uL := by
  have hmem : ∀ᶠ y : ℝ^2 in 𝓝 x, y 1 < shockSpeed uL uR * y 0 :=
    (isOpen_shockLeft uL uR).mem_nhds hx
  refine hmem.mono ?_
  intro y hy
  simp [shockProfile, hy]

/-- On the strict-right region, `shockProfile` is locally constant `uR`. -/
private theorem shockProfile_eventuallyEq_right {uL uR : ℝ} {x : ℝ^2}
    (hx : shockSpeed uL uR * x 0 < x 1) :
    shockProfile uL uR =ᶠ[𝓝 x] fun _ : ℝ^2 ↦ uR := by
  have hmem : ∀ᶠ y : ℝ^2 in 𝓝 x, shockSpeed uL uR * y 0 < y 1 :=
    (isOpen_shockRight uL uR).mem_nhds hx
  refine hmem.mono ?_
  intro y hy
  have : ¬ y 1 < shockSpeed uL uR * y 0 := not_lt_of_ge (le_of_lt hy)
  simp [shockProfile, this]

private theorem partialDeriv_shockProfile_left {uL uR : ℝ} {x : ℝ^2}
    (hx : x 1 < shockSpeed uL uR * x 0) (i : Fin 2) :
    (∂[i] (shockProfile uL uR)) x = 0 := by
  have hEq : shockProfile uL uR =ᶠ[𝓝 x] fun _ : ℝ^2 ↦ uL :=
    shockProfile_eventuallyEq_left (uL := uL) (uR := uR) hx
  have hf : fderiv ℝ (shockProfile uL uR) x = fderiv ℝ (fun _ : ℝ^2 ↦ uL) x := hEq.fderiv_eq
  unfold partialDeriv
  rw [hf]
  simp

private theorem partialDeriv_shockProfile_right {uL uR : ℝ} {x : ℝ^2}
    (hx : shockSpeed uL uR * x 0 < x 1) (i : Fin 2) :
    (∂[i] (shockProfile uL uR)) x = 0 := by
  have hEq : shockProfile uL uR =ᶠ[𝓝 x] fun _ : ℝ^2 ↦ uR :=
    shockProfile_eventuallyEq_right (uL := uL) (uR := uR) hx
  have hf : fderiv ℝ (shockProfile uL uR) x = fderiv ℝ (fun _ : ℝ^2 ↦ uR) x := hEq.fderiv_eq
  unfold partialDeriv
  rw [hf]
  simp

/-- Burgers PDE holds pointwise on the strict-left side of the shock (classical region). -/
theorem pde_shock_left {uL uR : ℝ} {x : ℝ^2} (hx : x 1 < shockSpeed uL uR * x 0) :
    (∂[(0 : Fin 2)] (shockProfile uL uR)) x +
        shockProfile uL uR x * (∂[(1 : Fin 2)] (shockProfile uL uR)) x = 0 := by
  have ht : (∂[(0 : Fin 2)] (shockProfile uL uR)) x = 0 :=
    partialDeriv_shockProfile_left (uL := uL) (uR := uR) hx (i := (0 : Fin 2))
  have hx' : (∂[(1 : Fin 2)] (shockProfile uL uR)) x = 0 :=
    partialDeriv_shockProfile_left (uL := uL) (uR := uR) hx (i := (1 : Fin 2))
  simp [ht, hx']

/-- Burgers PDE holds pointwise on the strict-right side of the shock (classical region). -/
theorem pde_shock_right {uL uR : ℝ} {x : ℝ^2} (hx : shockSpeed uL uR * x 0 < x 1) :
    (∂[(0 : Fin 2)] (shockProfile uL uR)) x +
        shockProfile uL uR x * (∂[(1 : Fin 2)] (shockProfile uL uR)) x = 0 := by
  have ht : (∂[(0 : Fin 2)] (shockProfile uL uR)) x = 0 :=
    partialDeriv_shockProfile_right (uL := uL) (uR := uR) hx (i := (0 : Fin 2))
  have hx' : (∂[(1 : Fin 2)] (shockProfile uL uR)) x = 0 :=
    partialDeriv_shockProfile_right (uL := uL) (uR := uR) hx (i := (1 : Fin 2))
  simp [ht, hx']

/-- Unified 1D Burgers Riemann solution.

For decreasing data it is the shock profile. For nondecreasing data it is the rarefaction
profile at nonzero times and the prescribed Riemann datum on the initial slice. The explicit
time-zero branch avoids interpreting the totalized quotient `x / 0` as an initial value. -/
noncomputable def riemannSolution (uL uR : ℝ) : ℝ^2 → ℝ :=
  if uR < uL then
    shockProfile uL uR
  else
    fun x ↦
      if x 0 = 0 then riemannData uL uR (x 1) else rarefactionProfile uL uR x

/-- Decreasing Riemann data select the shock profile. -/
@[simp] theorem riemannSolution_of_lt {uL uR : ℝ} (h : uR < uL) :
    riemannSolution uL uR = shockProfile uL uR := by
  simp [riemannSolution, h]

/-- Away from the initial slice, the nondecreasing branch is exactly the rarefaction profile. -/
@[simp] theorem riemannSolution_apply_of_not_lt_of_time_ne_zero {uL uR : ℝ}
    (h : ¬ uR < uL) {x : ℝ^2} (ht : x 0 ≠ 0) :
    riemannSolution uL uR x = rarefactionProfile uL uR x := by
  simp [riemannSolution, h, ht]

/-- On any set avoiding `t = 0`, the nondecreasing Riemann solution agrees with the
rarefaction profile. -/
theorem riemannSolution_eqOn_rarefactionProfile_of_not_lt {uL uR : ℝ} (h : ¬ uR < uL) :
    Set.EqOn (riemannSolution uL uR) (rarefactionProfile uL uR) {x : ℝ^2 | x 0 ≠ 0} := by
  intro x hx
  exact riemannSolution_apply_of_not_lt_of_time_ne_zero h hx

/-- The Riemann solution for equal states is the constant solution `u`, on both the initial
slice and positive time. -/
@[simp]
theorem riemannSolution_self (u : ℝ) :
    riemannSolution u u = fun _ : ℝ^2 ↦ u := by
  funext x
  by_cases ht : x 0 = 0
  · simp [riemannSolution, ht, riemannData]
  · simp [riemannSolution, ht]

/-- The unified Riemann solution has the prescribed value on the initial line for both the
shock and rarefaction branches. -/
theorem riemannSolution_timeZero_value (uL uR : ℝ) {x : ℝ^2} (ht : x 0 = 0) :
    riemannSolution uL uR x = riemannData uL uR (x 1) := by
  by_cases h : uR < uL
  · simpa [riemannSolution_of_lt h] using
      (shockProfile_initial_trace (uL := uL) (uR := uR) (x := x) ht)
  · simp [riemannSolution, h, ht]

end

end BurgersEquation.Riemann
