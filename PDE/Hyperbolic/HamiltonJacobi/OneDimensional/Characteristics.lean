/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
import PDE.FDeriv.Calculus
import CAS.ExactTactic

/-!
# One-dimensional Hamilton–Jacobi characteristics

We study the characteristic formula for

`u_t + H(u_x) = 0`, `u(0, x) = φ(x)`.

A footpoint map `ξ(t, x)` is required to satisfy

`x = ξ(t, x) + t H'(φ'(ξ(t, x)))`.

The relation is stated at one point, on a set, and eventually near a point. The
neighborhood form is the one needed to differentiate the identity. If the footpoint
Jacobian does not vanish, the characteristic formula has the expected spatial and time
derivatives and therefore satisfies the Hamilton–Jacobi equation.

The local construction of the footpoint map by the inverse function theorem is
proved in `OneDimensional.Characteristics.LocalInverse`.

The characteristic equations are Hamilton's equations (65) of Evans, §3.2.5(c), Example 6. For
`u_t + H(u_x) = 0` the characteristics are the straight lines `x = ξ + t H'(φ'(ξ))`, along which
`u_x = φ'(ξ)` is constant.

## Main results

* `IsFootpointAt`, `IsFootpointOn`, `IsFootpointNear`: the footpoint relation
  `x = ξ(t, x) + t H'(φ'(ξ(t, x)))` at a point, on a set, and eventually
  near a point.
* `characteristicSolution`: the candidate
  `u(t, x) = φ(ξ) + t (p H'(p) - H(p))` with `p = φ'(ξ)`, the initial value
  plus the Lagrangian accumulated along the characteristic.
* `characteristicSolution_partialDeriv_space`,
  `characteristicSolution_partialDeriv_time`,
  `characteristicSolution_residual`: where the footpoint Jacobian
  `1 + t H''(φ'(ξ)) φ''(ξ)` is nonzero, the candidate has the derivatives
  predicted by the characteristic construction and satisfies
  `u_t + H(u_x) = 0`.
* `firstCharacteristicDegeneracyTime`: the infimum, in `WithTop ℝ`, of the
  nonnegative times at which the Jacobian vanishes for some footpoint, or `⊤`
  if there are none; before it every Jacobian is nonzero
  (`characteristicJacobian_ne_zero_of_lt_firstDegeneracyTime`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.5(c), Example 6, equations (62)-(65); §3.3.1,
  Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (time_apply)

namespace HamiltonJacobi1D

noncomputable section

open PDE.Common

/-- The characteristic footpoint relation at one spacetime point. -/
def IsFootpointAt
    (H φ : ℝ → ℝ) (ξ : ℝ^2 → ℝ) (x : ℝ^2) : Prop :=
  x 1 = ξ x + x 0 * deriv H (deriv φ (ξ x))

/-- The characteristic footpoint relation on a spacetime set. -/
def IsFootpointOn
    (H φ : ℝ → ℝ) (ξ : ℝ^2 → ℝ) (s : Set ℝ^2) : Prop :=
  Set.EqOn
    (fun x : ℝ^2 ↦ x 1)
    (fun x : ℝ^2 ↦ ξ x + x 0 * deriv H (deriv φ (ξ x)))
    s

/-- The characteristic footpoint relation on a neighborhood of a point. -/
def IsFootpointNear
    (H φ : ℝ → ℝ) (ξ : ℝ^2 → ℝ) (x : ℝ^2) : Prop :=
  (fun y : ℝ^2 ↦ y 1) =ᶠ[nhds x]
    fun y : ℝ^2 ↦ ξ y + y 0 * deriv H (deriv φ (ξ y))

/-- A setwise footpoint relation specializes to every point of the set. -/
theorem IsFootpointOn.isFootpointAt {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ} {s : Set ℝ^2}
    (h : IsFootpointOn H φ ξ s) {x : ℝ^2} (hx : x ∈ s) :
    IsFootpointAt H φ ξ x :=
  h hx

/-- On an open set, a setwise footpoint relation holds near each point. -/
theorem IsFootpointOn.isFootpointNear {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ} {s : Set ℝ^2}
    (h : IsFootpointOn H φ ξ s) (hs : IsOpen s) {x : ℝ^2} (hx : x ∈ s) :
    IsFootpointNear H φ ξ x :=
  h.eventuallyEq_of_mem (hs.mem_nhds hx)

/-- The Jacobian of the characteristic map in the footpoint direction. -/
def footpointJacobian
    (H φ : ℝ → ℝ) (ξ : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  1 + x 0 * deriv (deriv H) (deriv φ (ξ x)) * deriv (deriv φ) (ξ x)

private theorem partialDeriv_footpoint_identity {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ}
    (hH' : Differentiable ℝ (deriv H)) (hφ' : Differentiable ℝ (deriv φ)) (i : Fin 2) (x : ℝ^2)
    (hξ : DifferentiableAt ℝ ξ x) (hrel : IsFootpointNear H φ ξ x) :
    (∂[i] (fun y : ℝ^2 ↦ y 1)) x = (∂[i] ξ) x + (∂[i] (fun y : ℝ^2 ↦ y 0)) x *
      deriv H (deriv φ (ξ x)) + x 0 * (∂[i] ξ) x * deriv (deriv φ) (ξ x) *
      deriv (deriv H) (deriv φ (ξ x)) := by
  have ht : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x := by cas
  have hp : DifferentiableAt ℝ (fun y : ℝ^2 ↦ deriv φ (ξ y)) x := hφ'.differentiableAt.comp x hξ
  have hv : DifferentiableAt ℝ (fun y : ℝ^2 ↦ deriv H (deriv φ (ξ y))) x :=
    hH'.differentiableAt.comp x hp
  rw [PDE.partialDeriv_congr_nhds i hrel, PDE.partialDeriv_add hξ (ht.fun_mul hv),
    PDE.partialDeriv_mul ht hv, PDE.partialDeriv_comp_real i hH'.differentiableAt hp,
    PDE.partialDeriv_comp_real i hφ'.differentiableAt hξ]
  ring

/-- Differentiability of a local footpoint forces its characteristic Jacobian to be nonzero. -/
theorem IsFootpointNear.jacobian_ne_zero {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ} {x : ℝ^2}
    (hrel : IsFootpointNear H φ ξ x) (hH' : Differentiable ℝ (deriv H))
    (hφ' : Differentiable ℝ (deriv φ)) (hξ : DifferentiableAt ℝ ξ x) :
    footpointJacobian H φ ξ x ≠ 0 := by
  have hidentity := partialDeriv_footpoint_identity hH' hφ' (1 : Fin 2) x hξ hrel
  refine right_ne_zero_of_mul_eq_one (a := (∂[(1 : Fin 2)] ξ) x) ?_
  simp only [Fin.isValue, PDE.partialDeriv_coord, ↓reduceIte, one_ne_zero, zero_mul, add_zero,
    footpointJacobian] at hidentity ⊢
  nlinarith

/-- Implicit differentiation of the footpoint relation in time. -/
theorem IsFootpointNear.partialDeriv_time {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ} {x : ℝ^2}
    (hrel : IsFootpointNear H φ ξ x) (hH' : Differentiable ℝ (deriv H))
    (hφ' : Differentiable ℝ (deriv φ)) (hξ : DifferentiableAt ℝ ξ x) :
    (∂[(0 : Fin 2)] ξ) x = -deriv H (deriv φ (ξ x)) / footpointJacobian H φ ξ x := by
  have hidentity := partialDeriv_footpoint_identity hH' hφ' (0 : Fin 2) x hξ hrel
  rw [eq_div_iff (hrel.jacobian_ne_zero hH' hφ' hξ)]
  simp only [Fin.isValue, PDE.partialDeriv_coord, zero_ne_one, ↓reduceIte, one_mul,
    footpointJacobian] at hidentity ⊢
  nlinarith

/-- Implicit differentiation of the footpoint relation in space. -/
theorem IsFootpointNear.partialDeriv_space {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ} {x : ℝ^2}
    (hrel : IsFootpointNear H φ ξ x) (hH' : Differentiable ℝ (deriv H))
    (hφ' : Differentiable ℝ (deriv φ)) (hξ : DifferentiableAt ℝ ξ x) :
    (∂[(1 : Fin 2)] ξ) x = 1 / footpointJacobian H φ ξ x := by
  have hidentity := partialDeriv_footpoint_identity hH' hφ' (1 : Fin 2) x hξ hrel
  rw [eq_div_iff (hrel.jacobian_ne_zero hH' hφ' hξ)]
  simp only [Fin.isValue, PDE.partialDeriv_coord, ↓reduceIte, one_ne_zero, zero_mul, add_zero,
    footpointJacobian] at hidentity ⊢
  nlinarith

/-- The value accumulated per unit time along a characteristic of momentum `p`. -/
def characteristicRate (H : ℝ → ℝ) (p : ℝ) : ℝ :=
  p * deriv H p - H p

private theorem differentiableAt_characteristicRate {H : ℝ → ℝ} {p : ℝ}
    (hH : DifferentiableAt ℝ H p) (hH' : DifferentiableAt ℝ (deriv H) p) :
    DifferentiableAt ℝ (characteristicRate H) p := by
  change DifferentiableAt ℝ (fun q ↦ q * deriv H q - H q) p
  exact (differentiableAt_id.mul hH').sub hH

private theorem deriv_characteristicRate {H : ℝ → ℝ} {p : ℝ} (hH : DifferentiableAt ℝ H p)
    (hH' : DifferentiableAt ℝ (deriv H) p) :
    deriv (characteristicRate H) p = p * deriv (deriv H) p := by
  have h : HasDerivAt (fun q ↦ q * deriv H q - H q)
      (1 * deriv H p + p * deriv (deriv H) p - deriv H p) p :=
    ((hasDerivAt_id' p).mul hH'.hasDerivAt).sub hH.hasDerivAt
  rw [show characteristicRate H = fun q ↦ q * deriv H q - H q from rfl, h.deriv]
  ring

/-- The characteristic candidate associated with a footpoint map. -/
def characteristicSolution
    (H φ : ℝ → ℝ) (ξ : ℝ^2 → ℝ) : ℝ^2 → ℝ :=
  fun x ↦ φ (ξ x) + x 0 * characteristicRate H (deriv φ (ξ x))

/-- Differentiability of the characteristic formula at a differentiable footpoint. -/
theorem differentiableAt_characteristicSolution {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ}
    (hH : Differentiable ℝ H) (hH' : Differentiable ℝ (deriv H)) (hφ : Differentiable ℝ φ)
    (hφ' : Differentiable ℝ (deriv φ)) {x : ℝ^2} (hξ : DifferentiableAt ℝ ξ x) :
    DifferentiableAt ℝ (characteristicSolution H φ ξ) x := by
  have ht : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x := by cas
  exact (hφ.differentiableAt.comp x hξ).add (ht.mul ((differentiableAt_characteristicRate
    hH.differentiableAt hH'.differentiableAt).comp x (hφ'.differentiableAt.comp x hξ)))

private theorem characteristicSolution_partialDeriv {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ}
    (hH : Differentiable ℝ H) (hH' : Differentiable ℝ (deriv H)) (hφ : Differentiable ℝ φ)
    (hφ' : Differentiable ℝ (deriv φ)) (i : Fin 2) (x : ℝ^2) (hξ : DifferentiableAt ℝ ξ x) :
    (∂[i] (characteristicSolution H φ ξ)) x =
      (∂[i] ξ) x * deriv φ (ξ x) +
        (∂[i] (fun y : ℝ^2 ↦ y 0)) x *
          characteristicRate H (deriv φ (ξ x)) +
        x 0 * (∂[i] ξ) x * deriv (deriv φ) (ξ x) *
          (deriv φ (ξ x) * deriv (deriv H) (deriv φ (ξ x))) := by
  have ht : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x := by cas
  have hp : DifferentiableAt ℝ (fun y : ℝ^2 ↦ deriv φ (ξ y)) x := hφ'.differentiableAt.comp x hξ
  have hrateAt : DifferentiableAt ℝ (characteristicRate H) (deriv φ (ξ x)) :=
    differentiableAt_characteristicRate hH.differentiableAt hH'.differentiableAt
  have hrate : DifferentiableAt ℝ (fun y : ℝ^2 ↦ characteristicRate H (deriv φ (ξ y))) x :=
    (hrateAt.comp x hp :)
  have hφξ : DifferentiableAt ℝ (fun y : ℝ^2 ↦ φ (ξ y)) x := hφ.differentiableAt.comp x hξ
  rw [show characteristicSolution H φ ξ =
      fun y ↦ φ (ξ y) + y 0 * characteristicRate H (deriv φ (ξ y)) from rfl,
    PDE.partialDeriv_add hφξ (ht.fun_mul hrate), PDE.partialDeriv_mul ht hrate,
    PDE.partialDeriv_comp_real i hφ.differentiableAt hξ, PDE.partialDeriv_comp_real i hrateAt hp,
    PDE.partialDeriv_comp_real i hφ'.differentiableAt hξ,
    deriv_characteristicRate hH.differentiableAt hH'.differentiableAt]
  ring

/-- The spatial derivative of the characteristic formula is the characteristic momentum. -/
theorem characteristicSolution_partialDeriv_space {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ}
    (hH : Differentiable ℝ H) (hH' : Differentiable ℝ (deriv H)) (hφ : Differentiable ℝ φ)
    (hφ' : Differentiable ℝ (deriv φ)) (x : ℝ^2) (hξ : DifferentiableAt ℝ ξ x)
    (hrel : IsFootpointNear H φ ξ x) :
    (∂[(1 : Fin 2)] (characteristicSolution H φ ξ)) x = deriv φ (ξ x) := by
  have hmul : (∂[(1 : Fin 2)] ξ) x * footpointJacobian H φ ξ x = 1 :=
    (eq_div_iff (hrel.jacobian_ne_zero hH' hφ' hξ)).1 (hrel.partialDeriv_space hH' hφ' hξ)
  rw [characteristicSolution_partialDeriv hH hH' hφ hφ' (1 : Fin 2) x hξ]
  simp only [footpointJacobian] at hmul
  simp only [PDE.partialDeriv_coord, one_ne_zero, ite_false, zero_mul, add_zero]
  linear_combination deriv φ (ξ x) * hmul

/-- The time derivative of the characteristic formula is minus the Hamiltonian. -/
theorem characteristicSolution_partialDeriv_time {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ}
    (hH : Differentiable ℝ H) (hH' : Differentiable ℝ (deriv H)) (hφ : Differentiable ℝ φ)
    (hφ' : Differentiable ℝ (deriv φ)) (x : ℝ^2) (hξ : DifferentiableAt ℝ ξ x)
    (hrel : IsFootpointNear H φ ξ x) :
    (∂[(0 : Fin 2)] (characteristicSolution H φ ξ)) x = -H (deriv φ (ξ x)) := by
  have hmul : (∂[(0 : Fin 2)] ξ) x * footpointJacobian H φ ξ x = -deriv H (deriv φ (ξ x)) :=
    (eq_div_iff (hrel.jacobian_ne_zero hH' hφ' hξ)).1 (hrel.partialDeriv_time hH' hφ' hξ)
  rw [characteristicSolution_partialDeriv hH hH' hφ hφ' (0 : Fin 2) x hξ]
  simp only [footpointJacobian] at hmul
  simp only [PDE.partialDeriv_coord, Fin.isValue, ite_eq_left, one_mul, characteristicRate]
  linear_combination deriv φ (ξ x) * hmul

/-- At initial time, the characteristic formula agrees with the initial profile. -/
theorem characteristicSolution_initial {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ} {x : ℝ^2}
    (hrel : IsFootpointAt H φ ξ x) (hx : x 0 = 0) :
    characteristicSolution H φ ξ x = φ (x 1) := by
  have hξeq : ξ x = x 1 := by
    have h := hrel
    simpa only [IsFootpointAt, hx, zero_mul, add_zero] using h.symm
  simp [characteristicSolution, hx, hξeq]

/-- The characteristic formula satisfies `u_t + H(u_x) = 0` at a regular footpoint. -/
theorem characteristicSolution_residual {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ} (hH : Differentiable ℝ H)
    (hH' : Differentiable ℝ (deriv H)) (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ))
    (x : ℝ^2) (hξ : DifferentiableAt ℝ ξ x) (hrel : IsFootpointNear H φ ξ x) :
    (∂[(0 : Fin 2)] (characteristicSolution H φ ξ)) x +
        H ((∂[(1 : Fin 2)] (characteristicSolution H φ ξ)) x) = 0 := by
  rw [characteristicSolution_partialDeriv_time hH hH' hφ hφ' x hξ hrel]
  rw [characteristicSolution_partialDeriv_space hH hH' hφ hφ' x hξ hrel]
  simp

/-- On an open set of regular footpoints, the characteristic formula satisfies the PDE. -/
theorem characteristicSolution_residual_on {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ} {U : Set ℝ^2}
    (hH : Differentiable ℝ H) (hH' : Differentiable ℝ (deriv H)) (hφ : Differentiable ℝ φ)
    (hφ' : Differentiable ℝ (deriv φ)) (hU : IsOpen U) (hξ : ∀ x ∈ U, DifferentiableAt ℝ ξ x)
    (hrel : IsFootpointOn H φ ξ U) :
    ∀ x ∈ U, (∂[(0 : Fin 2)] (characteristicSolution H φ ξ)) x +
      H ((∂[(1 : Fin 2)] (characteristicSolution H φ ξ)) x) = 0 :=
  fun x hx ↦ characteristicSolution_residual hH hH' hφ hφ' x (hξ x hx) (hrel.isFootpointNear hU hx)

/-- The characteristic formula has the prescribed trace on an initial subset. -/
theorem characteristicSolution_initial_on {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ} {s : Set ℝ^2}
    (hrel : IsFootpointOn H φ ξ s) :
    Set.EqOn (characteristicSolution H φ ξ) (fun x ↦ φ (x 1)) (s ∩ initialTimeSlice) := by
  intro x hx
  apply characteristicSolution_initial (hrel.isFootpointAt hx.1)
  simpa only [mem_initialTimeSlice, time_apply] using hx.2

/-!
## First characteristic degeneracy time

At fixed time `t`, the characteristic map is
`ξ ↦ ξ + t H'(φ'(ξ))`. Its derivative is
`1 + t H''(φ'(ξ)) φ''(ξ)`. We take the infimum of its nonnegative vanishing times,
with value `⊤` when there are none. On the unbounded footpoint line this infimum
need not be attained. We exclude Jacobian degeneracy strictly
before this threshold.
-/

/-- Nonnegative times at which the one-dimensional characteristic Jacobian vanishes. -/
def characteristicDegeneracyTimes (H φ : ℝ → ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ ∃ ξ : ℝ,
    1 + t * deriv (deriv H) (deriv φ ξ) * deriv (deriv φ) ξ = 0}

/-- Infimum of the nonnegative characteristic degeneracy times, or `⊤` if none occur.
This threshold need not itself be a degeneracy time. -/
noncomputable def firstCharacteristicDegeneracyTime (H φ : ℝ → ℝ) : WithTop ℝ := by
  classical
  exact
    if (characteristicDegeneracyTimes H φ).Nonempty then
      ↑(sInf (characteristicDegeneracyTimes H φ))
    else
      ⊤

/-- If the characteristic Jacobian never vanishes, the first degeneracy time is infinite. -/
theorem firstCharacteristicDegeneracyTime_eq_top
    (H φ : ℝ → ℝ) (h : characteristicDegeneracyTimes H φ = ∅) :
    firstCharacteristicDegeneracyTime H φ = ⊤ := by
  simp [firstCharacteristicDegeneracyTime, h]

private theorem characteristicDegeneracyTimes_bddBelow
    (H φ : ℝ → ℝ) : BddBelow (characteristicDegeneracyTimes H φ) :=
  ⟨0, fun _ ht ↦ ht.1⟩

/-- Before the first degeneracy time, every characteristic Jacobian is nonzero. -/
theorem characteristicJacobian_ne_zero_of_lt_firstDegeneracyTime (H φ : ℝ → ℝ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : (t : WithTop ℝ) < firstCharacteristicDegeneracyTime H φ) :
    ∀ ξ : ℝ, 1 + t * deriv (deriv H) (deriv φ ξ) * deriv (deriv φ) ξ ≠ 0 := by
  intro ξ hzero
  have ht_mem : t ∈ characteristicDegeneracyTimes H φ := ⟨ht0, ξ, hzero⟩
  have hnonempty : (characteristicDegeneracyTimes H φ).Nonempty := ⟨t, ht_mem⟩
  have hle : sInf (characteristicDegeneracyTimes H φ) ≤ t :=
    csInf_le (characteristicDegeneracyTimes_bddBelow H φ) ht_mem
  have hlt : t < sInf (characteristicDegeneracyTimes H φ) := by
    simpa [firstCharacteristicDegeneracyTime, hnonempty] using ht
  exact (not_lt_of_ge hle) hlt

end

end HamiltonJacobi1D
