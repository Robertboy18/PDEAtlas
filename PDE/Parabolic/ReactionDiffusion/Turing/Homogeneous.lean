/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.ReactionDiffusion.Turing.Coefficients
public import PDE.Analysis.Evolution.Time.ExponentialConvergence

/-!
# Decay of the homogeneous reaction ODE

Negative trace and positive determinant imply decay of every homogeneous linear reaction trajectory,
with a bound by a constant times the initial squared length (`homogeneous_uniform_bound`,
`homogeneous_tendsto_zero`, `homogeneous_asymptoticallyStable`). The two conditions are Evans's
stability conditions (27) in §4.1.2 for the linearized ODE (21).

## How it works

Evans reads off stability from the eigenvalues of `Df(0)`: (27) says that the roots of the
characteristic polynomial (26) have negative real parts. We prove decay analytically, without a
diagonalization or an exponential-decay estimate. Write `δ = det A`, `τ = tr A`. The quadratic
energy `E(X) = δ |X|² + |(A - τ I)X|²` (`Coefficients.reactionEnergy`) is positive definite, and
along `X' = AX` its derivative is `2δτ |X|²` (`hasDerivAt_reactionEnergy`). The bounds
`reactionEnergy_lower` and `reactionEnergy_upper` compare `E` with `|X|²`, and a Grönwall argument
gives decay.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.1.2 (Application: Turing instability), (21), p. 172, and
  (26)-(27), pp. 173-174.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace ReactionDiffusion.Turing

open Filter Set PDE.Analysis.Evolution
open scoped Topology

/-- A positive definite reaction energy when the determinant is positive. -/
def Coefficients.reactionEnergy (C : Coefficients) (x y : ℝ) : ℝ :=
  (C.a * C.d - C.b * C.c) * (x ^ 2 + y ^ 2) +
    (C.d * x - C.b * y) ^ 2 + (C.c * x - C.a * y) ^ 2

/-- A scalar upper bound for the reaction energy relative to squared Euclidean length. -/
def Coefficients.energyBound (C : Coefficients) : ℝ :=
  C.a * C.d - C.b * C.c + 2 * (C.a ^ 2 + C.b ^ 2 + C.c ^ 2 + C.d ^ 2)

/-- Stability and attraction of the homogeneous zero state, stated for
ODE trajectories. One coefficient-dependent constant bounds the squared length
at every future time by the initial squared length, and every trajectory decays. -/
def HomogeneousAsymptoticallyStable (C : Coefficients) : Prop :=
  ∃ bound : ℝ, 0 < bound ∧ ∀ u v : ℝ → ℝ,
    (∀ t ∈ Ici (0 : ℝ), HasDerivAt u (C.a * u t + C.b * v t) t) →
    (∀ t ∈ Ici (0 : ℝ), HasDerivAt v (C.c * u t + C.d * v t) t) →
    (∀ t ∈ Ici (0 : ℝ), u t ^ 2 + v t ^ 2 ≤ bound * (u 0 ^ 2 + v 0 ^ 2)) ∧
      Tendsto (fun t ↦ u t ^ 2 + v t ^ 2) atTop (𝓝 0)

/-- The determinant controls the state from below in the reaction energy. -/
theorem reactionEnergy_lower (C : Coefficients) (x y : ℝ) :
    (C.a * C.d - C.b * C.c) * (x ^ 2 + y ^ 2) ≤ C.reactionEnergy x y := by
  unfold Coefficients.reactionEnergy
  nlinarith [sq_nonneg (C.d * x - C.b * y), sq_nonneg (C.c * x - C.a * y)]

/-- The explicit coefficient bound controls the energy from above. -/
theorem reactionEnergy_upper (C : Coefficients) (x y : ℝ) :
    C.reactionEnergy x y ≤ C.energyBound * (x ^ 2 + y ^ 2) := by
  unfold Coefficients.reactionEnergy Coefficients.energyBound
  nlinarith [sq_nonneg (C.d * x + C.b * y), sq_nonneg (C.c * x + C.a * y),
    sq_nonneg (C.a * x), sq_nonneg (C.b * x), sq_nonneg (C.c * y), sq_nonneg (C.d * y)]

/-- The homogeneous reaction ODE has a strictly dissipative quadratic energy.
The derivative here is derived from the two scalar ODE derivatives. -/
theorem hasDerivAt_reactionEnergy (C : Coefficients) {u v : ℝ → ℝ} {t : ℝ}
    (hu : HasDerivAt u (C.a * u t + C.b * v t) t)
    (hv : HasDerivAt v (C.c * u t + C.d * v t) t) :
    HasDerivAt (fun s ↦ C.reactionEnergy (u s) (v s))
      (2 * (C.a * C.d - C.b * C.c) * (C.a + C.d) * (u t ^ 2 + v t ^ 2)) t := by
  have h := (((hu.pow 2).add (hv.pow 2)).const_mul (C.a * C.d - C.b * C.c)).add
    (((hu.const_mul C.d).sub (hv.const_mul C.b)).pow 2)
  have hfull := h.add (((hu.const_mul C.c).sub (hv.const_mul C.a)).pow 2)
  convert hfull using 1
  · rfl
  · dsimp
    ring

/-- Homogeneous trajectories satisfy a uniform bound proportional to their
initial squared length. Together with decay, this gives asymptotic stability,
including Lyapunov stability, rather than only pointwise attraction. -/
theorem homogeneous_uniform_bound (C : Coefficients)
    (htrace : C.a + C.d < 0) (hdet : 0 < C.a * C.d - C.b * C.c)
    {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Ici (0 : ℝ), HasDerivAt u (C.a * u t + C.b * v t) t)
    (hv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt v (C.c * u t + C.d * v t) t)
    {t : ℝ} (ht : 0 ≤ t) :
    u t ^ 2 + v t ^ 2 ≤
      C.energyBound / (C.a * C.d - C.b * C.c) * (u 0 ^ 2 + v 0 ^ 2) := by
  have henergy : C.reactionEnergy (u t) (v t) ≤ C.reactionEnergy (u 0) (v 0) := by
    have h := energy_le_exp_of_differential_inequality (a := 0) (b := t) (δ := 0)
      (fun s hs ↦ hasDerivAt_reactionEnergy C (hu s hs.1) (hv s hs.1))
      (fun s _ ↦ ?_) t ⟨ht, le_rfl⟩
    · simpa using h
    · simp only [mul_zero, neg_zero, zero_mul]
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) htrace.le) (by positivity)
  have hbound := (reactionEnergy_lower C (u t) (v t)).trans
    (henergy.trans (reactionEnergy_upper C (u 0) (v 0)))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hdet).2
  simpa only [mul_comm] using hbound

/-- Every forward homogeneous reaction trajectory decays to zero in squared
Euclidean length under the raw trace and determinant inequalities. -/
theorem homogeneous_tendsto_zero (C : Coefficients)
    (htrace : C.a + C.d < 0) (hdet : 0 < C.a * C.d - C.b * C.c)
    {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Ici (0 : ℝ), HasDerivAt u (C.a * u t + C.b * v t) t)
    (hv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt v (C.c * u t + C.d * v t) t) :
    Tendsto (fun t ↦ u t ^ 2 + v t ^ 2) atTop (𝓝 0) := by
  have hM : 0 < C.energyBound := by
    unfold Coefficients.energyBound
    nlinarith [sq_nonneg C.a, sq_nonneg C.b, sq_nonneg C.c, sq_nonneg C.d]
  let rate : ℝ := -((C.a * C.d - C.b * C.c) * (C.a + C.d)) / C.energyBound
  have hrate : 0 < rate := div_pos (neg_pos.mpr (mul_neg_of_pos_of_neg hdet htrace)) hM
  have hrateM : rate * C.energyBound =
      -((C.a * C.d - C.b * C.c) * (C.a + C.d)) := by
    dsimp [rate]
    exact div_mul_cancel₀ _ (ne_of_gt hM)
  have henergy : Tendsto (fun t ↦ C.reactionEnergy (u t) (v t)) atTop (𝓝 0) := by
    apply energy_tendsto_zero_of_differential_inequality (a := 0) hrate
    · intro t _
      exact (mul_nonneg hdet.le (by positivity)).trans (reactionEnergy_lower C _ _)
    · intro t ht
      exact hasDerivAt_reactionEnergy C (hu t ht) (hv t ht)
    · intro t _
      calc
        _ = -(2 * rate) * (C.energyBound * (u t ^ 2 + v t ^ 2)) := by
          nlinarith [congrArg (fun z ↦ 2 * z * (u t ^ 2 + v t ^ 2)) hrateM]
        _ ≤ -(2 * rate) * C.reactionEnergy (u t) (v t) :=
          mul_le_mul_of_nonpos_left (reactionEnergy_upper C _ _) (by linarith)
  have hquot : Tendsto
      (fun t ↦ C.reactionEnergy (u t) (v t) / (C.a * C.d - C.b * C.c))
      atTop (𝓝 0) := by
    simpa only [zero_div] using henergy.div_const (C.a * C.d - C.b * C.c)
  apply squeeze_zero (fun t ↦ by positivity) (fun t ↦ ?_) hquot
  apply (le_div_iff₀ hdet).2
  simpa only [mul_comm] using reactionEnergy_lower C (u t) (v t)

/-- The raw negative-trace and positive-determinant conditions imply homogeneous
asymptotic stability, without assuming an eigenbasis or an analytic decay bridge. -/
theorem homogeneous_asymptoticallyStable (C : Coefficients)
    (htrace : C.a + C.d < 0) (hdet : 0 < C.a * C.d - C.b * C.c) :
    HomogeneousAsymptoticallyStable C := by
  have hM : 0 < C.energyBound := by
    unfold Coefficients.energyBound
    nlinarith [sq_nonneg C.a, sq_nonneg C.b, sq_nonneg C.c, sq_nonneg C.d]
  refine ⟨C.energyBound / (C.a * C.d - C.b * C.c), div_pos hM hdet, ?_⟩
  intro u v hu hv
  exact ⟨fun _ ht ↦ homogeneous_uniform_bound C htrace hdet hu hv ht,
    homogeneous_tendsto_zero C htrace hdet hu hv⟩

end ReactionDiffusion.Turing
