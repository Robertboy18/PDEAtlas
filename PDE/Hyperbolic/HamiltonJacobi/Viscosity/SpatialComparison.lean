/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.QuadraticBarrier

/-!
# Hamiltonian errors at spatially dependent doubled contacts

Assume a uniform Lipschitz bound in momentum and a spatial Lipschitz bound
growing at most linearly in momentum. Splitting the Hamiltonian difference
through the common separation momentum keeps the spatial error independent
of the localization gradients.

For a quadratic separation penalty, the resulting spatial term is
`Cx * (‖x-y‖ + ‖x-y‖²/ε)`. Bringing the points together is not enough:
the squared separation divided by `ε` must also tend to zero. The two-diagonal
comparison in `Metric.exists_penalty_lt_of_isMaxOn_sub` supplies that step.

These contact estimates are used in `FiniteHorizon.Spatial`.
They impose neither convexity of the Hamiltonian nor finite dimensionality.

The two bounds are condition (3) of Evans, §10.2, and the estimate is the passage from (14) to
(15) in his proof of Theorem 1. There `|x₀-y₀| = o(ε)` by (11) makes the term `|x₀-y₀|²/ε²`
small.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.2, condition (3), proof of Theorem 1, equations (11)
  and (14)-(15).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi

open Set

section NormedGroup

variable {E : Type*} [NormedAddCommGroup E]

/-- Evans's uniform momentum bound and spatial growth bound imply joint continuity. -/
theorem continuous_hamiltonian_of_lipschitz {H : E → E → ℝ} {Cp Cx : NNReal}
    (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖)) :
    Continuous (fun q : E × E ↦ H q.1 q.2) := by
  apply continuous_prod_of_continuous_lipschitzWith _ Cp ?_ hp
  intro p
  have hpx : LipschitzWith (Cx * (1 + ‖p‖₊)) (H p) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mul, NNReal.coe_add,
      NNReal.coe_one, coe_nnnorm, mul_assoc, mul_comm, mul_left_comm] using hx p x y
  exact hpx.continuous

/-- Separate the two localization errors from the spatial variation of the
Hamiltonian. The spatial bound is evaluated at the common momentum `p`, so it
does not acquire an extra product with either localization correction. -/
theorem hamiltonian_sub_le_of_lipschitz {H : E → E → ℝ} {Cp Cx : NNReal}
    (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖)) (p a b x y : E) :
    H (p - b) y - H (p + a) x ≤ Cp * (‖a‖ + ‖b‖) + Cx * ‖x - y‖ * (1 + ‖p‖) := by
  have hleft := (hp y).le_add_mul (p - b) p
  have hright := (hp x).le_add_mul p (p + a)
  have hb : dist (p - b) p = ‖b‖ := by
    rw [dist_eq_norm]
    have heq : p - b - p = -b := by abel
    rw [heq, norm_neg]
  have ha : dist p (p + a) = ‖a‖ := by
    rw [dist_eq_norm]
    have heq : p - (p + a) = -a := by abel
    rw [heq, norm_neg]
  rw [hb] at hleft
  rw [ha] at hright
  have hmiddle := (le_abs_self (H p y - H p x)).trans (hx p y x)
  rw [norm_sub_rev y x] at hmiddle
  calc
    H (p - b) y - H (p + a) x ≤
        Cp * ‖b‖ + Cx * ‖x - y‖ * (1 + ‖p‖) + Cp * ‖a‖ := by
      linarith only [hleft, hmiddle, hright]
    _ = Cp * (‖a‖ + ‖b‖) + Cx * ‖x - y‖ * (1 + ‖p‖) := by ring

end NormedGroup

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For quadratic doubling, Evans's spatial modulus produces precisely a
distance term and a squared-distance-over-scale term. The momentum Lipschitz
constant is uniform in position and the two constants may differ. -/
theorem hamiltonian_sub_le_quadratic {H : E → E → ℝ} {Cp Cx : NNReal}
    (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖)) {ε : ℝ} (hε : 0 < ε) (a b x y : E) :
    H (ε⁻¹ • (x - y) - b) y - H (ε⁻¹ • (x - y) + a) x ≤
      Cp * (‖a‖ + ‖b‖) + Cx * (‖x - y‖ + ‖x - y‖ ^ 2 / ε) := by
  have h := hamiltonian_sub_le_of_lipschitz hp hx (ε⁻¹ • (x - y)) a b x y
  have hnorm : ‖ε⁻¹ • (x - y)‖ = ‖x - y‖ / ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε, inv_mul_eq_div]
  rw [hnorm] at h
  convert h using 1
  ring

end NormedSpace

section HilbertSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- At a quadratic-barrier contact, the viscosity inequalities and Evans's
two Lipschitz bounds control the remaining time terms by localization and
separation errors. -/
theorem IsSpatialViscositySubsolution.doubling_barrier_le_of_lipschitz {H : E → E → ℝ}
    {U V : Set (E × ℝ)} {u v : E × ℝ → ℝ} {z w : E × ℝ} {ε α a T : ℝ} {Cp Cx : NNReal}
    (hu : IsSpatialViscositySubsolution H U u) (hv : IsSpatialViscositySupersolution H V v)
    (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖)) (hz : z ∈ U) (hw : w ∈ V)
    (hε : 0 < ε) (hzT : T - z.2 ≠ 0) (hwT : T - w.2 ≠ 0)
    (hmax : IsLocalMaxOn (fun q : (E × ℝ) × (E × ℝ) ↦ u q.1 - v q.2 -
      (quadraticSize (q.1 - q.2) / (2 * ε) + α * (quadraticSize q.1 + quadraticSize q.2) + a /
      (T - q.1.2) + a / (T - q.2.2))) (U ×ˢ V) (z, w)) :
    2 * α * (z.2 + w.2) + a / (T - z.2) ^ 2 + a / (T - w.2) ^ 2 ≤
      2 * Cp * |α| * (‖z.1‖ + ‖w.1‖) + Cx * (‖z.1 - w.1‖ + ‖z.1 - w.1‖ ^ 2 / ε) := by
  have hcontact := hu.doubling_barrier_inequality hv hz hw hε.ne' hzT hwT hmax
  have herror := hamiltonian_sub_le_quadratic hp hx hε ((2 * α) • z.1) ((2 * α) • w.1) z.1 w.1
  refine (hcontact.trans herror).trans_eq ?_
  simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (zero_lt_two : (0 : ℝ) < 2)]
  ring

end HilbertSpace

end HamiltonJacobi
