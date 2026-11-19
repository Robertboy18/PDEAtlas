/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.PorousMedium.SelfSimilar
public import PDE.Parabolic.PorousMedium.TestIntegral
import CAS.ExactTactic

/-!
# The Barenblatt family solves the weak porous-medium equation

For `m > 1` and every real `C`, the Barenblatt density `u` solves `u_t = Δ(u^m)` weakly on
`(0, ∞) × ℝⁿ`, across its moving free boundary: for `0 < a ≤ b` and every `C¹` function `ψ` on
space-time,

`∫_a^b ∫ (u ψ_t - ∇(u^m) · ∇ψ) dx dt = ∫ (u ψ)(b, x) dx - ∫ (u ψ)(a, x) dx`

(`barenblatt_weak_pde`, `barenblatt_weak_pde_deriv_gradient`). For tests that vanish at `t = a` and
`t = b` the space-time residual is zero (`barenblatt_weak_pde_zero_endpoints`). The spatial and time
integrability of the integrand are proved, not assumed.

Evans's §4.2.2 derives the Barenblatt-Kompaneetz-Zeldovich solution (35)-(36) from the radial ansatz
and takes the positive part in (34) to make `w ≥ 0`; `barenblatt_weak_pde` shows that the resulting
function solves the equation weakly across the free boundary.

## How it works

The flux identity `∇(u^m)(x) = -(β/t) u(x) x` (`gradient_barenblatt_potential`) writes the integrand
as the density times the derivative of `ψ` along the dilation (`weakIntegrand_barenblatt_eq`). We
change variables `x = t^β y`, so that the pairing `∫ u(t, x) ψ(t, x) dx` becomes an integral over
the fixed support of the profile, whose `t`-derivative is the integral of the weak integrand
(`integral_weakIntegrand_barenblatt`, `hasDerivAt_barenblatt_pairing`). The fundamental theorem of
calculus on `[a, b]` then gives the identity. No classical derivative of `u` and no second
derivative of `u^m` at the interface is used.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.2.2, Example (A scaling invariant solution), (27)-(36),
  pp. 185-186.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PorousMedium

open MeasureTheory Set Filter
open scoped Gradient RealInnerProductSpace Topology

variable {n : ℕ}

/-- The divergence-form weak PDE integrand `u ψ_t - ∇(u^m) · ∇ψ`.
Directional spacetime Fréchet derivatives express both test derivatives. -/
def weakIntegrand (m : ℝ) (u : ℝ → ℝ^n → ℝ) (ψ : ℝ × ℝ^n → ℝ)
    (t : ℝ) (x : ℝ^n) : ℝ :=
  u t x * fderiv ℝ ψ (t, x) (1, 0) -
    fderiv ℝ ψ (t, x) (0, ∇ (fun z : ℝ^n ↦ u t z ^ m) x)

/-- The directional formulation agrees with scalar time derivatives and spatial gradients. -/
theorem weakIntegrand_eq_deriv_gradient (m : ℝ) (u : ℝ → ℝ^n → ℝ)
    {ψ : ℝ × ℝ^n → ℝ} (hψ : ContDiff ℝ 1 ψ) (t : ℝ) (x : ℝ^n) :
    weakIntegrand m u ψ t x =
      u t x * deriv (fun s ↦ ψ (s, x)) t -
        ⟪∇ (fun z : ℝ^n ↦ u t z ^ m) x, ∇ (fun z : ℝ^n ↦ ψ (t, z)) x⟫ := by
  have hd : HasDerivAt (fun s ↦ ψ (s, x)) (fderiv ℝ ψ (t, x) (1, 0)) t :=
    ((hψ.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hs := ((hψ.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  simp only [Function.comp_def, id_eq] at hs
  rw [weakIntegrand, hd.deriv, real_inner_comm, inner_gradient_left, hs.fderiv]
  rfl

private theorem apply_space_smul (L : ℝ × ℝ^n →L[ℝ] ℝ) (c : ℝ) (x : ℝ^n) :
    L (0, c • x) = c * L (0, x) := by
  simpa using L.map_smul c (0, x)

/-- The global flux identity rewrites the weak PDE integrand as dilation transport. -/
theorem weakIntegrand_barenblatt_eq {m t : ℝ} (hm : 1 < m) (ht : 0 < t)
    (C : ℝ) (ψ : ℝ × ℝ^n → ℝ) (x : ℝ^n) :
    weakIntegrand m (barenblatt n m C) ψ t x =
      barenblatt n m C t x *
        (fderiv ℝ ψ (t, x) (1, 0) +
          similarityBeta n m / t * fderiv ℝ ψ (t, x) (0, x)) := by
  rw [weakIntegrand, gradient_barenblatt_potential hm ht, apply_space_smul]
  cas

/-- The fixed-domain derivative has the same dilation transport form. -/
theorem profileTestDerivative_eq {m t : ℝ} (ht : 0 < t) (C : ℝ)
    (ψ : ℝ × ℝ^n → ℝ) (y : ℝ^n) :
    profileTestDerivative n m C ψ t y =
      profile n m C y *
        (fderiv ℝ ψ (t, t ^ similarityBeta n m • y) (1, 0) +
          similarityBeta n m / t *
            fderiv ℝ ψ (t, t ^ similarityBeta n m • y)
              (0, t ^ similarityBeta n m • y)) := by
  have hr : similarityBeta n m * t ^ (similarityBeta n m - 1) =
      similarityBeta n m / t * t ^ similarityBeta n m := by
    rw [Real.rpow_sub_one ht.ne']
    cas
  rw [profileTestDerivative, hr, mul_smul]
  have hp : ((1 : ℝ), (similarityBeta n m / t) • (t ^ similarityBeta n m • y)) =
      (1, (0 : ℝ^n)) + (similarityBeta n m / t) • (0, t ^ similarityBeta n m • y) := by
    simp
  rw [hp, map_add, map_smul]
  rfl

/-- The weak PDE integrand is continuous as a function of space at positive time. -/
theorem continuous_weakIntegrand_barenblatt {m t : ℝ} (hm : 1 < m) (ht : 0 < t)
    (C : ℝ) {ψ : ℝ × ℝ^n → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (weakIntegrand m (barenblatt n m C) ψ t) := by
  change Continuous (fun x ↦ weakIntegrand m (barenblatt n m C) ψ t x)
  simp_rw [weakIntegrand_barenblatt_eq hm ht]
  have hD : Continuous (fun x : ℝ^n ↦ fderiv ℝ ψ (t, x)) :=
    (hψ.continuous_fderiv (by norm_num)).comp
    (continuous_const.prodMk (continuous_id : Continuous (id : ℝ^n → ℝ^n)))
  exact (continuous_barenblatt hm C t).mul
    ((hD.clm_apply continuous_const).add
      (continuous_const.mul (hD.clm_apply (continuous_const.prodMk continuous_id))))

/-- The weak PDE integrand has compact support because its transport form contains the density. -/
theorem hasCompactSupport_weakIntegrand_barenblatt {m t : ℝ}
    (hm : 1 < m) (ht : 0 < t) (C : ℝ) (ψ : ℝ × ℝ^n → ℝ) :
    HasCompactSupport (weakIntegrand m (barenblatt n m C) ψ t) := by
  change HasCompactSupport (fun x ↦ weakIntegrand m (barenblatt n m C) ψ t x)
  simp_rw [weakIntegrand_barenblatt_eq hm ht]
  exact (hasCompactSupport_barenblatt hm C ht).mul_right

/-- The spatial integrand of the weak PDE identity is integrable at every positive time. -/
theorem integrable_weakIntegrand_barenblatt {m t : ℝ} (hm : 1 < m) (ht : 0 < t)
    (C : ℝ) {ψ : ℝ × ℝ^n → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    Integrable (weakIntegrand m (barenblatt n m C) ψ t) :=
  (continuous_weakIntegrand_barenblatt hm ht C hψ).integrable_of_hasCompactSupport
    (hasCompactSupport_weakIntegrand_barenblatt hm ht C ψ)

/-- The moving-domain weak PDE integral equals the derivative integral on the fixed profile
domain. -/
theorem integral_weakIntegrand_barenblatt {m t : ℝ} (hm : 1 < m) (ht : 0 < t)
    (C : ℝ) (ψ : ℝ × ℝ^n → ℝ) :
    (∫ x, weakIntegrand m (barenblatt n m C) ψ t x) =
      ∫ y, profileTestDerivative n m C ψ t y := by
  simp_rw [weakIntegrand_barenblatt_eq hm ht]
  rw [integral_barenblatt_mul m C ht]
  exact integral_congr_ae (Eventually.of_forall fun y ↦ (profileTestDerivative_eq ht C ψ y).symm)

/-- The endpoint density pairing is integrable for any continuous spacetime test. -/
theorem integrable_barenblatt_pairing {m t : ℝ} (hm : 1 < m) (ht : 0 < t)
    (C : ℝ) {ψ : ℝ × ℝ^n → ℝ} (hψ : Continuous ψ) :
    Integrable (fun x ↦ barenblatt n m C t x * ψ (t, x)) :=
  ((continuous_barenblatt hm C t).mul
    (hψ.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
      (hasCompactSupport_barenblatt hm C ht).mul_right

/-- The density pairing has the derivative prescribed by the weak porous-medium PDE. -/
theorem hasDerivAt_barenblatt_pairing {m C t : ℝ} (hm : 1 < m)
    (ht : 0 < t) {ψ : ℝ × ℝ^n → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    HasDerivAt (fun s ↦ ∫ x, barenblatt n m C s x * ψ (s, x))
      (∫ x, weakIntegrand m (barenblatt n m C) ψ t x) t := by
  rw [integral_weakIntegrand_barenblatt hm ht]
  apply (hasDerivAt_integral_profile_test hm hψ ht).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact integral_barenblatt_mul m C hs (fun x ↦ ψ (s, x))

/-- The spatial weak PDE integral is time integrable on every positive finite interval. -/
theorem intervalIntegrable_weakIntegrand_barenblatt {m C a b : ℝ}
    (hm : 1 < m) (ha : 0 < a) (hab : a ≤ b)
    {ψ : ℝ × ℝ^n → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    IntervalIntegrable
      (fun t ↦ ∫ x, weakIntegrand m (barenblatt n m C) ψ t x) volume a b := by
  have hpos : uIcc a b ⊆ Ioi (0 : ℝ) := by
    rw [uIcc_of_le hab]
    exact fun t ht ↦ lt_of_lt_of_le ha ht.1
  apply ContinuousOn.intervalIntegrable
  apply ((continuousOn_integral_profileTestDerivative (C := C) hm hψ).mono hpos).congr
  intro t ht
  exact integral_weakIntegrand_barenblatt hm (hpos ht) C ψ

/-- The Barenblatt family satisfies the weak porous-medium PDE across its moving boundary,
with its endpoint density pairings, for every positive finite interval and every `C¹` test. -/
theorem barenblatt_weak_pde {m C a b : ℝ}
    (hm : 1 < m) (ha : 0 < a) (hab : a ≤ b)
    {ψ : ℝ × ℝ^n → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    (∫ t in a..b, ∫ x, weakIntegrand m (barenblatt n m C) ψ t x) =
      (∫ x : ℝ^n, barenblatt n m C b x * ψ (b, x)) -
        ∫ x : ℝ^n, barenblatt n m C a x * ψ (a, x) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact hasDerivAt_barenblatt_pairing hm (lt_of_lt_of_le ha ht.1) hψ
  · exact intervalIntegrable_weakIntegrand_barenblatt hm ha hab hψ

/-- For tests vanishing at the temporal endpoints, the spacetime weak residual is zero. -/
theorem barenblatt_weak_pde_zero_endpoints {m C a b : ℝ}
    (hm : 1 < m) (ha : 0 < a) (hab : a ≤ b)
    {ψ : ℝ × ℝ^n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψa : ∀ x, ψ (a, x) = 0) (hψb : ∀ x, ψ (b, x) = 0) :
    (∫ t in a..b, ∫ x, weakIntegrand m (barenblatt n m C) ψ t x) = 0 := by
  rw [barenblatt_weak_pde hm ha hab hψ]
  simp [hψa, hψb]

/-- The weak PDE in the usual notation with time derivatives and spatial gradients. -/
theorem barenblatt_weak_pde_deriv_gradient {m C a b : ℝ}
    (hm : 1 < m) (ha : 0 < a) (hab : a ≤ b)
    {ψ : ℝ × ℝ^n → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    (∫ t in a..b, ∫ x : ℝ^n,
      barenblatt n m C t x * deriv (fun s ↦ ψ (s, x)) t -
        ⟪∇ (fun z : ℝ^n ↦ barenblatt n m C t z ^ m) x,
          ∇ (fun z : ℝ^n ↦ ψ (t, z)) x⟫) =
      (∫ x : ℝ^n, barenblatt n m C b x * ψ (b, x)) -
        ∫ x : ℝ^n, barenblatt n m C a x * ψ (a, x) := by
  simpa only [weakIntegrand_eq_deriv_gradient m _ hψ] using
    barenblatt_weak_pde hm ha hab hψ

end PorousMedium
