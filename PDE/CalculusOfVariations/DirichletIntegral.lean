/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.DirectMethod
public import PDE.CalculusOfVariations.IntegralEnergy
public import PDE.CalculusOfVariations.SobolevIntegral
public import PDE.Spaces.Sobolev.Inequalities.Poincare.BoundedDomain
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.Continuous
import PDE.Analysis.MeasureTheory.Lp.Superposition
import PDE.CalculusOfVariations.FiniteExponent

/-!
# Convex gradient integrals with quadratic growth on `H¹₀`

Consider `J(u) = ∫_Ω F(x, Du(x)) dx` on `H¹₀(Ω)`, with `F` measurable in
`(x, z)` and convex in `z` for almost every `x`. Since the gradient variable
ranges over all of finite-dimensional `ℝⁿ`, convexity also gives continuity.
The bounds

`c |z|² - b(x) ≤ F(x, z) ≤ a(x) + C |z|²`,

where `a, b` are integrable, `c > 0`, and `C ≥ 0`, imply that every energy is
finite and that `J` is weakly lower semicontinuous. On a bounded domain of
positive dimension, Poincaré gives coercivity in the full Sobolev norm.

The gradient is the continuous linear map `gradientCLM` into `L²(Ω; ℝⁿ)`.
Its norm identity connects the pointwise quadratic lower bound to the
Sobolev norm. Integrability is proved before any comparison of Bochner
integrals, so no estimate relies on the totalized value at a nonintegrable
density.

Here `H¹₀(Ω)` is defined by closure of test functions. On bounded open sets
this is the usual homogeneous Dirichlet problem; the proofs only require
boundedness, with no boundary regularity. The density depends on
position and gradient, not on the value of `u`.

Existence of minimizers, with zero or prescribed Sobolev boundary values, is the
case `p = 2` of `exists_minimizer_wkpGradientIntegral` and
`exists_minimizer_wkpGradientIntegral_prescribed_boundary`. This is the
quadratic-growth case of the direct method for convex integral functionals in
Evans, §8.2.2, Theorems 1 and 2 (weak lower semicontinuity and existence).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, Theorems 1 and 2.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace PDE.CalculusOfVariations

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "μ" => domainMeasure n Ω

/-- The homogeneous Dirichlet energy `∫_Ω F(x, Du(x)) dx`, evaluated on the
vector-valued weak gradient. The growth theorems below prove integrability
of the density before using this real-valued Bochner integral. -/
def dirichletGradientIntegralEnergy (F : ℝ^n → ℝ^n → ℝ) (u : H¹₀(Ω)) : ℝ :=
  ∫ x, F x (∇ (u : H¹(Ω)) x) ∂μ

variable {F : ℝ^n → ℝ^n → ℝ} {a b : ℝ^n → ℝ} {c C : ℝ}

private theorem abs_density_le_of_quadratic_bounds
    (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ 2 - b x ≤ F x z)
    (hupper : ∀ᵐ x ∂μ, ∀ z, F x z ≤ a x + C * ‖z‖ ^ 2) :
    ∀ᵐ x ∂μ, ∀ z, |F x z| ≤ (|a x| + |b x|) + C * ‖z‖ ^ 2 := by
  simpa only [NNReal.coe_ofNat, Real.rpow_two] using
    abs_density_le_of_rpow_bounds (p := 2) hc hC
      (by simpa only [NNReal.coe_ofNat, Real.rpow_two] using hlower)
      (by simpa only [NNReal.coe_ofNat, Real.rpow_two] using hupper)

/-- Two-sided quadratic growth with integrable offsets makes the gradient
density integrable for every `H¹₀` function. Neither continuity nor convexity
of the density, nor boundedness of the domain, is needed for this step.
The offsets may have either sign. -/
theorem integrable_dirichletGradientIntegralEnergy_density
    (hF : Measurable (Function.uncurry F)) (ha : Integrable a μ) (hb : Integrable b μ)
    (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ 2 - b x ≤ F x z)
    (hupper : ∀ᵐ x ∂μ, ∀ z, F x z ≤ a x + C * ‖z‖ ^ 2)
    (u : H¹₀(Ω)) :
    Integrable (fun x ↦ F x (∇ (u : H¹(Ω)) x)) μ := by
  apply (Lp.memLp (∇ (u : H¹(Ω)))).integrable_comp_of_norm_rpow_le
    (by norm_num) (by norm_num) hF (ha.abs.add hb.abs)
  simpa only [Pi.add_apply, ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs] using
    abs_density_le_of_quadratic_bounds hc hC hlower hupper

/-- A measurable, almost-everywhere convex density with two-sided
quadratic growth defines a weakly lower-semicontinuous energy on `H¹₀`.
Continuity in the gradient follows from finite-dimensional convexity;
the lower bound `-b` and integrability follow from the growth hypotheses.
This conclusion does not require a bounded domain or a positive lower
quadratic coefficient. -/
theorem lowerSemicontinuous_weakSpace_dirichletGradientIntegralEnergy
    (hF : Measurable (Function.uncurry F))
    (hconvex : ∀ᵐ x ∂μ, ConvexOn ℝ univ (F x))
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ 2 - b x ≤ F x z)
    (hupper : ∀ᵐ x ∂μ, ∀ z, F x z ≤ a x + C * ‖z‖ ^ 2) :
    LowerSemicontinuous
      (fun w : WeakSpace ℝ H¹₀(Ω) ↦
        dirichletGradientIntegralEnergy F ((toWeakSpace ℝ H¹₀(Ω)).symm w)) := by
  have hcont : ∀ᵐ x ∂μ, Continuous (F x) :=
    hconvex.mono fun x hx ↦ continuousOn_univ.mp (hx.continuousOn isOpen_univ)
  unfold dirichletGradientIntegralEnergy
  refine @lowerSemicontinuous_weakSpace_integral_Lp_comp_of_growth
    (ℝ^n) (ℝ^n) inferInstance μ inferInstance inferInstance
    2 H¹₀(Ω) inferInstance inferInstance inferInstance inferInstance inferInstance
    (gradientCLM (n := n) (Ω := Ω)) (by norm_num) F _ _ C
    hF hcont hconvex (ha.abs.add hb.abs) hb.neg
    ?_ ?_
  · filter_upwards [hlower] with x hx
    intro z
    change -b x ≤ F x z
    linarith [hx z, mul_nonneg hc (sq_nonneg ‖z‖)]
  · simpa only [Pi.add_apply, ENNReal.toReal_ofNat, Real.rpow_two] using
      abs_density_le_of_quadratic_bounds hc hC hlower hupper

/-- Integrating the quadratic lower bound gives
`c ‖Du‖²₂ - ∫_Ω b ≤ J(u)`. Only the lower bound and integrability of this
density are needed; no convexity or domain assumption enters the estimate. -/
theorem dirichletGradientIntegralEnergy_lower_bound
    (hb : Integrable b μ) (u : H¹₀(Ω))
    (hFint : Integrable (fun x ↦ F x (∇ (u : H¹(Ω)) x)) μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ 2 - b x ≤ F x z) :
    c * ‖∇ (u : H¹(Ω))‖ ^ 2 - (∫ x, b x ∂μ) ≤
      dirichletGradientIntegralEnergy F u := by
  have hint :
      Integrable (fun x ↦ ‖∇ (u : H¹(Ω)) x‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using
      (L2.integrable_inner (𝕜 := ℝ)
        (∇ (u : H¹(Ω))) (∇ (u : H¹(Ω))))
  have hnorm :
      (∫ x, ‖∇ (u : H¹(Ω)) x‖ ^ 2 ∂μ) =
        ‖∇ (u : H¹(Ω))‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using
      (L2.inner_def (𝕜 := ℝ)
        (∇ (u : H¹(Ω))) (∇ (u : H¹(Ω)))).symm
  calc
    c * ‖∇ (u : H¹(Ω))‖ ^ 2 - (∫ x, b x ∂μ) =
        ∫ x, c * ‖∇ (u : H¹(Ω)) x‖ ^ 2 - b x ∂μ := by
      rw [integral_sub (hint.const_mul c) hb, integral_const_mul, hnorm]
    _ ≤ dirichletGradientIntegralEnergy F u :=
      integral_mono_ae ((hint.const_mul c).sub hb) hFint
        (hlower.mono fun x hx ↦ hx (∇ (u : H¹(Ω)) x))

private theorem norm_sq_le_poincare_mul_gradient_sq
    (P : ℝ≥0)
    (hP : ∀ u : H¹₀(Ω), ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ≤
      (P : ℝ) * ∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖)
    (u : H¹₀(Ω)) :
    ‖u‖ ^ 2 ≤ ((P : ℝ) ^ 2 * (n : ℝ) + 1) *
      ‖∇ (u : H¹(Ω))‖ ^ 2 := by
  have hsum :
      (∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖) ^ 2 ≤
        (n : ℝ) * ∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
        (f := fun i ↦ ‖derivCoordCLM (n := n) (Ω := Ω) i u‖) (α := ℝ))
  have hbase :
      ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2 ≤
        (P : ℝ) ^ 2 *
          (∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖) ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg P.coe_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg _))).2
          (hP u)
  have hbase' := hbase.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg (P : ℝ)))
  calc
    ‖u‖ ^ 2 = ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2 +
        ∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ ^ 2 :=
      norm_sq_eq_base_sq_add_sum_deriv_sq u
    _ ≤ ((P : ℝ) ^ 2 * (n : ℝ) + 1) *
        ∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ ^ 2 := by
      nlinarith [hbase']
    _ = ((P : ℝ) ^ 2 * (n : ℝ) + 1) *
        ‖∇ (u : H¹(Ω))‖ ^ 2 := by
      exact congrArg (((P : ℝ) ^ 2 * (n : ℝ) + 1) * ·)
        (norm_gradientCLM_sq_eq_sum_deriv_sq u).symm

/-- On a bounded domain of positive dimension, a positive quadratic lower
bound for the density yields a positive quadratic lower bound in the full
`H¹₀` norm. If `P` is the constant in the scalar-coordinate Poincaré
inequality, the proof takes `k = c / (P² n + 1)`. -/
theorem exists_pos_quadratic_lower_bound_dirichletGradientIntegralEnergy
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (hc : 0 < c) (hb : Integrable b μ)
    (hFint : ∀ u : H¹₀(Ω),
      Integrable (fun x ↦ F x (∇ (u : H¹(Ω)) x)) μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ 2 - b x ≤ F x z) :
    ∃ k : ℝ, 0 < k ∧ ∀ u : H¹₀(Ω),
      k * ‖u‖ ^ 2 - (∫ x, b x ∂μ) ≤ dirichletGradientIntegralEnergy F u := by
  obtain ⟨P, hP⟩ := exists_poincare_H10 hn hΩbounded
  have hP' : ∀ u : H¹₀(Ω), ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ≤
      (P : ℝ) * ∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ := by
    intro u
    simpa only [baseCoordCLM_apply, derivCoordCLM_apply] using hP u
  let K : ℝ := (P : ℝ) ^ 2 * (n : ℝ) + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hk : 0 < c / K := div_pos hc hK
  refine ⟨c / K, hk, fun u ↦ ?_⟩
  have hnorm := norm_sq_le_poincare_mul_gradient_sq P hP' u
  have hgradient :
      (c / K) * ‖u‖ ^ 2 ≤ c * ‖∇ (u : H¹(Ω))‖ ^ 2 := by
    calc
      (c / K) * ‖u‖ ^ 2 ≤
          (c / K) * (K * ‖∇ (u : H¹(Ω))‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hnorm hk.le
      _ = c * ‖∇ (u : H¹(Ω))‖ ^ 2 := by
        rw [← mul_assoc, div_mul_cancel₀ _ hK.ne']
  exact (sub_le_sub_right hgradient _).trans
    (dirichletGradientIntegralEnergy_lower_bound hb u (hFint u) hlower)

/-- Positive quadratic growth from below makes the gradient energy coercive
on `H¹₀` of a bounded domain of positive dimension. Integrability of the
densities is explicit here and follows from the two-sided growth theorem
when applying the minimizer result. -/
theorem tendsto_dirichletGradientIntegralEnergy_atTop
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (hc : 0 < c) (hb : Integrable b μ)
    (hFint : ∀ u : H¹₀(Ω),
      Integrable (fun x ↦ F x (∇ (u : H¹(Ω)) x)) μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ 2 - b x ≤ F x z) :
    Tendsto (dirichletGradientIntegralEnergy (Ω := Ω) F)
      (Bornology.cobounded H¹₀(Ω)) atTop := by
  obtain ⟨k, hk, hbound⟩ :=
    exists_pos_quadratic_lower_bound_dirichletGradientIntegralEnergy
      hn hΩbounded hc hb hFint hlower
  refine tendsto_atTop.2 fun R ↦ ?_
  filter_upwards [eventually_cobounded_le_norm
    (max 1 ((R + ∫ x, b x ∂μ) / k))] with u hu
  have hu1 : 1 ≤ ‖u‖ := (le_max_left _ _).trans hu
  have huR : (R + ∫ x, b x ∂μ) / k ≤ ‖u‖ := (le_max_right _ _).trans hu
  have hR := (div_le_iff₀ hk).mp huR
  have hsquare : ‖u‖ ≤ ‖u‖ ^ 2 := by
    nlinarith [mul_nonneg (norm_nonneg u) (sub_nonneg.mpr hu1)]
  have hquadratic := mul_le_mul_of_nonneg_left hsquare hk.le
  linarith [hbound u]

end PDE.CalculusOfVariations
