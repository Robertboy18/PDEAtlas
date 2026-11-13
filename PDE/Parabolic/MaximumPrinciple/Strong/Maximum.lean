/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.MaximumPrinciple.Strong.Propagation

/-!
# Parabolic strong maximum and minimum principles

These are the four cases of Evans's §7.1.4(c), Theorem 11 (Strong maximum principle) and Theorem 12
(Strong maximum principle for `c ≥ 0`), on an open preconnected set `U`, for continuous symmetric
uniformly elliptic coefficients. The operator is `matrixParabolicOperator`.

A maximum `M` reduces to the nonnegative supersolution `M - u` when `cM ≥ 0`; a minimum `m` reduces
to `u - m` when `cm ≤ 0`. Thus the zero-potential cases allow either sign of the extremum. For
nonnegative potential, the maximum must be nonnegative or the minimum nonpositive, including zero in
both cases.

The conclusion holds on the entire closed backward cylinder, by continuity. The proof uses
derivatives only at times strictly between `0` and `T`, so it covers a contact at `t₀ = T`.
Boundedness of `U` and positivity of the dimension are not used.

## Main results

* `matrix_eqOn_const_of_isMaxOn`, `matrix_eqOn_const_of_isMinOn`: the strong principles under the
  compatibility conditions `cM ≥ 0` and `cm ≤ 0`.
* `matrix_strong_maximum_zero_potential`, `matrix_strong_minimum_zero_potential`: Evans's
  Theorem 11(i) and (ii).
* `matrix_strong_maximum_nonnegative_potential`, `matrix_strong_minimum_nonnegative_potential`:
  Evans's Theorem 12(i) and (ii).

## How it works

Evans assumes `u` and the coefficients smooth, solves `vₜ + Lv = 0` in a subcylinder `W × (0, T]`
with `W` smooth and `v = u` on its parabolic boundary, and applies the Harnack inequality (91) to
`M - v ≥ 0`. We use neither this boundary value problem nor Harnack's inequality. The moving cubic
bump `ε exp(-δ(t - s)) (R² - ‖x - z - (t - s)v‖²)₊³` is a subsolution once `δ` exceeds an explicit
bound in the ellipticity constant, the radius, the velocity and upper bounds for the trace, drift
and potential (`matrixParabolicOperator_movingPolynomialBump_nonpos`). Weak comparison on a time
slab keeps a nonnegative supersolution above such a bump (`lower_bound_on_moving_halfBall`), so
positivity at one point moves along short straight paths (`positive_at_moving_center`), and a finite
chain of interior balls carries it to every point of `U` at every later time
(`positive_of_positive_before`). Hence a nonnegative supersolution that vanishes at `(x₀, t₀)`
vanishes on `closure U × [0, t₀]` (`eqOn_zero_before_of_nonneg_of_eq_zero`), applied to `M - u` or
`u - m`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.4(c), Theorem 11 (Strong maximum principle) and its
  proof, (90)-(91), pp. 396-397, and Theorem 12 (Strong maximum principle for `c ≥ 0`), pp. 397-398.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace ParabolicMaximum

open PDE.Analysis Set
open scoped RealInnerProductSpace

variable {n : ℕ} {U : Set (ℝ^n)} (hU : IsOpen U) (hconn : IsPreconnected U)
  {T θ : ℝ} (hθ : 0 < θ)
  (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
  (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
  (ha : ContinuousOn (fun p : ℝ^n × ℝ ↦ a p.1 p.2) (U ×ˢ Ioc 0 T))
  (hb : ContinuousOn (fun p : ℝ^n × ℝ ↦ b p.1 p.2) (U ×ˢ Ioc 0 T))
  (hccont : ContinuousOn (fun p : ℝ^n × ℝ ↦ c p.1 p.2) (U ×ˢ Ioc 0 T))
  (hsymm : ∀ x ∈ U, ∀ t ∈ Ioc 0 T, (a x t).IsSymm)
  (hell : ∀ x ∈ U, ∀ t ∈ Ioc 0 T, ∀ d : ℝ^n,
    θ * ‖d‖ ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, a x t i j * d i * d j)
  {u : ℝ^n → ℝ → ℝ}
  (hucont : ContinuousOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder U T))
  (huspace : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u y t) x)
  (hutime : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (u x) t)
  {x₀ : ℝ^n} (hx₀ : x₀ ∈ U) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioc 0 T)

include hU hconn hθ ha hb hccont hsymm hell hucont huspace hutime hx₀ ht₀

/-- The strong maximum principle with the exact potential compatibility
`c M ≥ 0`. No sign assumption on the solution itself is imposed. -/
theorem matrix_eqOn_const_of_isMaxOn
    (hc : ∀ x ∈ U, ∀ t ∈ Ioc 0 T, 0 ≤ c x t)
    (hsub : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, matrixParabolicOperator a b c u x t ≤ 0)
    (hmax : IsMaxOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder U T) (x₀, t₀))
    (hcM : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, 0 ≤ c x t * u x₀ t₀) :
    EqOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (fun _ ↦ u x₀ t₀) (closedCylinder U t₀) := by
  have hell' (x : ℝ^n) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Ioc 0 T) (d : ℝ^n) :
      θ * ‖d‖ ^ 2 ≤ ⟪d, (a x t).toEuclideanLin d⟫ := by
    rw [inner_toEuclideanLin_self]
    exact hell x hx t ht d
  have hPSD (x : ℝ^n) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Ioo 0 T) :
      (a x t).PosSemidef :=
    posSemidef_of_elliptic (hsymm x hx t ⟨ht.1, ht.2.le⟩) hθ.le
      (hell' x hx t ⟨ht.1, ht.2.le⟩)
  have hzero := eqOn_zero_before_of_nonneg_of_eq_zero hU hconn hθ a b c
    (continuous_id.matrix_trace.comp_continuousOn ha) hb hccont hPSD
    (fun x hx t ht ↦ hell' x hx t ⟨ht.1, ht.2.le⟩)
    (fun x hx t ht ↦ hc x hx t ⟨ht.1, ht.2.le⟩)
    (fun x t ↦ u x₀ t₀ - u x t) (continuousOn_const.sub hucont)
    (fun x hx t ht ↦ contDiffAt_const.sub (huspace x hx t ht))
    (fun x hx t ht ↦ (differentiableAt_const _).sub (hutime x hx t ht))
    (fun x hx t ht ↦ by
      rw [matrixParabolicOperator_sub a b c contDiffAt_const (huspace x hx t ht)
        (differentiableAt_const _) (hutime x hx t ht), matrixParabolicOperator_const]
      exact sub_nonneg.mpr ((hsub x hx t ht).trans (hcM x hx t ht)))
    (fun x hx t ht ↦ sub_nonneg.mpr
      (hmax (show (x, t) ∈ closedCylinder U T from
        ⟨subset_closure hx, ht.1.le, ht.2⟩))) hx₀ ht₀ (sub_self _)
  exact fun p hp ↦ (sub_eq_zero.mp (hzero hp)).symm

/-- The dual strong minimum principle with the compatibility `c m ≤ 0`. -/
theorem matrix_eqOn_const_of_isMinOn
    (hc : ∀ x ∈ U, ∀ t ∈ Ioc 0 T, 0 ≤ c x t)
    (hsuper : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, 0 ≤ matrixParabolicOperator a b c u x t)
    (hmin : IsMinOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder U T) (x₀, t₀))
    (hcm : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, c x t * u x₀ t₀ ≤ 0) :
    EqOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (fun _ ↦ u x₀ t₀) (closedCylinder U t₀) := by
  have hell' (x : ℝ^n) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Ioc 0 T) (d : ℝ^n) :
      θ * ‖d‖ ^ 2 ≤ ⟪d, (a x t).toEuclideanLin d⟫ := by
    rw [inner_toEuclideanLin_self]
    exact hell x hx t ht d
  have hPSD (x : ℝ^n) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Ioo 0 T) :
      (a x t).PosSemidef :=
    posSemidef_of_elliptic (hsymm x hx t ⟨ht.1, ht.2.le⟩) hθ.le
      (hell' x hx t ⟨ht.1, ht.2.le⟩)
  have hzero := eqOn_zero_before_of_nonneg_of_eq_zero hU hconn hθ a b c
    (continuous_id.matrix_trace.comp_continuousOn ha) hb hccont hPSD
    (fun x hx t ht ↦ hell' x hx t ⟨ht.1, ht.2.le⟩)
    (fun x hx t ht ↦ hc x hx t ⟨ht.1, ht.2.le⟩)
    (fun x t ↦ u x t - u x₀ t₀) (hucont.sub continuousOn_const)
    (fun x hx t ht ↦ (huspace x hx t ht).sub contDiffAt_const)
    (fun x hx t ht ↦ (hutime x hx t ht).sub (differentiableAt_const _))
    (fun x hx t ht ↦ by
      rw [matrixParabolicOperator_sub a b c (huspace x hx t ht) contDiffAt_const
        (hutime x hx t ht) (differentiableAt_const _), matrixParabolicOperator_const]
      exact sub_nonneg.mpr ((hcm x hx t ht).trans (hsuper x hx t ht)))
    (fun x hx t ht ↦ sub_nonneg.mpr
      (hmin (show (x, t) ∈ closedCylinder U T from
        ⟨subset_closure hx, ht.1.le, ht.2⟩))) hx₀ ht₀ (sub_self _)
  exact fun p hp ↦ sub_eq_zero.mp (hzero hp)

/-- Evans's §7.1.4(c), Theorem 11(i): with zero potential, a maximum of either
sign attained at an interior point at positive time forces backward constancy. -/
theorem matrix_strong_maximum_zero_potential
    (hc : ∀ x ∈ U, ∀ t ∈ Ioc 0 T, c x t = 0)
    (hsub : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, matrixParabolicOperator a b c u x t ≤ 0)
    (hmax : IsMaxOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder U T) (x₀, t₀)) :
    EqOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (fun _ ↦ u x₀ t₀) (closedCylinder U t₀) :=
  matrix_eqOn_const_of_isMaxOn hU hconn hθ a b c ha hb hccont hsymm hell
    hucont huspace hutime hx₀ ht₀ (fun x hx t ht ↦ (hc x hx t ht).ge) hsub hmax
    (fun x hx t ht ↦ by rw [hc x hx t ⟨ht.1, ht.2.le⟩, zero_mul])

/-- Evans's §7.1.4(c), Theorem 11(ii): with zero potential, an interior
positive-time minimum of either sign forces backward constancy. -/
theorem matrix_strong_minimum_zero_potential
    (hc : ∀ x ∈ U, ∀ t ∈ Ioc 0 T, c x t = 0)
    (hsuper : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, 0 ≤ matrixParabolicOperator a b c u x t)
    (hmin : IsMinOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder U T) (x₀, t₀)) :
    EqOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (fun _ ↦ u x₀ t₀) (closedCylinder U t₀) :=
  matrix_eqOn_const_of_isMinOn hU hconn hθ a b c ha hb hccont hsymm hell
    hucont huspace hutime hx₀ ht₀ (fun x hx t ht ↦ (hc x hx t ht).ge) hsuper hmin
    (fun x hx t ht ↦ by rw [hc x hx t ⟨ht.1, ht.2.le⟩, zero_mul])

/-- Evans's §7.1.4(c), Theorem 12(i): for nonnegative potential, an attained
nonnegative maximum forces backward constancy. A zero maximum is included. -/
theorem matrix_strong_maximum_nonnegative_potential
    (hc : ∀ x ∈ U, ∀ t ∈ Ioc 0 T, 0 ≤ c x t)
    (hsub : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, matrixParabolicOperator a b c u x t ≤ 0)
    (hmax : IsMaxOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder U T) (x₀, t₀))
    (hvalue : 0 ≤ u x₀ t₀) :
    EqOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (fun _ ↦ u x₀ t₀) (closedCylinder U t₀) :=
  matrix_eqOn_const_of_isMaxOn hU hconn hθ a b c ha hb hccont hsymm hell
    hucont huspace hutime hx₀ ht₀ hc hsub hmax
    (fun x hx t ht ↦ mul_nonneg (hc x hx t ⟨ht.1, ht.2.le⟩) hvalue)

/-- Evans's §7.1.4(c), Theorem 12(ii): for nonnegative potential, an attained
nonpositive minimum forces backward constancy. A zero minimum is included. -/
theorem matrix_strong_minimum_nonnegative_potential
    (hc : ∀ x ∈ U, ∀ t ∈ Ioc 0 T, 0 ≤ c x t)
    (hsuper : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, 0 ≤ matrixParabolicOperator a b c u x t)
    (hmin : IsMinOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder U T) (x₀, t₀))
    (hvalue : u x₀ t₀ ≤ 0) :
    EqOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (fun _ ↦ u x₀ t₀) (closedCylinder U t₀) :=
  matrix_eqOn_const_of_isMinOn hU hconn hθ a b c ha hb hccont hsymm hell
    hucont huspace hutime hx₀ ht₀ hc hsuper hmin
    (fun x hx t ht ↦ mul_nonpos_of_nonneg_of_nonpos (hc x hx t ⟨ht.1, ht.2.le⟩) hvalue)

end ParabolicMaximum
