/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.GaussianGrowth.Comparison
import PDE.FDeriv.Calculus

/-!
# The whole-space heat maximum principle and uniqueness under Gaussian growth

These are Evans's §2.3.3(a), Theorem 6 (Maximum principle for the Cauchy problem) and Theorem 7
(Uniqueness for Cauchy problem). The maximum principle requires only a one-sided Gaussian growth
bound; uniqueness uses two-sided bounds for the two solutions. The time horizon is arbitrary.

Evans assumes `u ∈ C²₁(ℝⁿ × (0, T])`, the growth bound for `0 ≤ t ≤ T` and, for uniqueness, a
continuous forcing. We need the equation, the derivatives and the growth bounds only for
`0 < t < T`; the derivatives need not be jointly continuous, and the forcing is arbitrary.
Continuity on the closed slab supplies both time faces; no backward-time regularity is assumed.

The suprema take values in `EReal`, so unbounded initial data are included. We prove both the
closed-slab statement and its positive-time version. Equality of solutions is pointwise on the
entire closed slab, including the terminal time.

## Main results

* `iSup_eq_initial_of_gaussian_growth`: Evans's Theorem 6, with suprema over the closed slab.
* `iSup_Ioc_eq_initial_of_gaussian_growth`: the same with the supremum over positive times.
* `eq_of_gaussian_growth`: Evans's Theorem 7.

## How it works

Evans first assumes `4aT < 1` and applies the maximum principle on bounded cylinders to
`u - μ(T + ε - t)^(-n/2) exp(|x - y|² / (4(T + ε - t)))`, which solves the heat equation, on balls
centred at the evaluation point `y`, (25)-(29); in general he repeats the argument on intervals of
length `1/(8a)`. We subtract instead a small multiple of `growingGaussian (a + 1) c` with
`c = (4 + 2n)(a + 1)`, a supersolution centred at the origin that grows like `exp((a + 1)‖x‖²)`, so
that every positive multiple of it exceeds `A exp(a‖x‖²)` on large spheres. The weak maximum
principle `heat_subsolution_le_of_boundary_le` on a large ball, followed by letting the multiple
tend to zero, gives `heat_subsolution_le_of_gaussian_growth_short` when `cT < 1`, and
`heat_subsolution_le_of_gaussian_growth` applies it on successive intervals of length `1/(2c)`.
Uniqueness applies the maximum principle to `±(u - v)`, as in Evans's proof of Theorem 7.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.3(a), Theorem 6 (Maximum principle for the Cauchy
  problem) and its proof, (23)-(29), pp. 57-58, and Theorem 7 (Uniqueness for Cauchy problem),
  (30)-(31), p. 59.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open Set

/-- The positive-time heat supremum equals the initial supremum under one-sided
Gaussian growth. Continuity recovers the initial values even though time zero is
excluded from the first supremum. -/
theorem iSup_Ioc_eq_initial_of_gaussian_growth {n : ℕ} {A a T : ℝ}
    (ha : 0 ≤ a) (hT : 0 < T) (u : ℝ^n → ℝ → ℝ)
    (hucont : ContinuousOn (fun p ↦ u p.1 p.2) (univ ×ˢ Icc 0 T))
    (huspace : ∀ x, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (u x) t)
    (hheat : ∀ x, ∀ t ∈ Ioo 0 T, heatParabolicOperator u x t = 0)
    (hgrowth : ∀ x, ∀ t ∈ Ioo 0 T, u x t ≤ A * Real.exp (a * ‖x‖ ^ 2)) :
    (⨆ (x : ℝ^n) (t : Ioc (0 : ℝ) T), (u x t : EReal)) =
      ⨆ x : ℝ^n, (u x 0 : EReal) := by
  apply le_antisymm
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro M hM
    have hinitial (x : ℝ^n) : u x 0 ≤ M :=
      EReal.coe_le_coe_iff.mp ((le_iSup (fun y : ℝ^n ↦ (u y 0 : EReal)) x).trans hM.le)
    have hbound := heat_subsolution_le_of_gaussian_growth ha hT u hucont huspace hutime
      (fun x t ht ↦ (hheat x t ht).le) hgrowth hinitial
    exact iSup_le fun x ↦ iSup_le fun t ↦
      EReal.coe_le_coe (hbound x t ⟨t.property.1.le, t.property.2⟩)
  · refine iSup_le fun x ↦ ?_
    have hcont : ContinuousOn (u x) (Icc 0 T) :=
      hucont.comp (f := fun s ↦ (x, s)) (by fun_prop) (fun s hs ↦ ⟨mem_univ _, hs⟩)
    have hle : ∀ s ∈ Ioc 0 T, (u x s : EReal) ≤
        ⨆ (y : ℝ^n) (t : Ioc (0 : ℝ) T), (u y t : EReal) :=
      fun s hs ↦ le_iSup_of_le x (le_iSup_of_le (⟨s, hs⟩ : Ioc (0 : ℝ) T) le_rfl)
    apply le_on_closure hle
      (by simpa only [closure_Ioc hT.ne, Function.comp_def] using
        continuous_coe_real_ereal.comp_continuousOn hcont) continuousOn_const
    simpa only [closure_Ioc hT.ne] using (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)

/-- The whole-space heat maximum principle with one-sided Gaussian growth, in the
closed-slab form of Evans's §2.3.3(a), Theorem 6. Extended-real suprema include
initial data that have no finite upper bound. -/
theorem iSup_eq_initial_of_gaussian_growth {n : ℕ} {A a T : ℝ}
    (ha : 0 ≤ a) (hT : 0 < T) (u : ℝ^n → ℝ → ℝ)
    (hucont : ContinuousOn (fun p ↦ u p.1 p.2) (univ ×ˢ Icc 0 T))
    (huspace : ∀ x, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (u x) t)
    (hheat : ∀ x, ∀ t ∈ Ioo 0 T, heatParabolicOperator u x t = 0)
    (hgrowth : ∀ x, ∀ t ∈ Ioo 0 T, u x t ≤ A * Real.exp (a * ‖x‖ ^ 2)) :
    (⨆ (x : ℝ^n) (t : Icc (0 : ℝ) T), (u x t : EReal)) =
      ⨆ x : ℝ^n, (u x 0 : EReal) := by
  have hpositive := iSup_Ioc_eq_initial_of_gaussian_growth ha hT u hucont huspace
    hutime hheat hgrowth
  apply le_antisymm
  · refine iSup_le fun x ↦ iSup_le fun t ↦ ?_
    rcases t.property.1.eq_or_lt with ht | ht
    · rw [← ht]
      exact le_iSup (fun y : ℝ^n ↦ (u y 0 : EReal)) x
    · calc
        (u x t : EReal) ≤ ⨆ (y : ℝ^n) (s : Ioc (0 : ℝ) T), (u y s : EReal) :=
          le_iSup_of_le x (le_iSup_of_le (⟨t, ht, t.property.2⟩ : Ioc (0 : ℝ) T) le_rfl)
        _ = _ := hpositive
  · exact iSup_le fun x ↦
      le_iSup_of_le x (le_iSup_of_le (⟨0, le_rfl, hT.le⟩ : Icc (0 : ℝ) T) le_rfl)

/-- Two classical solutions of the same forced heat equation with the same initial
data and possibly different two-sided Gaussian bounds agree on the closed slab.
The forcing need not satisfy any additional regularity assumption. -/
theorem eq_of_gaussian_growth {n : ℕ} {A₁ A₂ a₁ a₂ T : ℝ}
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hT : 0 < T) (u v f : ℝ^n → ℝ → ℝ)
    (hucont : ContinuousOn (fun p ↦ u p.1 p.2) (univ ×ˢ Icc 0 T))
    (hvcont : ContinuousOn (fun p ↦ v p.1 p.2) (univ ×ˢ Icc 0 T))
    (huspace : ∀ x, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hvspace : ∀ x, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ v y t) x)
    (hutime : ∀ x, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (u x) t)
    (hvtime : ∀ x, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (v x) t)
    (hueq : ∀ x, ∀ t ∈ Ioo 0 T, heatParabolicOperator u x t = f x t)
    (hveq : ∀ x, ∀ t ∈ Ioo 0 T, heatParabolicOperator v x t = f x t)
    (hugrowth : ∀ x, ∀ t ∈ Ioo 0 T, |u x t| ≤ A₁ * Real.exp (a₁ * ‖x‖ ^ 2))
    (hvgrowth : ∀ x, ∀ t ∈ Ioo 0 T, |v x t| ≤ A₂ * Real.exp (a₂ * ‖x‖ ^ 2))
    (hinitial : ∀ x, u x 0 = v x 0) :
    ∀ x, ∀ t ∈ Icc 0 T, u x t = v x t := by
  let w : ℝ^n → ℝ → ℝ := fun x t ↦ u x t - v x t
  have hwcont : ContinuousOn (fun p ↦ w p.1 p.2) (univ ×ˢ Icc 0 T) :=
    hucont.sub hvcont
  have hwspace (x : ℝ^n) (t : ℝ) (ht : t ∈ Ioo 0 T) :
      ContDiffAt ℝ 2 (fun y ↦ w y t) x :=
    (huspace x t ht).sub (hvspace x t ht)
  have hwtime (x : ℝ^n) (t : ℝ) (ht : t ∈ Ioo 0 T) :
      DifferentiableAt ℝ (w x) t :=
    (hutime x t ht).sub (hvtime x t ht)
  have hweq (x : ℝ^n) (t : ℝ) (ht : t ∈ Ioo 0 T) :
      heatParabolicOperator w x t = 0 := by
    have hderiv : deriv (w x) t = deriv (u x) t - deriv (v x) t :=
      ((hutime x t ht).hasDerivAt.sub (hvtime x t ht).hasDerivAt).deriv
    have hu := hueq x t ht
    have hv := hveq x t ht
    unfold heatParabolicOperator at *
    rw [hderiv]
    dsimp [w]
    rw [PDE.laplacian_sub _ _ x (huspace x t ht) (hvspace x t ht)]
    linarith
  have hwgrowth (x : ℝ^n) (t : ℝ) (ht : t ∈ Ioo 0 T) :
      |w x t| ≤ (A₁ + A₂) * Real.exp ((a₁ + a₂) * ‖x‖ ^ 2) := by
    have h₁ : Real.exp (a₁ * ‖x‖ ^ 2) ≤ Real.exp ((a₁ + a₂) * ‖x‖ ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ha₂)
        (sq_nonneg _))
    have h₂ : Real.exp (a₂ * ‖x‖ ^ 2) ≤ Real.exp ((a₁ + a₂) * ‖x‖ ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ha₁)
        (sq_nonneg _))
    calc
      |w x t| ≤ |u x t| + |v x t| := by
        simpa only [w, sub_eq_add_neg, abs_neg] using abs_add_le (u x t) (-v x t)
      _ ≤ A₁ * Real.exp (a₁ * ‖x‖ ^ 2) + A₂ * Real.exp (a₂ * ‖x‖ ^ 2) :=
        add_le_add (hugrowth x t ht) (hvgrowth x t ht)
      _ ≤ A₁ * Real.exp ((a₁ + a₂) * ‖x‖ ^ 2) +
          A₂ * Real.exp ((a₁ + a₂) * ‖x‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left h₁ hA₁) (mul_le_mul_of_nonneg_left h₂ hA₂)
      _ = (A₁ + A₂) * Real.exp ((a₁ + a₂) * ‖x‖ ^ 2) := (add_mul _ _ _).symm
  have hwzero (x : ℝ^n) : w x 0 = 0 := sub_eq_zero.mpr (hinitial x)
  have hupper := heat_subsolution_le_of_gaussian_growth (add_nonneg ha₁ ha₂) hT w
    hwcont hwspace hwtime (fun x t ht ↦ (hweq x t ht).le)
    (fun x t ht ↦ (le_abs_self _).trans (hwgrowth x t ht)) (fun x ↦ (hwzero x).le)
  have hlower := heat_subsolution_le_of_gaussian_growth (add_nonneg ha₁ ha₂) hT
    (fun x t ↦ -w x t) hwcont.neg
    (fun x t ht ↦ (hwspace x t ht).neg)
    (fun x t ht ↦ (hwtime x t ht).neg)
    (fun x t ht ↦ by simp only [heatParabolicOperator_neg, hweq x t ht, neg_zero, le_refl])
    (fun x t ht ↦ (neg_le_abs _).trans (hwgrowth x t ht))
    (fun x ↦ by rw [hwzero, neg_zero])
  intro x t ht
  have hu := hupper x t ht
  have hv := hlower x t ht
  dsimp [w] at hu hv
  linarith

end HeatEquation
