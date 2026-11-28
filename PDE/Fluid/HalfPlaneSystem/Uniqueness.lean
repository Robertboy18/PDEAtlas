/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Lagrangian
public import PDE.Analysis.ODE.Flow.Inverse
public import PDE.Analysis.ODE.Flow.Estimates
public import PDE.Analysis.ODE.Flow.Comparison
import PDE.Fluid.Boussinesq.HalfPlane.Uniqueness
import PDE.Fluid.Incompressible.HalfPlane.VelocityComparison
import PDE.Analysis.Calculus.SliceDerivative
import PDE.Analysis.Calculus.HolderInterpolation
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Uniqueness of solutions of a half-plane system

This module proves that a classical solution of a half-plane system is determined, forward in time,
by its data on the closed half-plane. The velocity gradient depends on the vorticity with a
logarithmic loss, so the distance of two solutions satisfies an inequality with the Osgood modulus
and not a linear one; the proof runs along the particle trajectories and closes with Osgood's lemma.
Below the boundary the fields of a solution are not determined, and no stability estimate for
different data is stated.

Two solutions in the class `IsSolutionOn U κ R₀` with the same data at time `0` agree on the closed
half-plane at every later time of a common interval. Of the velocity law the argument needs only its
size bound, its homogeneous Kato bound and the log-Lipschitz bound of the derivative of the field of
a `C¹` datum. With `X, X'` the trajectories and `J, J'` their first variations on `[0, b]`, let
`E(s)` be the supremum over `r ∈ [0, s]` and labels `a` in the closed half-plane of
`‖X(r, a) - X'(r, a)‖ + ‖J(r, a) - J'(r, a)‖`. Then:

* the vorticities differ by at most `c₃ E(s)` at time `s` (`abs_vorticity_sub_le_of_le`): the
  Lagrangian vorticity of the first solution is Lipschitz in the label, the labels differ by the
  difference of the trajectories, and the forcing `κ(X) ∂₁θ(X) = κ(X) Dθ₀(a)(J⁻¹ e₁)` along a
  trajectory has a difference controlled by `J - J'` and, through the Lipschitz coefficient `κ`, by
  `X - X'` (the notation `∂₁`, `e₁` is that of `Lagrangian.lean`);
* the fields differ by `C E(s)` and their derivatives by `C φ(E(s))` on the closed half-plane, with
  `φ` the Osgood modulus: the size and homogeneous Kato bounds of the law, by linearity;
* the derivative of the first field is log-Lipschitz, a modulus `C φ(min q A)`
  (`norm_fderivWithin_sub_le_osgoodModulus_min`);
* the comparison of flows and of their variations gives `E(s) ≤ C ∫₀ˢ φ(E)`, so `E = 0` by the
  Osgood lemma.

## Main results

* `IsSolutionOn.eqOn_of_hasDataAt`: agreement on `[0, b] × H̄` for solutions on `I ⊇ [0, b]` with
  the same data at time `0` on the closed half-plane.
* `IsSolutionOn.eq_of_hasDataAt`: agreement at every time `t ≥ 0` of an order-connected `I ∋ 0`.
* `Fields.shiftTime`, `IsSolutionOn.shiftTime`: the class is invariant under shifts of the time.
* `IsSolutionOn.eq_of_eq_at_of_le`: two solutions on an order-connected `I` that agree at a time
  `t₀ ∈ I` agree at every later time of `I`.
* `abs_vorticity_sub_le_of_le`: the vorticities of two solutions with the same data differ at a time
  by a constant times a bound `E` of the differences of their trajectories and first variations up
  to that time.
* `norm_fderivWithin_sub_le_osgoodModulus_min`: the log-Lipschitz bound of the derivative of the
  field of a `C¹` datum, written with the Osgood modulus.

`Maximal.lean` uses uniqueness to glue local solutions and for the uniqueness of the maximal
solution, and `Persistence.lean` uses `IsSolutionOn.eq_of_eq_at_of_le` to compare a solution with a
restarted one. The library also proves the theorem for the Biot-Savart law directly
(`Boussinesq.HalfPlane.IsSolutionOn.eq_of_hasDataAt`).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal Topology
open IncompressibleFlow PDE.Analysis.ODE Boussinesq.HalfPlane

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}

/-- **The log-Lipschitz bound of the derivative of the field as an Osgood modulus.** For `f`
`C¹` within the closed half-plane, vanishing there outside the disc of radius `R ≤ R₀`, with
gradient bounded by `B₁` and the derivative of the field bounded by `K₁` on the closed half-plane,
and `A ≥ 1`: `‖DU f(y) - DU f(z)‖ ≤ (2 C₀₀ B₁ + 2K₁/A) φ_A(min ‖y - z‖ A)`. -/
theorem norm_fderivWithin_sub_le_osgoodModulus_min (hU : IsVelocityLaw U R₀ C) {f : ℝ^2 → ℝ}
    {R B₁ K₁ A : ℝ} (hR : R ≤ R₀) (hf : ContDiffOn ℝ 1 f H̄)
    (hz : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hB : ∀ y : ℝ^2, 0 ≤ y 1 → ‖fderivWithin ℝ f H̄ y‖ ≤ B₁)
    (hK : ∀ y : ℝ^2, 0 ≤ y 1 → ‖fderivWithin ℝ (U f) H̄ y‖ ≤ K₁) (hA : 1 ≤ A)
    {y z : ℝ^2} (hy : 0 ≤ y 1) (hz' : 0 ≤ z 1) :
    ‖fderivWithin ℝ (U f) H̄ y - fderivWithin ℝ (U f) H̄ z‖ ≤
      (2 * (C 0 0 * B₁) + 2 * K₁ / A) * PDE.Analysis.osgoodModulus A (min ‖y - z‖ A) := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans (hB 0 (by simp))
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (hK 0 (by simp))
  have hC0 : 0 ≤ C 0 0 * B₁ := mul_nonneg (hU.const_nonneg 0 0) hB₁
  set q := ‖y - z‖ with hqdef
  rcases le_or_gt q A with hqA | hqA
  · rw [min_eq_left hqA]
    have hlog := hU.norm_fderivWithin_sub_le_log hR hf hz hB y z hy hz'
    have hm := IncompressibleFlow.mul_add_posLog_le_osgoodModulus hA (c := 4) (by norm_num)
      (norm_nonneg (y - z)) hqA
    have hφq : 0 ≤ PDE.Analysis.osgoodModulus A q :=
      PDE.Analysis.osgoodModulus_nonneg (norm_nonneg _) hqA
    have hq1 : q * (1 + Real.posLog (1 / q)) ≤ 2 * PDE.Analysis.osgoodModulus A q := by
      have : q * (4 + 4 * Real.posLog (1 / q)) = 4 * (q * (1 + Real.posLog (1 / q))) := by ring
      linarith
    calc _ ≤ C 0 0 * B₁ * q * (1 + Real.posLog (1 / q)) := hlog
      _ = C 0 0 * B₁ * (q * (1 + Real.posLog (1 / q))) := by ring
      _ ≤ C 0 0 * B₁ * (2 * PDE.Analysis.osgoodModulus A q) :=
          mul_le_mul_of_nonneg_left hq1 hC0
      _ ≤ _ := by
          have : 0 ≤ 2 * K₁ / A * PDE.Analysis.osgoodModulus A q := by positivity
          nlinarith
  · rw [min_eq_right hqA.le, PDE.Analysis.osgoodModulus_self]
    have h2 : ‖fderivWithin ℝ (U f) H̄ y - fderivWithin ℝ (U f) H̄ z‖ ≤ 2 * K₁ :=
      (norm_sub_le _ _).trans (by linarith [hK y hy, hK z hz'])
    have hA' : 2 * K₁ / A * A = 2 * K₁ := div_mul_cancel₀ _ hA0.ne'
    have : 0 ≤ 2 * (C 0 0 * B₁) * A := by positivity
    nlinarith

variable {sol sol' : Fields} {I : Set ℝ} {b : ℝ} {K₀ K₀' : ℝ≥0}

/-- **The vorticities differ by the Lagrangian differences.** If on `[0, q]` the trajectories and
the first variations of two solutions with the same data differ by at most `E` on the closed
half-plane, then at time `q` their vorticities differ by at most
`(B₁ e^{2K₀ b} + b (Bκ₀ N₀ e^{K₁ b} e^{K₁' b} + Bκ₁ N₀ e^{K₁' b})) E` on the closed half-plane,
where `B₁` bounds the gradient of the first vorticity, `N₀` the gradient of the initial
temperature, `K₀` is the global derivative bound of the first velocity field, `K₁, K₁'` bound the
derivatives of the two velocity fields on the closed half-plane, and `Bκ₀, Bκ₁` bound the forcing
coefficient and its derivative. -/
theorem abs_vorticity_sub_le_of_le (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
    (h : IsSolutionOn U κ R₀ sol I) (h' : IsSolutionOn U κ R₀ sol' I)
    (hb : 0 < b) (hI : Icc 0 b ⊆ I)
    (hv : IsC1FieldOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b K₀)
    (hv' : IsC1FieldOn (velocityField U sol') (velocityFieldDeriv U sol') 0 b K₀')
    (hdata : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x 0 = sol'.vorticity x 0 ∧ sol.temperature x 0 = sol'.temperature x 0)
    {B₁ N₀ K₁ K₁' E : ℝ}
    (hB₁ : ∀ s ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖fderiv ℝ (fun y ↦ sol.vorticity y s) x‖ ≤ B₁)
    (hN₀ : ∀ a : ℝ^2, 0 ≤ a 1 → ‖fderiv ℝ (fun y ↦ sol.temperature y 0) a‖ ≤ N₀)
    (hK₁ : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityFieldDeriv U sol r y‖ ≤ K₁)
    (hK₁' : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityFieldDeriv U sol' r y‖ ≤ K₁')
    {q : ℝ} (hq : q ∈ Icc 0 b)
    (hE : ∀ r ∈ Icc 0 q, ∀ a : ℝ^2, 0 ≤ a 1 →
      ‖trajectory U sol b r a - trajectory U sol' b r a‖ +
        ‖variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b r 0 a -
          variationOn (velocityField U sol') (velocityFieldDeriv U sol') 0 b r 0 a‖ ≤ E)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    |sol.vorticity x q - sol'.vorticity x q| ≤
      (B₁ * Real.exp (K₀ * b) * Real.exp (K₀ * b) +
        b * (Bκ 0 * (N₀ * Real.exp (K₁ * b) * Real.exp (K₁' * b)) +
          Bκ 1 * (N₀ * Real.exp (K₁' * b)))) * E := by
  have hL := hv.isLipschitzFieldOn
  have hL' := hv'.isLipschitzFieldOn
  have hκc : Continuous κ := hκ.contDiff_one.continuous
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hS : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b, MapsTo (flowOn (velocityField U sol) 0 b s t) H̄ H̄ :=
    fun s hs t ht ↦ (h.bijOn_flowOn hU hI hL hs ht).mapsTo
  have hS' : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b,
      MapsTo (flowOn (velocityField U sol') 0 b s t) H̄ H̄ :=
    fun s hs t ht ↦ (h'.bijOn_flowOn hU hI hL' hs ht).mapsTo
  have hqq : q ∈ Icc 0 q := ⟨hq.1, le_rfl⟩
  have hE0 : 0 ≤ E := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hE q hqq 0 (by simp))
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ q hq 0 (by simp))
  have hN₀0 : 0 ≤ N₀ := (norm_nonneg _).trans (hN₀ 0 (by simp))
  have hκ0 := hκ.bound_nonneg 0
  have hκ1 := hκ.bound_nonneg 1
  set a' := label U sol' b x q with ha'def
  set a := label U sol b x q with hadef
  have ha' : 0 ≤ a' 1 := h'.label_mem hU hI hL' hb.le hq hx
  have ha : 0 ≤ a 1 := h.label_mem hU hI hL hb.le hq hx
  have hxa' : trajectory U sol' b q a' = x := trajectory_label hL' hb.le hq x
  have hxa : trajectory U sol b q a = x := trajectory_label hL hb.le hq x
  -- the trajectories from `a'` differ by at most `E`
  have hXE : ‖trajectory U sol b q a' - trajectory U sol' b q a'‖ ≤ E :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hE q hqq a' ha')
  -- the labels differ by at most `e^{K₀ b} E`
  have hexp₀ : Real.exp (K₀ * |0 - q|) ≤ Real.exp (K₀ * b) := by
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ K₀.2)
    rw [zero_sub, abs_neg, abs_of_nonneg hq.1]; exact hq.2
  have hlab : ‖a - a'‖ ≤ Real.exp (K₀ * b) * E := by
    have h1 := hL.norm_flowOn_sub_flowOn_le_of_inverse hL' (s := q) (t := 0) hq h0 x
    calc ‖a - a'‖ ≤ Real.exp (K₀ * |0 - q|) *
          ‖trajectory U sol b q a' - trajectory U sol' b q a'‖ := h1
      _ ≤ Real.exp (K₀ * b) * E :=
          mul_le_mul hexp₀ hXE (norm_nonneg _) (Real.exp_pos _).le
  -- the Lagrangian vorticity is Lipschitz in the label
  have hlip := h.abs_vorticity_trajectory_sub_le hU hb hI hv hB₁ hq ha ha'
  rw [hxa] at hlip
  -- the forcing integrals
  have hω := h.vorticity_trajectory hU hκc hb hI hv ha' hq
  have hω' := h'.vorticity_trajectory hU hκc hb hI hv' ha' hq
  rw [hxa'] at hω'
  have hsub : Icc 0 q ⊆ Icc 0 b := Icc_subset_Icc_right hq.2
  have hPc := (h.continuousOn_forcing_trajectory hκc hb hI hv a').mono hsub
  have hPc' := (h'.continuousOn_forcing_trajectory hκc hb hI hv' a').mono hsub
  have hPi := hPc.intervalIntegrable_of_Icc (μ := volume) hq.1
  have hPi' := hPc'.intervalIntegrable_of_Icc (μ := volume) hq.1
  have hgrad : fderiv ℝ (fun y ↦ sol.temperature y 0) a' =
      fderiv ℝ (fun y ↦ sol'.temperature y 0) a' :=
    fderiv_eq_of_eqOn_closedUpper ha'
      ((h.contDiff_temperature (hI h0)).differentiable (by norm_num) a')
      ((h'.contDiff_temperature (hI h0)).differentiable (by norm_num) a')
      fun y hy ↦ (hdata y hy).2
  have hK₁0 : 0 ≤ K₁ := (norm_nonneg _).trans (hK₁ 0 h0 0 (by simp))
  have hK₁0' : 0 ≤ K₁' := (norm_nonneg _).trans (hK₁' 0 h0 0 (by simp))
  have hint : ‖(∫ r in (0)..q, κ (trajectory U sol b r a') *
        (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory U sol b r a')) -
      ∫ r in (0)..q, κ (trajectory U sol' b r a') *
        (∂[(0 : Fin 2)] (fun y ↦ sol'.temperature y r)) (trajectory U sol' b r a')‖ ≤
      (Bκ 0 * (N₀ * Real.exp (K₁ * b) * Real.exp (K₁' * b)) +
        Bκ 1 * (N₀ * Real.exp (K₁' * b))) * E * |q - 0| := by
    rw [← intervalIntegral.integral_sub hPi hPi']
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦ ?_
    have hr' : r ∈ Icc 0 q := by
      rw [uIoc_of_le hq.1] at hr
      exact ⟨hr.1.le, hr.2⟩
    have hrb := hsub hr'
    rw [h.partialDeriv_temperature_trajectory hU hb hI hv ha' hrb,
      h'.partialDeriv_temperature_trajectory hU hb hI hv' ha' hrb, ← hgrad]
    have hW := hv.norm_variationOn_inverse_sub_le hv' hrb h0 a'
    have hWb := hv.norm_variationOn_le_of_invariant hS hK₁ h0 hrb
      (hS r hrb 0 h0 ha')
    have hWb' := hv'.norm_variationOn_le_of_invariant hS' hK₁' h0 hrb
      (hS' r hrb 0 h0 ha')
    have hJE : ‖variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b r 0 a' -
        variationOn (velocityField U sol') (velocityFieldDeriv U sol') 0 b r 0 a'‖ ≤ E :=
      (le_add_of_nonneg_left (norm_nonneg _)).trans (hE r hr' a' ha')
    have hXr : ‖trajectory U sol b r a' - trajectory U sol' b r a'‖ ≤ E :=
      (le_add_of_nonneg_right (norm_nonneg _)).trans (hE r hr' a' ha')
    have hexp (K : ℝ) (hK : 0 ≤ K) : Real.exp (K * |0 - r|) ≤ Real.exp (K * b) := by
      refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hK)
      rw [zero_sub, abs_neg, abs_of_nonneg hr'.1]; exact hrb.2
    set W := variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b 0 r
      (trajectory U sol b r a')
    set W' := variationOn (velocityField U sol') (velocityFieldDeriv U sol') 0 b 0 r
      (trajectory U sol' b r a')
    have hWW : ‖W - W'‖ ≤ Real.exp (K₁ * b) * E * Real.exp (K₁' * b) := by
      refine hW.trans ?_
      gcongr
      · exact hWb.trans (hexp K₁ hK₁0)
      · exact hWb'.trans (hexp K₁' hK₁0')
    have hW'b : ‖W'‖ ≤ Real.exp (K₁' * b) := hWb'.trans (hexp K₁' hK₁0')
    have he : ‖(EuclideanSpace.single 0 1 : ℝ^2)‖ = 1 := by simp
    set D := fderiv ℝ (fun y ↦ sol.temperature y 0) a'
    have hP : ‖D (W (EuclideanSpace.single 0 1)) - D (W' (EuclideanSpace.single 0 1))‖ ≤
        N₀ * Real.exp (K₁ * b) * Real.exp (K₁' * b) * E := by
      calc ‖D (W (EuclideanSpace.single 0 1)) - D (W' (EuclideanSpace.single 0 1))‖
          = ‖D ((W - W') (EuclideanSpace.single 0 1))‖ := by rw [sub_apply, map_sub]
        _ ≤ ‖D‖ * (‖W - W'‖ * ‖(EuclideanSpace.single 0 1 : ℝ^2)‖) :=
            ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)))
        _ ≤ N₀ * (Real.exp (K₁ * b) * E * Real.exp (K₁' * b) * 1) := by
            rw [he]
            exact mul_le_mul (hN₀ a' ha') (by linarith) (by positivity) hN₀0
        _ = N₀ * Real.exp (K₁ * b) * Real.exp (K₁' * b) * E := by ring
    have hP' : ‖D (W' (EuclideanSpace.single 0 1))‖ ≤ N₀ * Real.exp (K₁' * b) := by
      calc ‖D (W' (EuclideanSpace.single 0 1))‖
          ≤ ‖D‖ * (‖W'‖ * ‖(EuclideanSpace.single 0 1 : ℝ^2)‖) :=
            ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)))
        _ ≤ N₀ * (Real.exp (K₁' * b) * 1) := by
            rw [he]
            exact mul_le_mul (hN₀ a' ha') (by linarith) (by positivity) hN₀0
        _ = N₀ * Real.exp (K₁' * b) := by ring
    have hκX := hκ.abs_le (trajectory U sol b r a')
    have hκd := hκ.abs_sub_le (trajectory U sol b r a') (trajectory U sol' b r a')
    set X := trajectory U sol b r a'
    set X' := trajectory U sol' b r a'
    have hsplit : κ X * D (W (EuclideanSpace.single 0 1)) -
        κ X' * D (W' (EuclideanSpace.single 0 1)) =
        κ X * (D (W (EuclideanSpace.single 0 1)) - D (W' (EuclideanSpace.single 0 1))) +
          (κ X - κ X') * D (W' (EuclideanSpace.single 0 1)) := by ring
    rw [hsplit, Real.norm_eq_abs]
    rw [Real.norm_eq_abs] at hP hP'
    calc |κ X * (D (W (EuclideanSpace.single 0 1)) - D (W' (EuclideanSpace.single 0 1))) +
          (κ X - κ X') * D (W' (EuclideanSpace.single 0 1))|
        ≤ |κ X| * |D (W (EuclideanSpace.single 0 1)) - D (W' (EuclideanSpace.single 0 1))| +
          |κ X - κ X'| * |D (W' (EuclideanSpace.single 0 1))| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ Bκ 0 * (N₀ * Real.exp (K₁ * b) * Real.exp (K₁' * b) * E) +
          Bκ 1 * E * (N₀ * Real.exp (K₁' * b)) := by
          gcongr
          exact hκd.trans (mul_le_mul_of_nonneg_left hXr hκ1)
      _ = (Bκ 0 * (N₀ * Real.exp (K₁ * b) * Real.exp (K₁' * b)) +
          Bκ 1 * (N₀ * Real.exp (K₁' * b))) * E := by ring
  have hq0 : |q - 0| ≤ b := by rw [sub_zero, abs_of_nonneg hq.1]; exact hq.2
  have hdiff : sol.vorticity x q - sol'.vorticity x q =
      (sol.vorticity x q - sol.vorticity (trajectory U sol b q a') q) +
      ((∫ r in (0)..q, κ (trajectory U sol b r a') *
          (∂[(0 : Fin 2)] (fun y ↦ sol.temperature y r)) (trajectory U sol b r a')) -
        ∫ r in (0)..q, κ (trajectory U sol' b r a') *
          (∂[(0 : Fin 2)] (fun y ↦ sol'.temperature y r)) (trajectory U sol' b r a')) := by
    rw [hω, hω', (hdata a' ha').1]; ring
  rw [hdiff]
  have hc0 : 0 ≤ Bκ 0 * (N₀ * Real.exp (K₁ * b) * Real.exp (K₁' * b)) +
      Bκ 1 * (N₀ * Real.exp (K₁' * b)) := by positivity
  have hint' := hint.trans (mul_le_mul_of_nonneg_left hq0 (mul_nonneg hc0 hE0))
  rw [Real.norm_eq_abs] at hint'
  calc _ ≤ |sol.vorticity x q - sol.vorticity (trajectory U sol b q a') q| + |_| :=
        abs_add_le _ _
    _ ≤ B₁ * Real.exp (K₀ * b) * (Real.exp (K₀ * b) * E) +
        (Bκ 0 * (N₀ * Real.exp (K₁ * b) * Real.exp (K₁' * b)) +
          Bκ 1 * (N₀ * Real.exp (K₁' * b))) * E * b := by
        gcongr
        exact hlip.trans (mul_le_mul_of_nonneg_left hlab (by positivity))
    _ = _ := by ring

/-- **Uniqueness.** Two solutions on `I ⊇ [0, b]`, `0 < b`, with the same vorticity and
temperature at time `0` on the closed half-plane agree on the closed half-plane at every time of
`[0, b]`. So the data determine the solution, which the gluing of local solutions and the
symmetry of solutions need. Proof: the running supremum `E` of the differences of the
trajectories and of their first variations satisfies `E(s) ≤ C ∫₀ˢ φ(E)` with the Osgood modulus
`φ`, because the vorticities differ by a multiple of `E` and the velocity fields and their
derivatives by `C E` and `C φ(E)`; Osgood's lemma gives `E = 0`, and the Lagrangian form of the
two solutions gives equal fields. -/
theorem IsSolutionOn.eqOn_of_hasDataAt (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) (h : IsSolutionOn U κ R₀ sol I)
    (h' : IsSolutionOn U κ R₀ sol' I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
    (hdata : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x 0 = sol'.vorticity x 0 ∧ sol.temperature x 0 = sol'.temperature x 0) :
    ∀ t ∈ Icc 0 b, ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t := by
  obtain ⟨K₀, hv⟩ := h.exists_isC1FieldOn hU hb hI
  obtain ⟨K₀', hv'⟩ := h'.exists_isC1FieldOn hU hb hI
  have hL := hv.isLipschitzFieldOn
  have hL' := hv'.isLipschitzFieldOn
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hS : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b, MapsTo (flowOn (velocityField U sol) 0 b s t) H̄ H̄ :=
    fun s hs t ht ↦ (h.bijOn_flowOn hU hI hL hs ht).mapsTo
  have hS' : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b,
      MapsTo (flowOn (velocityField U sol') 0 b s t) H̄ H̄ :=
    fun s hs t ht ↦ (h'.bijOn_flowOn hU hI hL' hs ht).mapsTo
  have hconv : Convex ℝ H̄ := PDE.Analysis.convex_closedUpperHalfPlane
  have h0H : (0 : ℝ^2) ∈ H̄ := by simp
  have hC00 := hU.const_nonneg 0 0
  -- uniform bounds of the two vorticities
  obtain ⟨R, hRR, B, B₁, hB0, hB₁0, hω, hB₁⟩ :=
    h.exists_isVorticityHistory (α := 1 / 2) hb hI (by norm_num) (by norm_num)
  obtain ⟨R', hRR', B', B₁', hB0', hB₁0', hω', hB₁'⟩ :=
    h'.exists_isVorticityHistory (α := 1 / 2) hb hI (by norm_num) (by norm_num)
  set M := max B₁ (2 * B) with hMdef
  set M' := max B₁' (2 * B') with hM'def
  have hM0 : 0 ≤ M := hω.holder_nonneg h0
  have hM0' : 0 ≤ M' := hω'.holder_nonneg h0
  obtain ⟨Rθ, -, hRθ⟩ := h.support 0 b hI
  obtain ⟨-, N₀, -, hN₀0, -, hN₀, -, -⟩ := PDE.Analysis.exists_bounds_of_contDiffOn
    (f := sol.temperature) hb hI h.temperature_contDiffOn
    fun t ht x hx hxR ↦ (hRθ t ht x hx hxR).2
  set Rm := max R R' with hRmdef
  have hRm : Rm ≤ R₀ := (max_lt hRR hRR').le
  have hRRm : R ≤ Rm := le_max_left R R'
  have hRRm' : R' ≤ Rm := le_max_right R R'
  have hsupp (r : ℝ) (hr : r ∈ Icc 0 b) : ∀ y : ℝ^2, 0 ≤ y 1 → Rm < ‖y‖ →
      (fun x ↦ sol.vorticity x r) y = 0 := fun y hy hyR ↦
    hω.eq_zero r hr y hy (hRRm.trans_lt hyR)
  have hsupp' (r : ℝ) (hr : r ∈ Icc 0 b) : ∀ y : ℝ^2, 0 ≤ y 1 → Rm < ‖y‖ →
      (fun x ↦ sol'.vorticity x r) y = 0 := fun y hy hyR ↦
    hω'.eq_zero r hr y hy (hRRm'.trans_lt hyR)
  -- the velocity fields on the closed half-plane
  have hvel (r : ℝ) {y : ℝ^2} (hy : 0 ≤ y 1) :
      velocityField U sol r y = U (fun x ↦ sol.vorticity x r) y :=
    IsSolutionOn.velocityField_eq hy
  have hvel' (r : ℝ) {y : ℝ^2} (hy : 0 ≤ y 1) :
      velocityField U sol' r y = U (fun x ↦ sol'.vorticity x r) y :=
    IsSolutionOn.velocityField_eq hy
  have hDvel {r : ℝ} (hr : r ∈ Icc 0 b) {y : ℝ^2} (hy : 0 ≤ y 1) :
      velocityFieldDeriv U sol r y =
        fderivWithin ℝ (U (fun x ↦ sol.vorticity x r)) H̄ y :=
    fderiv_extendedField_of_nonneg le_rfl
      (by simpa using hω.contDiffOn_law hU hRR.le (by norm_num) (by norm_num) hr) hy
  have hDvel' {r : ℝ} (hr : r ∈ Icc 0 b) {y : ℝ^2} (hy : 0 ≤ y 1) :
      velocityFieldDeriv U sol' r y =
        fderivWithin ℝ (U (fun x ↦ sol'.vorticity x r)) H̄ y :=
    fderiv_extendedField_of_nonneg le_rfl
      (by simpa using hω'.contDiffOn_law hU hRR'.le (by norm_num) (by norm_num) hr) hy
  set K₁ := C 0 (1 / 2) * (1 + B * Real.log (2 + M) + B) with hK₁def
  set K₁' := C 0 (1 / 2) * (1 + B' * Real.log (2 + M') + B') with hK₁'def
  have hK₁ : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityFieldDeriv U sol r y‖ ≤ K₁ := fun r hr y hy ↦ by
    rw [hDvel hr hy]
    exact hω.norm_fderivWithin_law_le hU hRR.le (by norm_num) (by norm_num) hr hy
  have hK₁' : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityFieldDeriv U sol' r y‖ ≤ K₁' :=
    fun r hr y hy ↦ by
      rw [hDvel' hr hy]
      exact hω'.norm_fderivWithin_law_le hU hRR'.le (by norm_num) (by norm_num) hr hy
  have hK₁0 : 0 ≤ K₁ := (norm_nonneg _).trans (hK₁ 0 h0 0 h0H)
  have hK₁0' : 0 ≤ K₁' := (norm_nonneg _).trans (hK₁' 0 h0 0 h0H)
  set V := C 0 0 * B with hVdef
  set V' := C 0 0 * B' with hV'def
  have hV : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityField U sol r y‖ ≤ V := fun r hr y hy ↦ by
    rw [hvel r hy]
    exact hω.norm_law_le hU hRR.le hr hy
  have hV' : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ‖velocityField U sol' r y‖ ≤ V' := fun r hr y hy ↦ by
    rw [hvel' r hy]
    exact hω'.norm_law_le hU hRR'.le hr hy
  -- the Lagrangian differences and their running supremum
  set G : ℝ → ℝ^2 → ℝ := fun r a ↦ ‖trajectory U sol b r a - trajectory U sol' b r a‖ +
    ‖variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b r 0 a -
      variationOn (velocityField U sol') (velocityFieldDeriv U sol') 0 b r 0 a‖ with hGdef
  set A₀ := (V + V') * b + Real.exp (K₁ * b) + Real.exp (K₁' * b) with hA₀def
  have hGA : ∀ r ∈ Icc 0 b, ∀ a ∈ H̄, G r a ≤ A₀ := by
    intro r hr a ha
    have hexp (K : ℝ) (hK : 0 ≤ K) : Real.exp (K * |r - 0|) ≤ Real.exp (K * b) := by
      refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hK)
      rw [sub_zero, abs_of_nonneg hr.1]; exact hr.2
    have hr0 : |r - 0| ≤ b := by rw [sub_zero, abs_of_nonneg hr.1]; exact hr.2
    have hX := IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant hS hV hr h0 ha
    have hX' := IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant hS' hV' hr h0 ha
    have hJ := hv.norm_variationOn_le_of_invariant hS hK₁ hr h0 ha
    have hJ' := hv'.norm_variationOn_le_of_invariant hS' hK₁' hr h0 ha
    have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV 0 h0 0 h0H)
    have hV0' : 0 ≤ V' := (norm_nonneg _).trans (hV' 0 h0 0 h0H)
    have h1 : ‖trajectory U sol b r a - trajectory U sol' b r a‖ ≤ (V + V') * b := by
      calc ‖trajectory U sol b r a - trajectory U sol' b r a‖
          = ‖(flowOn (velocityField U sol) 0 b r 0 a - a) -
            (flowOn (velocityField U sol') 0 b r 0 a - a)‖ := by
              rw [sub_sub_sub_cancel_right]; rfl
        _ ≤ V * |r - 0| + V' * |r - 0| := (norm_sub_le _ _).trans (add_le_add hX hX')
        _ ≤ (V + V') * b := by nlinarith
    have h2 := norm_sub_le
      (variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b r 0 a)
      (variationOn (velocityField U sol') (velocityFieldDeriv U sol') 0 b r 0 a)
    have := hexp K₁ hK₁0
    have := hexp K₁' hK₁0'
    simp only [hGdef, hA₀def]
    linarith
  set E : ℝ → ℝ := fun s ↦ sSup ((fun p : ℝ × ℝ^2 ↦ G p.1 p.2) '' (Icc 0 s ×ˢ H̄)) with hEdef
  have hbdd {s : ℝ} (hs : s ≤ b) :
      BddAbove ((fun p : ℝ × ℝ^2 ↦ G p.1 p.2) '' (Icc 0 s ×ˢ H̄)) := by
    refine ⟨A₀, ?_⟩
    rintro _ ⟨⟨r, a⟩, ⟨hr, ha⟩, rfl⟩
    exact hGA r ⟨hr.1, hr.2.trans hs⟩ a ha
  have hne {s : ℝ} (hs : 0 ≤ s) :
      ((fun p : ℝ × ℝ^2 ↦ G p.1 p.2) '' (Icc 0 s ×ˢ H̄)).Nonempty :=
    ⟨_, ⟨(0, 0), ⟨⟨le_rfl, hs⟩, h0H⟩, rfl⟩⟩
  have hGE {s : ℝ} (hs : s ∈ Icc 0 b) : ∀ r ∈ Icc 0 s, ∀ a ∈ H̄, G r a ≤ E s :=
    fun r hr a ha ↦ le_csSup (hbdd hs.2) ⟨(r, a), ⟨hr, ha⟩, rfl⟩
  have hEle {s c : ℝ} (hs : 0 ≤ s) (hc : ∀ r ∈ Icc 0 s, ∀ a ∈ H̄, G r a ≤ c) : E s ≤ c := by
    refine csSup_le (hne hs) ?_
    rintro _ ⟨⟨r, a⟩, ⟨hr, ha⟩, rfl⟩
    exact hc r hr a ha
  have hEmono : MonotoneOn E (Icc 0 b) := fun s hs s' hs' hss' ↦
    csSup_le_csSup (hbdd hs'.2) (hne hs.1)
      (image_mono (prod_mono (Icc_subset_Icc_right hss') subset_rfl))
  have hG0 (r : ℝ) (a : ℝ^2) : 0 ≤ G r a := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hE0 : ∀ s ∈ Icc 0 b, 0 ≤ E s := fun s hs ↦
    (hG0 0 0).trans (hGE hs 0 ⟨le_rfl, hs.1⟩ 0 h0H)
  have hEA : ∀ s ∈ Icc 0 b, E s ≤ A₀ := fun s hs ↦
    hEle hs.1 fun r hr a ha ↦ hGA r ⟨hr.1, hr.2.trans hs.2⟩ a ha
  have hA₀0 : 0 ≤ A₀ := (hE0 0 h0).trans (hEA 0 h0)
  -- step 1: the vorticities differ by `c₃ E`
  set C₃ := B₁ * Real.exp (K₀ * b) * Real.exp (K₀ * b) +
    b * (Bκ 0 * (N₀ * Real.exp (K₁ * b) * Real.exp (K₁' * b)) +
      Bκ 1 * (N₀ * Real.exp (K₁' * b))) with hC₃def
  set c₃ := max C₃ 1 with hc₃def
  have hc₃ : 1 ≤ c₃ := le_max_right _ _
  have hstep₁ : ∀ q ∈ Icc 0 b, ∀ y : ℝ^2, 0 ≤ y 1 →
      |(fun x ↦ sol.vorticity x q) y - (fun x ↦ sol'.vorticity x q) y| ≤ c₃ * E q := by
    intro q hq y hy
    have h1 := abs_vorticity_sub_le_of_le hU hκ h h' hb hI hv hv' hdata hB₁
      (fun a ha ↦ hN₀ 0 h0 a ha) hK₁ hK₁' hq (E := E q) (fun r hr a ha ↦ hGE hq r hr a ha) hy
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hE0 q hq))
  -- the Osgood parameter
  have hV0 : 0 ≤ V := mul_nonneg hC00 hB0
  have hV0' : 0 ≤ V' := mul_nonneg hC00 hB0'
  have hA₀pos : 0 < A₀ := by
    have := Real.exp_pos (K₁ * b)
    have := Real.exp_pos (K₁' * b)
    have : 0 ≤ (V + V') * b := mul_nonneg (add_nonneg hV0 hV0') hb.le
    simp only [hA₀def]
    linarith
  have hc₃0 : 0 ≤ c₃ := zero_le_one.trans hc₃
  set A₁ := 2 * (c₃ * A₀) + (M + M') with hA₁def
  set A := max (max A₁ 1) (max A₀ (c₃ * A₀)) with hAdef
  have hA1 : 1 ≤ A := (le_max_right A₁ 1).trans (le_max_left _ _)
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  have hA₁A : A₁ ≤ A := (le_max_left A₁ 1).trans (le_max_left _ _)
  have hA₀A : A₀ ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hcA₀A : c₃ * A₀ ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hA₁0 : 0 < A₁ := by
    have : 0 < c₃ * A₀ := mul_pos (zero_lt_one.trans_le hc₃) hA₀pos
    simp only [hA₁def]
    linarith
  have hEmemA {q : ℝ} (hq : q ∈ Icc 0 b) : E q ∈ Icc 0 A := ⟨hE0 q hq, (hEA q hq).trans hA₀A⟩
  have hcEmemA {q : ℝ} (hq : q ∈ Icc 0 b) : c₃ * E q ∈ Icc 0 A :=
    ⟨mul_nonneg hc₃0 (hE0 q hq),
      (mul_le_mul_of_nonneg_left (hEA q hq) hc₃0).trans hcA₀A⟩
  -- step 2: the velocity fields differ by `C E` and their derivatives by `C φ(E)`
  have hvd : ∀ q ∈ Icc 0 b, ∀ y ∈ H̄,
      ‖velocityField U sol q y - velocityField U sol' q y‖ ≤ C 0 0 * (c₃ * E q) := by
    intro q hq y hy
    rw [hvel q hy, hvel' q hy]
    exact hU.norm_sub_le hRm (hω.continuousOn q hq) (hsupp q hq) (hω'.continuousOn q hq)
      (hsupp' q hq) (hstep₁ q hq) hy
  set Cκ := 2 * C 0 (1 / 2) with hCκdef
  have hCκ0 : 0 ≤ Cκ := mul_nonneg (by norm_num) (hU.const_nonneg 0 _)
  have hDvd : ∀ q ∈ Icc 0 b, ∀ y ∈ H̄,
      ‖velocityFieldDeriv U sol q y - velocityFieldDeriv U sol' q y‖ ≤
        Cκ * PDE.Analysis.osgoodModulus A (c₃ * E q) := by
    intro q hq y hy
    rw [hDvel hq hy, hDvel' hq hy]
    obtain ⟨hβ0, hβA⟩ := hcEmemA hq
    have hβA' : c₃ * E q ≤ c₃ * A₀ := mul_le_mul_of_nonneg_left (hEA q hq) hc₃0
    have h1 := hU.norm_fderivWithin_sub_le_osgood (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num) hRm (hω.continuousOn q hq) (hsupp q hq) (hω'.continuousOn q hq)
      (hsupp' q hq) (hω.holder q hq) (hω'.holder q hq) hM0 hM0' (hstep₁ q hq) hβA' hy
    rw [← hA₁def] at h1
    have h2 := PDE.Analysis.osgoodModulus_le_osgoodModulus (r := c₃ * E q) hA₁0 hA₁A hβ0
    have h3 := PDE.Analysis.le_osgoodModulus hβ0 hβA
    have hC := hU.const_nonneg 0 (1 / 2)
    refine h1.trans ?_
    calc C 0 (1 / 2) * (PDE.Analysis.osgoodModulus A₁ (c₃ * E q) + c₃ * E q)
        ≤ C 0 (1 / 2) * (PDE.Analysis.osgoodModulus A (c₃ * E q) +
          PDE.Analysis.osgoodModulus A (c₃ * E q)) := by gcongr
      _ = Cκ * PDE.Analysis.osgoodModulus A (c₃ * E q) := by simp only [hCκdef]; ring
  set Cψ := 2 * (C 0 0 * B₁) + 2 * K₁ / A with hCψdef
  have hCψ0 : 0 ≤ Cψ := by
    have : 0 ≤ 2 * K₁ / A := div_nonneg (by linarith) hA0.le
    have : 0 ≤ C 0 0 * B₁ := mul_nonneg hC00 hB₁0
    linarith
  have hψ : ∀ r ∈ Icc 0 b, ∀ y ∈ H̄, ∀ z ∈ H̄,
      ‖velocityFieldDeriv U sol r y - velocityFieldDeriv U sol r z‖ ≤
        Cψ * PDE.Analysis.osgoodModulus A (min ‖y - z‖ A) := by
    intro r hr y hy z hz
    rw [hDvel hr hy, hDvel hr hz]
    have hc1 : ContDiffOn ℝ 1 (fun x ↦ sol.vorticity x r) H̄ :=
      (h.contDiff_vorticity (hI hr)).contDiffOn
    refine norm_fderivWithin_sub_le_osgoodModulus_min hU hRm hc1 (hsupp r hr)
      (fun w hw ↦ ?_)
      (fun w hw ↦ hω.norm_fderivWithin_law_le hU hRR.le (by norm_num) (by norm_num) hr hw)
      hA1 hy hz
    rw [((h.contDiff_vorticity (hI hr)).differentiable (by norm_num) w).fderivWithin
      (uniqueDiffOn_closedUpper w hw)]
    exact hB₁ r hr w hw
  -- monotone majorants
  set Φ : ℝ → ℝ := fun q ↦ PDE.Analysis.osgoodModulus A (E q) with hΦdef
  have hΦmono : MonotoneOn Φ (Icc 0 b) := fun q hq q' hq' hqq' ↦
    PDE.Analysis.monotoneOn_osgoodModulus hA0 (hEmemA hq) (hEmemA hq') (hEmono hq hq' hqq')
  have hΦ0 : ∀ q ∈ Icc 0 b, 0 ≤ Φ q := fun q hq ↦
    PDE.Analysis.osgoodModulus_nonneg (hEmemA hq).1 (hEmemA hq).2
  have hEΦ : ∀ q ∈ Icc 0 b, E q ≤ Φ q := fun q hq ↦
    PDE.Analysis.le_osgoodModulus (hEmemA hq).1 (hEmemA hq).2
  have hε₀mono : MonotoneOn (fun q ↦ C 0 0 * (c₃ * E q)) (Icc 0 b) :=
    fun q hq q' hq' hqq' ↦ mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hEmono hq hq' hqq') hc₃0) hC00
  have hε₁mono : MonotoneOn (fun q ↦ Cκ * PDE.Analysis.osgoodModulus A (c₃ * E q))
      (Icc 0 b) := fun q hq q' hq' hqq' ↦ mul_le_mul_of_nonneg_left
    (PDE.Analysis.monotoneOn_osgoodModulus hA0 (hcEmemA hq) (hcEmemA hq')
      (mul_le_mul_of_nonneg_left (hEmono hq hq' hqq') hc₃0)) hCκ0
  have hmonoSub {u : ℝ → ℝ} (hu : MonotoneOn u (Icc 0 b)) {r : ℝ} (hr : r ∈ Icc 0 b) :
      IntervalIntegrable u volume 0 r := by
    refine MonotoneOn.intervalIntegrable (hu.mono ?_)
    rw [uIcc_of_le hr.1]
    exact Icc_subset_Icc_right hr.2
  set Ctot := Real.exp (K₁ * b) * (C 0 0 * c₃) +
    Real.exp ((K₁ + K₁') * b) * (Cψ + Cκ * c₃) with hCtotdef
  have hCtot0 : 0 ≤ Ctot := by positivity
  -- step 3: comparison of the flows and the variations
  have hGbound : ∀ s ∈ Icc 0 b, ∀ r ∈ Icc 0 s, ∀ a ∈ H̄,
      G r a ≤ Ctot * ∫ q in (0)..s, Φ q := by
    intro s hs r hr a ha
    have hrb : r ∈ Icc 0 b := ⟨hr.1, hr.2.trans hs.2⟩
    have hDflow : ∀ q ∈ Icc 0 b, ‖flowOn (velocityField U sol) 0 b q 0 a -
        flowOn (velocityField U sol') 0 b q 0 a‖ ≤ E q := fun q hq ↦
      (le_add_of_nonneg_right (norm_nonneg _)).trans (hGE hq q ⟨hq.1, le_rfl⟩ a ha)
    have hX := hv.norm_flowOn_sub_flowOn_le_of_invariant hv' hconv hS hS' hK₁ h0 hε₀mono
      (fun q hq ↦ mul_nonneg hC00 (mul_nonneg hc₃0 (hE0 q hq))) hvd ha hrb
    have hJ := hv.norm_variationOn_sub_variationOn_le_of_invariant hv' hS hS' hK₁ hK₁'
      (monotoneOn_osgoodModulus_min hA0 hCψ0)
      (fun q hq ↦ osgoodModulus_min_nonneg hA0 hCψ0 hq) hψ h0 hε₁mono
      (fun q hq ↦ mul_nonneg hCκ0
        (PDE.Analysis.osgoodModulus_nonneg (hcEmemA hq).1 (hcEmemA hq).2))
      hDvd ha hEmono hDflow hrb
    have hΦi := hmonoSub hΦmono hrb
    have hI₁ : ∫ q in (0)..r, C 0 0 * (c₃ * E q) ≤ C 0 0 * c₃ * ∫ q in (0)..r, Φ q := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hr.1 (hmonoSub hε₀mono hrb)
        (hΦi.const_mul _) fun q hq ↦ ?_
      have hqb : q ∈ Icc 0 b := ⟨hq.1, hq.2.trans hrb.2⟩
      have hle := hEΦ q hqb
      have hpos : 0 ≤ C 0 0 * c₃ := mul_nonneg hC00 hc₃0
      calc C 0 0 * (c₃ * E q) = C 0 0 * c₃ * E q := by ring
        _ ≤ C 0 0 * c₃ * Φ q := mul_le_mul_of_nonneg_left hle hpos
    have hI₂ : ∫ q in (0)..r, (Cψ * PDE.Analysis.osgoodModulus A (min (E q) A) +
          Cκ * PDE.Analysis.osgoodModulus A (c₃ * E q)) ≤
        (Cψ + Cκ * c₃) * ∫ q in (0)..r, Φ q := by
      rw [← intervalIntegral.integral_const_mul]
      have hmono2 : MonotoneOn (fun q ↦ Cψ * PDE.Analysis.osgoodModulus A (min (E q) A) +
          Cκ * PDE.Analysis.osgoodModulus A (c₃ * E q)) (Icc 0 b) := by
        refine fun q hq q' hq' hqq' ↦ add_le_add ?_ (hε₁mono hq hq' hqq')
        exact monotoneOn_osgoodModulus_min hA0 hCψ0 (hE0 q hq) (hE0 q' hq')
          (hEmono hq hq' hqq')
      refine intervalIntegral.integral_mono_on hr.1 (hmonoSub hmono2 hrb)
        (hΦi.const_mul _) fun q hq ↦ ?_
      have hqb : q ∈ Icc 0 b := ⟨hq.1, hq.2.trans hrb.2⟩
      rw [min_eq_left (hEmemA hqb).2]
      have hm := PDE.Analysis.osgoodModulus_mul_le hA0 hc₃ (hE0 q hqb)
      have : Cκ * PDE.Analysis.osgoodModulus A (c₃ * E q) ≤ Cκ * (c₃ * Φ q) :=
        mul_le_mul_of_nonneg_left hm hCκ0
      calc Cψ * PDE.Analysis.osgoodModulus A (E q) +
            Cκ * PDE.Analysis.osgoodModulus A (c₃ * E q) ≤ Cψ * Φ q + Cκ * (c₃ * Φ q) :=
            add_le_add le_rfl this
        _ = (Cψ + Cκ * c₃) * Φ q := by ring
    have hrs : ∫ q in (0)..r, Φ q ≤ ∫ q in (0)..s, Φ q :=
      intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
          exact hΦ0 q ⟨hq.1.le, hq.2.trans hs.2⟩)
        (hmonoSub hΦmono hs)
    have he₁ : Real.exp (K₁ * (r - 0)) ≤ Real.exp (K₁ * b) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hrb.2]) hK₁0)
    have he₂ : Real.exp ((K₁ + K₁') * (r - 0)) ≤ Real.exp ((K₁ + K₁') * b) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hrb.2]) (by linarith))
    have hX' : ‖trajectory U sol b r a - trajectory U sol' b r a‖ ≤
        Real.exp (K₁ * b) * (C 0 0 * c₃ * ∫ q in (0)..r, Φ q) :=
      hX.trans (mul_le_mul he₁ hI₁ (intervalIntegral.integral_nonneg hr.1 fun q hq ↦
        mul_nonneg hC00 (mul_nonneg hc₃0 (hE0 q ⟨hq.1, hq.2.trans hrb.2⟩)))
        (Real.exp_pos _).le)
    have hJ' : ‖variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b r 0 a -
          variationOn (velocityField U sol') (velocityFieldDeriv U sol') 0 b r 0 a‖ ≤
        Real.exp ((K₁ + K₁') * b) * ((Cψ + Cκ * c₃) * ∫ q in (0)..r, Φ q) :=
      hJ.trans (mul_le_mul he₂ hI₂ (intervalIntegral.integral_nonneg hr.1 fun q hq ↦
        add_nonneg (osgoodModulus_min_nonneg hA0 hCψ0 (hE0 q ⟨hq.1, hq.2.trans hrb.2⟩))
          (mul_nonneg hCκ0 (PDE.Analysis.osgoodModulus_nonneg
            (hcEmemA ⟨hq.1, hq.2.trans hrb.2⟩).1 (hcEmemA ⟨hq.1, hq.2.trans hrb.2⟩).2)))
        (Real.exp_pos _).le)
    have hsum : G r a ≤ Ctot * ∫ q in (0)..r, Φ q := by
      calc G r a = ‖trajectory U sol b r a - trajectory U sol' b r a‖ +
          ‖variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b r 0 a -
            variationOn (velocityField U sol') (velocityFieldDeriv U sol') 0 b r 0 a‖ := rfl
        _ ≤ Real.exp (K₁ * b) * (C 0 0 * c₃ * ∫ q in (0)..r, Φ q) +
            Real.exp ((K₁ + K₁') * b) * ((Cψ + Cκ * c₃) * ∫ q in (0)..r, Φ q) :=
          add_le_add hX' hJ'
        _ = Ctot * ∫ q in (0)..r, Φ q := by simp only [hCtotdef]; ring
    exact hsum.trans (mul_le_mul_of_nonneg_left hrs hCtot0)
  -- the Osgood lemma
  have hEz := PDE.Analysis.eq_zero_of_le_integral_osgoodModulus hA0 hCtot0 hEmono hE0
    (fun s hs ↦ (hEA s hs).trans hA₀A) (fun s hs ↦ hEle hs.1 (hGbound s hs))
  intro t ht x hx
  have hEt := hEz t ht
  refine ⟨?_, ?_⟩
  · have h1 := hstep₁ t ht x hx
    rw [hEt, mul_zero] at h1
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h1)
  · set a' := label U sol' b x t with ha'def
    have ha' : 0 ≤ a' 1 := h'.label_mem hU hI hL' hb.le ht hx
    have hXE : ‖trajectory U sol b t a' - trajectory U sol' b t a'‖ ≤ 0 := by
      rw [← hEt]
      exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hGE ht t ⟨ht.1, le_rfl⟩ a' ha')
    have hlab := hL.norm_flowOn_sub_flowOn_le_of_inverse hL' (s := t) (t := 0) ht h0 x
    have hlab0 : label U sol b x t = a' := by
      have h2 : ‖label U sol b x t - a'‖ ≤ 0 := hlab.trans
        (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hXE)
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
    rw [h.temperature_eq_label hU hb hI hv ht hx, h'.temperature_eq_label hU hb hI hv' ht hx,
      hlab0, (hdata a' ha').2]

/-- **Uniqueness on an interval.** Two solutions on an order-connected set of times `I ∋ 0` with
the same vorticity and temperature at time `0` on the closed half-plane agree on the closed
half-plane at every time `t ∈ I` with `0 ≤ t`. -/
theorem IsSolutionOn.eq_of_hasDataAt (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) (h : IsSolutionOn U κ R₀ sol I)
    (h' : IsSolutionOn U κ R₀ sol' I) (hI : I.OrdConnected) (h0 : (0 : ℝ) ∈ I)
    (hdata : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x 0 = sol'.vorticity x 0 ∧ sol.temperature x 0 = sol'.temperature x 0)
    {t : ℝ} (ht : t ∈ I) (ht0 : 0 ≤ t) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t := by
  rcases ht0.eq_or_lt with rfl | htpos
  · exact hdata x hx
  · exact h.eqOn_of_hasDataAt hU hκ h' htpos (hI.out h0 ht) hdata t ⟨ht0, le_rfl⟩ x hx

/-! ### Shifting the time -/

/-- The fields of `sol` with the time shifted by `t₀`: the value at `(x, t)` is the value of
`sol` at `(x, t + t₀)`. -/
def Fields.shiftTime (sol : Fields) (t₀ : ℝ) : Fields where
  vorticity x t := sol.vorticity x (t + t₀)
  temperature x t := sol.temperature x (t + t₀)

/-- Solutions are invariant under shifts of the time: the system is autonomous. -/
theorem IsSolutionOn.shiftTime (h : IsSolutionOn U κ R₀ sol I) (t₀ : ℝ) :
    IsSolutionOn U κ R₀ (sol.shiftTime t₀) ((· + t₀) ⁻¹' I) := by
  have hφ : ContDiff ℝ 1 (fun xt : ℝ^2 × ℝ ↦ (xt.1, xt.2 + t₀)) :=
    contDiff_fst.prodMk (contDiff_snd.add contDiff_const)
  have hmaps : MapsTo (fun xt : ℝ^2 × ℝ ↦ (xt.1, xt.2 + t₀)) (univ ×ˢ ((· + t₀) ⁻¹' I))
      (univ ×ˢ I) := fun xt hxt ↦ ⟨mem_univ _, hxt.2⟩
  refine
    { vorticity_contDiffOn := h.vorticity_contDiffOn.comp hφ.contDiffOn hmaps
      temperature_contDiffOn := h.temperature_contDiffOn.comp hφ.contDiffOn hmaps
      vorticity_differentiableAt_time := fun {x t} ht ↦
        DifferentiableAt.comp (g := fun s ↦ sol.vorticity x s) (f := fun s ↦ s + t₀) t
          (h.vorticity_differentiableAt_time ht) ((differentiableAt_id (x := t)).add_const t₀)
      temperature_differentiableAt_time := fun {x t} ht ↦
        DifferentiableAt.comp (g := fun s ↦ sol.temperature x s) (f := fun s ↦ s + t₀) t
          (h.temperature_differentiableAt_time ht) ((differentiableAt_id (x := t)).add_const t₀)
      vorticity_equation := fun {x t} hx ht ↦ ?_
      temperature_equation := fun {x t} hx ht ↦ ?_
      support := fun a b hab ↦ ?_ }
  · have heq := h.vorticity_equation hx ht
    change deriv (fun s ↦ sol.vorticity x (s + t₀)) t + _ = _
    rw [deriv_comp_add_const]
    exact heq
  · have heq := h.temperature_equation hx ht
    change deriv (fun s ↦ sol.temperature x (s + t₀)) t + _ = _
    rw [deriv_comp_add_const]
    exact heq
  · have hsub : Icc (a + t₀) (b + t₀) ⊆ I := fun s hs ↦ by
      have := hab (show s - t₀ ∈ Icc a b from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      simpa using this
    obtain ⟨R, hR, hz⟩ := h.support (a + t₀) (b + t₀) hsub
    exact ⟨R, hR, fun t ht x hx hxR ↦
      hz (t + t₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x hx hxR⟩

/-- **Uniqueness from any time.** Two solutions on an order-connected set of times `I` that agree
on the closed half-plane at a time `t₀ ∈ I` agree on the closed half-plane at every later time of
`I`. -/
theorem IsSolutionOn.eq_of_eq_at_of_le (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) (h : IsSolutionOn U κ R₀ sol I)
    (h' : IsSolutionOn U κ R₀ sol' I) (hI : I.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (hdata : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x t₀ = sol'.vorticity x t₀ ∧ sol.temperature x t₀ = sol'.temperature x t₀)
    {t : ℝ} (ht : t ∈ I) (htt₀ : t₀ ≤ t) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t := by
  have hJ : ((· + t₀) ⁻¹' I).OrdConnected := ⟨fun p hp q hq r hr ↦
    hI.out hp hq ⟨by simpa using hr.1, by simpa using hr.2⟩⟩
  have h0 : (0 : ℝ) ∈ (· + t₀) ⁻¹' I := by simpa using ht₀
  have hd : ∀ y : ℝ^2, 0 ≤ y 1 → (sol.shiftTime t₀).vorticity y 0 =
      (sol'.shiftTime t₀).vorticity y 0 ∧
      (sol.shiftTime t₀).temperature y 0 = (sol'.shiftTime t₀).temperature y 0 := by
    intro y hy
    simpa [Fields.shiftTime] using hdata y hy
  have hmem : t - t₀ ∈ (· + t₀) ⁻¹' I := by simpa using ht
  have := (h.shiftTime t₀).eq_of_hasDataAt hU hκ (h'.shiftTime t₀) hJ h0 hd hmem
    (sub_nonneg.mpr htt₀) hx
  simpa [Fields.shiftTime] using this

end HalfPlaneSystem
