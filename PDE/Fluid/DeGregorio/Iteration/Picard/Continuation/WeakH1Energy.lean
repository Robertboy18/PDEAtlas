/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakRescaledEnergy
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakProduction
public import PDE.Analysis.Evolution.Core.Gronwall
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# H¹ control of the weak second-derivative energy

The lower derivative supplies the bounded multipliers in the second-derivative
equation. The estimate for the first derivative in L∞ uses its weak derivative
in L². Young's inequality then bounds the production by H¹ times the augmented
energy `B₁² + ‖ωₓₓ‖₂²`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Topology Sobolev

namespace DeGregorio.Iteration

local notation "L₂" => Lp ℝ 2 (volume : Measure ℝ)

/-- The second-derivative production is bounded using only bounded lower
coefficients and L² highest derivatives. These are the one-dimensional H¹
and weak H² bounds supplied by the coupled Hilbert jet. -/
theorem norm_secondDerivative_energy_production_le_of_bounds
    {r G : L₂} {w q h d : ℝ → ℝ} {ρ M : ℝ}
    (hw : Continuous w) (hq : Continuous q) (hh : Continuous h)
    (hM : 0 ≤ M) (hρ : |ρ| ≤ M)
    (hW : ∀ x, ‖w x‖ ≤ M) (hH : ∀ x, ‖h x‖ ≤ M)
    (hQ : ∀ x, ‖q x‖ ≤ M + ‖r‖)
    (hd : MemLp d 2 volume) (hdnorm : lpNorm d 2 volume ≤ M)
    (hG : (G : ℝ → ℝ) =ᵐ[volume] fun x ↦
      -(ρ + h x) * r x + realHilbertTransformL2 r x * w x + d x * q x) :
    ‖(∫ x, (ρ + h x) * (r x) ^ 2) + 2 * inner ℝ G r‖ ≤
      11 * M * (M ^ 2 + ‖r‖ ^ 2) := by
  let k := fun x ↦ ρ + h x
  have hk : Continuous k := continuous_const.add hh
  have hK (x : ℝ) : ‖k x‖ ≤ 2 * M := by
    apply (norm_add_le ρ (h x)).trans
    rw [Real.norm_eq_abs ρ]
    linarith only [hρ, hH x]
  let X := (memLp_mul_of_bounded (Lp.memLp r) hk hK).toLp (fun x ↦ r x * k x)
  let Y := (memLp_mul_of_bounded (Lp.memLp (realHilbertTransformL2 r)) hw hW).toLp
    (fun x ↦ realHilbertTransformL2 r x * w x)
  let Z := (memLp_mul_of_bounded hd hq hQ).toLp (fun x ↦ d x * q x)
  have hX : ‖X‖ ≤ 2 * M * ‖r‖ := by
    simpa only [Lp.toLp_coeFn] using norm_toLp_mul_of_bounded (Lp.memLp r) hk hK
  have hY : ‖Y‖ ≤ M * ‖r‖ := by
    simpa only [Lp.toLp_coeFn, norm_realHilbertTransformL2] using
      norm_toLp_mul_of_bounded (Lp.memLp (realHilbertTransformL2 r)) hw hW
  have hZ : ‖Z‖ ≤ (M + ‖r‖) * M := by
    apply (norm_toLp_mul_of_bounded hd hq hQ).trans
    rw [Lp.norm_toLp]
    exact mul_le_mul_of_nonneg_left hdnorm (add_nonneg hM (norm_nonneg _))
  have hXrep : (X : ℝ → ℝ) =ᵐ[volume] fun x ↦ r x * k x :=
    (memLp_mul_of_bounded (Lp.memLp r) hk hK).coeFn_toLp
  have hYrep : (Y : ℝ → ℝ) =ᵐ[volume] fun x ↦ realHilbertTransformL2 r x * w x :=
    (memLp_mul_of_bounded (Lp.memLp (realHilbertTransformL2 r)) hw hW).coeFn_toLp
  have hZrep : (Z : ℝ → ℝ) =ᵐ[volume] fun x ↦ d x * q x :=
    (memLp_mul_of_bounded hd hq hQ).coeFn_toLp
  have hGsum : G = -X + Y + Z := by
    apply Lp.ext
    filter_upwards [hG, hXrep, hYrep, hZrep, Lp.coeFn_add (-X + Y) Z,
      Lp.coeFn_add (-X) Y, Lp.coeFn_neg X] with x hx hXx hYx hZx hsum hadd hneg
    simp only [Pi.add_apply, Pi.neg_apply] at hsum hadd hneg
    rw [hx, hsum, hadd, hneg, hXx, hYx, hZx]
    dsimp only [k]
    ring
  have hGnorm : ‖G‖ ≤ 4 * M * ‖r‖ + M ^ 2 := by
    rw [hGsum]
    calc
      ‖-X + Y + Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ := by
        simpa only [norm_neg] using (norm_add_le (-X + Y) Z).trans
          (add_le_add (norm_add_le (-X) Y) le_rfl)
      _ ≤ 2 * M * ‖r‖ + M * ‖r‖ + (M + ‖r‖) * M :=
        add_le_add (add_le_add hX hY) hZ
      _ = _ := by ring
  have hwork : (∫ x, (ρ + h x) * (r x) ^ 2) = inner ℝ X r := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hXrep] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial]
    dsimp only [k]
    ring
  rw [hwork]
  calc
    ‖inner ℝ X r + 2 * inner ℝ G r‖ ≤
        ‖inner ℝ X r‖ + 2 * ‖inner ℝ G r‖ := by
      simpa only [norm_mul, Real.norm_ofNat] using norm_add_le (inner ℝ X r) (2 * inner ℝ G r)
    _ ≤ ‖X‖ * ‖r‖ + 2 * (‖G‖ * ‖r‖) :=
      add_le_add (norm_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num))
    _ ≤ (2 * M * ‖r‖) * ‖r‖ + 2 * ((4 * M * ‖r‖ + M ^ 2) * ‖r‖) :=
      add_le_add (mul_le_mul_of_nonneg_right hX (norm_nonneg _))
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hGnorm (norm_nonneg _)) (by norm_num))
    _ ≤ 11 * M * (M ^ 2 + ‖r‖ ^ 2) := by
      have hsq := mul_nonneg hM (sq_nonneg (M - ‖r‖))
      have hcube := mul_nonneg hM (sq_nonneg M)
      nlinarith

/-- The normalized weak Hilbert jet supplies every coefficient bound in
`norm_secondDerivative_energy_production_le_of_bounds` from its H¹ size. -/
theorem norm_secondDerivative_energy_production_le_of_weak_jet
    {w u : ℝ → ℝ} {r G : L₂} {R M : ℝ}
    (hw : ContDiff ℝ 1 w) (hu : ContDiff ℝ 1 u)
    (hpair : IsHilbertPair w (deriv u))
    (hwq : HasWeakTimeDerivativeOn univ w (deriv w))
    (hqr : HasWeakTimeDerivativeOn univ (deriv w) r)
    (hq : MemLp (deriv w) 2 volume)
    (hzero : u 0 = 0) (hR : 0 < R)
    (hH1 : lpNorm w 2 volume + lpNorm (deriv w) 2 volume ≤ M)
    (hG : (G : ℝ → ℝ) =ᵐ[volume] fun x ↦
      -(-u R / R + deriv u x) * r x +
        realHilbertTransformL2 r x * w x + deriv (deriv u) x * deriv w x) :
    ‖(∫ x, (-u R / R + deriv u x) * (r x) ^ 2) + 2 * inner ℝ G r‖ ≤
      11 * M * (M ^ 2 + ‖r‖ ^ 2) := by
  obtain ⟨_, hpair₁, _⟩ := IsHilbertPair.exists_weak_velocity_jet
    hpair hu hq (Lp.memLp r) hwq hqr
  have hM : 0 ≤ M := (add_nonneg lpNorm_nonneg lpNorm_nonneg).trans hH1
  have hρ := (abs_endpoint_rate_le_of_weak_derivative hu hpair hpair₁ hwq hzero hR).trans hH1
  have hW (x : ℝ) : ‖w x‖ ≤ M :=
    (hwq.norm_apply_le_eLpNorm_toReal_add hw.continuous (by norm_num)
      hpair.memLp_left hq x).trans hH1
  have hH (x : ℝ) : ‖deriv u x‖ ≤ M :=
    (hpair.norm_le_of_weak_derivative hpair₁ hwq (hu.continuous_deriv le_rfl) x).trans hH1
  have hqM : lpNorm (deriv w) 2 volume ≤ M :=
    (le_add_of_nonneg_left lpNorm_nonneg).trans hH1
  have hQ (x : ℝ) : ‖deriv w x‖ ≤ M + ‖r‖ := by
    have h := hqr.norm_apply_le_eLpNorm_toReal_add (hw.continuous_deriv le_rfl)
      (by norm_num) hq (Lp.memLp r) x
    change ‖deriv w x‖ ≤ lpNorm (deriv w) 2 volume + ‖r‖ at h
    exact h.trans (add_le_add hqM le_rfl)
  have hd : lpNorm (deriv (deriv u)) 2 volume ≤ M := by
    change (eLpNorm (deriv (deriv u)) 2 volume).toReal ≤ M
    rw [hpair₁.eLpNorm_eq]
    exact hqM
  exact norm_secondDerivative_energy_production_le_of_bounds hw.continuous
    (hw.continuous_deriv le_rfl) (hu.continuous_deriv le_rfl)
    hM hρ hW hH hQ hpair₁.memLp_right hd hG

end DeGregorio.Iteration
