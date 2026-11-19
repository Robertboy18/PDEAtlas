/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.OneDimensional.BoundaryLayer.Variable.Outer
import CAS.ExactTactic

/-!
# Freezing the drift at the inflow boundary

A compact C¹ drift has an ε-independent Lipschitz bound. Two explicit
exponential barriers then compare the constructed homogeneous correction with
`exp (-a(0) x / ε)`. The estimate keeps the finite-interval endpoint tail and
is valid for every positive ε, including when the coefficient variation is zero.
-/

@[expose] public section

noncomputable section
open Set
namespace PDE.Elliptic.BoundaryLayer.Variable

/-- Compact C¹ data have a fixed Lipschitz bound relative to the left endpoint. -/
theorem drift_bound {L : ℝ} (hL : 0 < L) {U : Set ℝ} (hU : IsOpen U)
    (hIU : Icc 0 L ⊆ U) (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a U) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc 0 L, |a x - a 0| ≤ K * x := by
  have hc := (ha.continuousOn_deriv_of_isOpen hU le_rfl).mono hIU
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun x hx ↦ ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y hy ↦ (ha.contDiffAt (hU.mem_nhds (hIU hy))).differentiableAt (by norm_num))
    (fun y hy ↦ (hC y hy).trans (le_max_left C 0)) (convex_Icc (0 : ℝ) L)
    (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL.le⟩) hx
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hx.1] using h

/-- A linear prefactor is absorbed by half of the exponential decay. -/
theorem weighted_exp_le {b μ t : ℝ} (hμ : 0 < μ) (hb : 2 * μ ≤ b) (ht : 0 ≤ t) :
    t * Real.exp (-b * t) ≤ Real.exp (-μ * t) / μ := by
  have hsmall : (μ * t) * Real.exp (-μ * t) ≤ 1 := by
    have h := Real.mul_exp_neg_le_exp_neg_one (μ * t)
    simpa only [neg_mul] using h.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hsplit : Real.exp (-(2 * μ) * t) = Real.exp (-μ * t) * Real.exp (-μ * t) := by
    rw [← Real.exp_add]
    congr 1
    cas
  have hdecay : Real.exp (-b * t) ≤ Real.exp (-(2 * μ) * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hb) ht)
  apply (le_div_iff₀ hμ).mpr
  calc
    (t * Real.exp (-b * t)) * μ ≤ (t * Real.exp (-(2 * μ) * t)) * μ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdecay ht) hμ.le
    _ = ((μ * t) * Real.exp (-μ * t)) * Real.exp (-μ * t) := by rw [hsplit]; ring
    _ ≤ 1 * Real.exp (-μ * t) :=
      mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
    _ = _ := one_mul _

/-- Two explicit exponentials provide the barriers for freezing the drift at the boundary. -/
theorem frozen_barrier_operator (a : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (b μ c d x : ℝ) :
    ε * deriv (deriv (fun y ↦ Real.exp (-b * y / ε) +
      c * ε * Real.exp (-μ * y / ε) + d)) x +
      a x * deriv (fun y ↦ Real.exp (-b * y / ε) +
        c * ε * Real.exp (-μ * y / ε) + d) x =
      b * (b - a x) / ε * Real.exp (-b * x / ε) +
        c * μ * (μ - a x) * Real.exp (-μ * x / ε) := by
  let F : ℝ → ℝ := fun y ↦ Real.exp (-b * y / ε) +
    c * ε * Real.exp (-μ * y / ε) + d
  have hd (y : ℝ) : HasDerivAt F
      ((-b / ε) * Real.exp (-b * y / ε) - c * μ * Real.exp (-μ * y / ε)) y := by
    dsimp [F]
    cas using hε.ne'
  have heq : deriv F = fun y ↦
      (-b / ε) * Real.exp (-b * y / ε) - c * μ * Real.exp (-μ * y / ε) :=
    funext fun y ↦ (hd y).deriv
  have hdd : deriv (deriv F) x = (b / ε) ^ 2 * Real.exp (-b * x / ε) +
      c * μ ^ 2 / ε * Real.exp (-μ * x / ε) := by
    rw [heq]
    cas using hε.ne'
  change ε * deriv (deriv F) x + a x * deriv F x = _
  rw [hdd, (hd x).deriv]
  have hid (z w v : ℝ) :
      ε * ((b / ε) ^ 2 * z + c * μ ^ 2 / ε * w) + v * ((-b / ε) * z - c * μ * w) =
        b * (b - v) / ε * z + c * μ * (μ - v) * w := by cas using hε.ne'
  exact hid _ _ _

/-- The exact homogeneous correction is uniformly close to the frozen exponential profile. -/
theorem frozen_profile_error {L ε μ K : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hμ : 0 < μ) (hK : 0 ≤ K) (a H : ℝ → ℝ)
    (ha : ∀ x ∈ Icc 0 L, 2 * μ ≤ a x)
    (hvariation : ∀ x ∈ Icc 0 L, |a x - a 0| ≤ K * x)
    (hH : ContDiff ℝ 2 H) (hH0 : H 0 = 1) (hHL : H L = 0)
    (hopH : ∀ x ∈ Ioo 0 L, ε * deriv (deriv H) x + a x * deriv H x = 0) :
    ∀ x ∈ Icc 0 L, |H x - Real.exp (-a 0 * x / ε)| ≤
      (a 0 * K / μ ^ 3) * ε * Real.exp (-μ * x / ε) + Real.exp (-a 0 * L / ε) := by
  let b := a 0
  let C := b * K / μ ^ 3
  let T := Real.exp (-b * L / ε)
  have hb : 2 * μ ≤ b := ha 0 ⟨le_rfl, hL.le⟩
  have hbpos : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hbpos.le hK) (pow_nonneg hμ.le _)
  have hCeq : C * μ ^ 2 = b * K / μ := by dsimp [C]; cas using hμ.ne'
  have hres (x : ℝ) (hx : x ∈ Icc 0 L) :
      |b * (b - a x) / ε * Real.exp (-b * x / ε)| ≤
        (b * K / μ) * Real.exp (-μ * x / ε) := by
    have hexp := weighted_exp_le hμ hb (div_nonneg hx.1 hε.le)
    have hn : b * (K * x) / ε * Real.exp (-b * x / ε) =
        (b * K) * ((x / ε) * Real.exp (-b * (x / ε))) := by
      simp only [mul_div_assoc]
      ring
    rw [abs_mul, abs_div, abs_mul, abs_of_pos hbpos, abs_of_pos hε,
      abs_of_pos (Real.exp_pos _), abs_sub_comm b]
    calc
      b * |a x - b| / ε * Real.exp (-b * x / ε) ≤
          b * (K * x) / ε * Real.exp (-b * x / ε) := by
        gcongr
        exact hvariation x hx
      _ = _ := hn
      _ ≤ (b * K) * (Real.exp (-μ * (x / ε)) / μ) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hbpos.le hK)
      _ = _ := by simp only [mul_div_assoc]; ring
  have hbar (x : ℝ) (hx : x ∈ Icc 0 L) :
      C * μ * (μ - a x) * Real.exp (-μ * x / ε) ≤
        -(b * K / μ) * Real.exp (-μ * x / ε) := by
    rw [show -(b * K / μ) = C * μ * -μ by linear_combination hCeq]
    gcongr
    linarith [ha x hx]
  let upper : ℝ → ℝ := fun x ↦ Real.exp (-b * x / ε) +
    C * ε * Real.exp (-μ * x / ε) + T
  let lower : ℝ → ℝ := fun x ↦ Real.exp (-b * x / ε) +
    (-C) * ε * Real.exp (-μ * x / ε) + (-T)
  have hureg : ContDiff ℝ 2 upper := by dsimp [upper]; fun_prop
  have hlreg : ContDiff ℝ 2 lower := by dsimp [lower]; fun_prop
  have ha₀ (x : ℝ) (hx : x ∈ Ioo 0 L) : 0 ≤ a x :=
    (by positivity : (0 : ℝ) ≤ 2 * μ).trans (ha x (Ioo_subset_Icc_self hx))
  have hu := scalar_comparison hL hε a ha₀ hH.continuous.continuousOn
    hureg.continuous.continuousOn (fun _ _ ↦ hH.contDiffAt) (fun _ _ ↦ hureg.contDiffAt)
    (fun x hx ↦ by
      rw [hopH x hx]
      dsimp [upper]
      rw [frozen_barrier_operator a hε]
      have hr := (abs_le.mp (hres x (Ioo_subset_Icc_self hx))).2
      have hh := hbar x (Ioo_subset_Icc_self hx)
      linarith)
    (by simp only [hH0, upper, mul_zero, zero_div, Real.exp_zero, mul_one]
        have hT : 0 ≤ T := (Real.exp_pos _).le
        nlinarith)
    (by rw [hHL]; dsimp [upper]; positivity)
  have hl := scalar_comparison hL hε a ha₀ hlreg.continuous.continuousOn
    hH.continuous.continuousOn (fun _ _ ↦ hlreg.contDiffAt) (fun _ _ ↦ hH.contDiffAt)
    (fun x hx ↦ by
      rw [hopH x hx]
      dsimp [lower]
      rw [frozen_barrier_operator a hε]
      have hr := (abs_le.mp (hres x (Ioo_subset_Icc_self hx))).1
      have hh := hbar x (Ioo_subset_Icc_self hx)
      nlinarith)
    (by simp only [hH0, lower, mul_zero, zero_div, Real.exp_zero, mul_one]
        have : 0 ≤ T := (Real.exp_pos _).le
        nlinarith)
    (by
      rw [hHL]
      dsimp [lower, T]
      have hc := mul_nonneg (mul_nonneg hC hε.le) (Real.exp_pos (-μ * L / ε)).le
      nlinarith)
  intro x hx
  apply abs_le.mpr
  have hupper := hu x hx
  have hlower := hl x hx
  dsimp [upper, lower, C, b, T] at hupper hlower
  constructor <;> nlinarith

end PDE.Elliptic.BoundaryLayer.Variable
