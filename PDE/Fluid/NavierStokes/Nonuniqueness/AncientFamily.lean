/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Semilinear.AncientMixed
public import PDE.Fluid.NavierStokes.Nonlinearity.Sobolev
public import PDE.Fluid.NavierStokes.Nonuniqueness.CutoffField
public import PDE.Fluid.NavierStokes.Selfsimilar.ProfileDichotomy

/-!
# The ancient correction family

Let `Ũ` be an unstable profile with the exponential dichotomy `UnstableProfile.dichotomy`:
weight `0 < η ≤ 1/16`, stable and unstable kernels `Ks` and `Ku` from vector `H²` to vector `H³`,
a finite-rank projection `P` annihilating the stable kernel, an eigenvector `e` with eigenvalue
`μ > η`, and homogeneous unstable paths `b c` decoding to `τ ↦ e^{μτ} c e`. At cutoff radius `R`
the velocity in similarity variables is `Ũ + U_cut + U_cor`, and the correction `U_cor` solves
(2.11) of Hou, Wang and Yang. The ancient solutions with unstable terminal coordinate `c e`
solve (2.15):

`U_cor(τ) = e^{μτ} c e + ∫_{-∞}^τ Ks(τ - σ) N(σ) dσ - ∫_τ^0 Ku(σ - τ) N(σ) dσ`,
`N(σ) = F(σ) + L_far(σ) U_cor(σ) - (U_cor(σ)·∇)U_cor(σ)`;

the kernels apply the Leray projection `Π`.

For every `R` above an explicit threshold and every `s ∈ [0, 1]` exactly one small ancient
correction has unstable terminal coordinate `s c₀ e` (`exists_ancient_family`), and
`ancientCorrection D R s` is this fixed point. The decoded equation (2.15) and the
divergence-freeness of the correction are in `AncientFamilyEquation`.

## Main results

* `exists_ancient_family`: existence and uniqueness of the small ancient correction with
  unstable terminal coordinate `s c₀ e`, for all `R` above a threshold and all `s ∈ [0, 1]`.
* `existsUnique_ancientCorrection`, `ancientCorrection_spec`, `eq_ancientCorrection`,
  `projection_ancientCorrection_terminal`, `injOn_ancientCorrection_terminal`: the same with
  the explicit constants, for the chosen fixed point.
* `norm_ancientLift_ancientCorrection_le`: `‖U_cor(τ)‖ ≤ r e^{ητ}`.

## How it works

We follow the contraction argument of Hou, Wang and Yang. On bounded continuous paths
`τ ↦ e^{-ητ} U_cor(τ)` in vector `H³` on `τ ≤ 0` the right side of (2.15) is `b c + G (N u)`, with
the mixed Green operator `G` of the dichotomy (`UnstableProfile.ancientGreen`) and the forcing `N u`
of the cutoff paths (`ancientForcing`). The Green operator has norm at most a constant `C`
(`UnstableProfile.norm_ancientGreen_le`), the coefficient and forcing paths have norms at most
constants times `R^{-1/4}` (`norm_cutoffCoefficientPath_le`, and `norm_cutoffForcingPath_le` for
`R ≥ 1`), and the convection `B` is bounded. For the radius `r = (8 C ‖B‖ + 1)⁻¹`, the amplitude
`c₀ = r / (4 ‖e‖)` and every `R` above the threshold, the source and contraction budgets hold for
every `c = s c₀` with `s ∈ [0, 1]` (`ancientCorrection_budgets`), so the fixed point theorem of the
mixed ancient problem, `PDE.Analysis.Evolution.existsUnique_mixedAncientAffine_of_bounds_ofJoint`,
gives a unique fixed point in the closed ball of radius `r` (`existsUnique_ancientCorrection`). Its
unstable terminal coordinate is `P (u 0) = s c₀ e`, because `P` annihilates the stable kernel and
the unstable integral vanishes at the terminal time (`projection_terminal_of_fixedPoint`).

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 2.2, (2.11), p. 12,
  (2.14)-(2.16) and the contraction argument, pp. 13-14.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace HeatEquation.WholeSpace
open PDE.Analysis.Evolution PDE.Common NavierStokes.SobolevConvection NavierStokes.Selfsimilar
open scoped Sobolev BoundedContinuousFunction

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable (D : UnstableProfile)

namespace UnstableProfile

/-- The mixed Green operator of the localized ancient problem at terminal time `0`: the past
integral of the stable kernel minus the future integral of the unstable kernel of the dichotomy,
from paths in vector `H²` of weight `2η` to paths in vector `H³` of weight `η`. -/
def ancientGreen : (Iic (0 : ℝ) →ᵇ VectorH 3 2) →L[ℝ] (Iic (0 : ℝ) →ᵇ VectorH 3 3) :=
  mixedDuhamelOperatorOfJoint (a := 0) (α := 1 / 2) (β := 2 * D.dichotomy.η) (by norm_num)
    D.dichotomy.ω_lt (by linarith [D.dichotomy.η_pos]) (by linarith [D.dichotomy.η_pos])
    D.dichotomy.η_le_κ D.dichotomy.Ms_nonneg D.dichotomy.Mu_nonneg D.dichotomy.continuousOn_Ks
    D.dichotomy.continuous_Ku D.dichotomy.norm_Ks_le D.dichotomy.norm_Ku_le

/-- The bound `Ms Γ(1/2) (2η - ω)^{-1/2} + Mu / η` of the ancient Green operator. -/
def ancientGreenConstant : ℝ :=
  D.dichotomy.Ms * smoothingMass (1 / 2) (2 * D.dichotomy.η - D.dichotomy.ω) +
    D.dichotomy.Mu / D.dichotomy.η

/-- The bound of the ancient Green operator is nonnegative. -/
theorem ancientGreenConstant_nonneg : 0 ≤ D.ancientGreenConstant :=
  add_nonneg (mul_nonneg D.dichotomy.Ms_nonneg
    (smoothingMass_nonneg (by norm_num) (sub_pos.mpr D.dichotomy.ω_lt)))
    (div_nonneg D.dichotomy.Mu_nonneg D.dichotomy.η_pos.le)

/-- The ancient Green operator has norm at most `ancientGreenConstant`. -/
theorem norm_ancientGreen_le : ‖D.ancientGreen‖ ≤ D.ancientGreenConstant := by
  refine (norm_mixedDuhamelOperatorOfJoint_le _ _ _ _ _ _ _ _ _ _ _).trans_eq ?_
  rw [show 2 * D.dichotomy.η - D.dichotomy.η = D.dichotomy.η by ring, mul_zero, Real.exp_zero,
    mul_one, ancientGreenConstant]

/-- The radius `r = (8 C ‖B‖ + 1)⁻¹` of the ball of ancient corrections, with `C` the bound of
the Green operator and `B` the convection. -/
def ancientRadius : ℝ :=
  (8 * D.ancientGreenConstant * ‖convection‖ + 1)⁻¹

/-- The radius of the ball of ancient corrections is positive. -/
theorem ancientRadius_pos : 0 < D.ancientRadius :=
  inv_pos.mpr (add_pos_of_nonneg_of_pos (mul_nonneg (mul_nonneg (by norm_num)
    D.ancientGreenConstant_nonneg) (norm_nonneg convection)) one_pos)

/-- The amplitude `c₀ = r / (4 ‖e‖)` of the unstable terminal coordinates `s c₀ e`. -/
def ancientAmplitude : ℝ :=
  D.ancientRadius / (4 * ‖D.dichotomy.e‖)

/-- The amplitude of the unstable terminal coordinates is positive. -/
theorem ancientAmplitude_pos : 0 < D.ancientAmplitude :=
  div_pos D.ancientRadius_pos (mul_pos four_pos (norm_pos_iff.mpr D.dichotomy.e_ne_zero))

/-- The constant `4 C (C_F / r + C_L) + 1`, with `C_F` and `C_L` the constants of the forcing and
coefficient bounds, whose fourth power bounds the threshold radius. -/
def ancientThresholdBase : ℝ :=
  4 * D.ancientGreenConstant *
    (cutoffForcingConstant D 2 / D.ancientRadius + cutoffCoefficientConstant D 2) + 1

/-- The threshold `R₀ = max 1 (4 C (C_F / r + C_L) + 1)⁴` of the cutoff radius. -/
def ancientThreshold : ℝ :=
  max 1 (D.ancientThresholdBase ^ 4)

/-- The threshold radius is at least one. -/
theorem one_le_ancientThreshold : 1 ≤ D.ancientThreshold :=
  le_max_left _ _

/-- The base of the threshold radius is at least one. -/
theorem one_le_ancientThresholdBase : 1 ≤ D.ancientThresholdBase := by
  have := D.ancientGreenConstant_nonneg
  have := D.ancientRadius_pos
  have := cutoffForcingConstant_nonneg D 2
  have := cutoffCoefficientConstant_nonneg D 2
  have : 0 ≤ 4 * D.ancientGreenConstant *
      (cutoffForcingConstant D 2 / D.ancientRadius + cutoffCoefficientConstant D 2) := by
    positivity
  unfold ancientThresholdBase
  linarith

/-- Above the threshold, `R^{-1/4}` is at most the inverse of `4 C (C_F / r + C_L) + 1`. -/
theorem rpow_neg_quarter_le_inv_ancientThresholdBase {R : ℝ} (hR : D.ancientThreshold ≤ R) :
    R ^ (-(1 / 4 : ℝ)) ≤ D.ancientThresholdBase⁻¹ := by
  have hM0 : 0 < D.ancientThresholdBase := one_pos.trans_le D.one_le_ancientThresholdBase
  have hR4 : D.ancientThresholdBase ^ 4 ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 ≤ R := (by positivity : 0 ≤ D.ancientThresholdBase ^ 4).trans hR4
  rw [Real.rpow_neg hR0]
  refine inv_anti₀ hM0 ?_
  calc D.ancientThresholdBase = (D.ancientThresholdBase ^ 4) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le]
        norm_num
    _ ≤ R ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hR4 (by norm_num)

end UnstableProfile

/-- The forcing of the localized ancient problem on a path `u` in vector `H³` of weight `η`:
the cutoff forcing path, the cutoff coefficient path applied to `u`, and minus the convection
of `u`, in vector `H²` of weight `2η`. -/
def ancientForcing (R : ℝ) (u : Iic (0 : ℝ) →ᵇ VectorH 3 3) : Iic (0 : ℝ) →ᵇ VectorH 3 2 :=
  fullPathForcing (cutoffCoefficientPath D R D.dichotomy.η) (-convection)
    (cutoffForcingPath D R D.dichotomy.η) u

variable {D} {R s : ℝ}

/-- The arithmetic of the budgets. With `r = (8 C B + 1)⁻¹` and `M = 4 C (C_F / r + C_L) + 1`,
a homogeneous part of size at most `r / 4` and forcing and coefficient sizes at most `C_F / M`
and `C_L / M` give a source budget at most `r` and a contraction budget below one. -/
private theorem ancient_budgets_of_le {C B r M CF CL f L b x : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hCF : 0 ≤ CF) (hCL : 0 ≤ CL) (hr : r = (8 * C * B + 1)⁻¹)
    (hM : M = 4 * C * (CF / r + CL) + 1) (hb : b ≤ r / 4) (hf : f ≤ CF * M⁻¹)
    (hL : L ≤ CL * M⁻¹) :
    b + (C * Real.exp (x * 0)) * (f + L * r + B * r ^ 2) ≤ r ∧
      (C * Real.exp (x * 0)) * (L + 2 * B * r) < 1 := by
  rw [mul_zero, Real.exp_zero, mul_one]
  have hden : 0 < 8 * C * B + 1 := by positivity
  have hr0 : 0 < r := hr ▸ inv_pos.mpr hden
  have hM0 : 0 < M := by
    rw [hM]
    have : 0 ≤ 4 * C * (CF / r + CL) := by positivity
    linarith
  -- the forcing term is at most `r / 4`
  have hX : C * f ≤ r / 4 := by
    have h1 : C * f ≤ C * CF * M⁻¹ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hf hC
    have h2 : 4 * (C * CF) ≤ r * M := by
      have e : r * M = 4 * (C * CF) + (4 * (C * CL) * r + r) := by
        rw [hM]
        field_simp
        ring
      have : 0 ≤ 4 * (C * CL) * r + r := by positivity
      linarith
    have h3 : C * CF * M⁻¹ ≤ r / 4 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hM0]
      linarith
    linarith
  -- the coefficient term is at most `1 / 4`
  have hY : C * L ≤ 1 / 4 := by
    have h1 : C * L ≤ C * CL * M⁻¹ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hL hC
    have h2 : 4 * (C * CL) ≤ M := by
      rw [hM, show 4 * C * (CF / r + CL) + 1 = 4 * C * (CF / r) + 4 * (C * CL) + 1 by ring]
      have : 0 ≤ 4 * C * (CF / r) := by positivity
      linarith
    have h3 : C * CL * M⁻¹ ≤ 1 / 4 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hM0]
      linarith
    linarith
  -- the convection term is at most `1 / 8` per unit radius
  have hZ : C * B * r ≤ 1 / 8 := by
    rw [hr, ← div_eq_mul_inv, div_le_iff₀ hden]
    linarith
  have hYr : C * L * r ≤ r / 4 := (mul_le_mul_of_nonneg_right hY hr0.le).trans_eq (by ring)
  have hZr : C * B * r * r ≤ r / 8 := (mul_le_mul_of_nonneg_right hZ hr0.le).trans_eq (by ring)
  constructor
  · have e1 : C * (f + L * r + B * r ^ 2) = C * f + C * L * r + C * B * r * r := by ring
    rw [e1]
    linarith
  · have e2 : C * (L + 2 * B * r) = C * L + 2 * (C * B * r) := by ring
    rw [e2]
    linarith

/-- The homogeneous part `b (s c₀)` with `s ∈ [0, 1]` has norm at most `r / 4`. -/
theorem norm_b_ancientAmplitude_le (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖D.dichotomy.b (s * D.ancientAmplitude)‖ ≤ D.ancientRadius / 4 := by
  refine (D.dichotomy.norm_b_le _).trans ?_
  have he : 0 < ‖D.dichotomy.e‖ := norm_pos_iff.mpr D.dichotomy.e_ne_zero
  have hc : 0 < D.ancientAmplitude := D.ancientAmplitude_pos
  rw [abs_of_nonneg (mul_nonneg hs.1 hc.le)]
  calc s * D.ancientAmplitude * ‖D.dichotomy.e‖ ≤ 1 * D.ancientAmplitude * ‖D.dichotomy.e‖ := by
        gcongr
        exact hs.2
    _ = D.ancientRadius / 4 := by
        rw [one_mul, UnstableProfile.ancientAmplitude]
        field_simp

/-- The source and contraction budgets of the ancient fixed point hold above the threshold
radius for every terminal amplitude `s c₀` with `s ∈ [0, 1]`. -/
theorem ancientCorrection_budgets (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖D.dichotomy.b (s * D.ancientAmplitude)‖ +
        (D.ancientGreenConstant * Real.exp (D.dichotomy.η * 0)) *
          (‖cutoffForcingPath D R D.dichotomy.η‖ +
            ‖cutoffCoefficientPath D R D.dichotomy.η‖ * D.ancientRadius +
            ‖-convection‖ * D.ancientRadius ^ 2) ≤ D.ancientRadius ∧
      (D.ancientGreenConstant * Real.exp (D.dichotomy.η * 0)) *
          (‖cutoffCoefficientPath D R D.dichotomy.η‖ +
            2 * ‖-convection‖ * D.ancientRadius) < 1 := by
  have hR1 : 1 ≤ R := D.one_le_ancientThreshold.trans hR
  have hρ := D.rpow_neg_quarter_le_inv_ancientThresholdBase hR
  have hCF := cutoffForcingConstant_nonneg D 2
  have hCL := cutoffCoefficientConstant_nonneg D 2
  have hB : ‖-convection‖ = ‖convection‖ := norm_neg convection
  refine ancient_budgets_of_le D.ancientGreenConstant_nonneg (norm_nonneg (-convection)) hCF hCL
    (by rw [hB]; rfl) rfl (norm_b_ancientAmplitude_le hs)
    ((norm_cutoffForcingPath_le D D.dichotomy.η_le hR1).trans
      (mul_le_mul_of_nonneg_left hρ hCF))
    ((norm_cutoffCoefficientPath_le D D.dichotomy.η_le (one_pos.trans_le hR1)).trans
      (mul_le_mul_of_nonneg_left hρ hCL))

variable (D R s)

/-- **Existence and uniqueness of the ancient correction**, with the explicit constants: above
the threshold radius and for `s ∈ [0, 1]` exactly one path in the closed ball of radius `r`
solves `u = b (s c₀) + G (N u)`. -/
theorem existsUnique_ancientCorrection (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃! u : Iic (0 : ℝ) →ᵇ VectorH 3 3, ‖u‖ ≤ D.ancientRadius ∧
      u = D.dichotomy.b (s * D.ancientAmplitude) + D.ancientGreen (ancientForcing D R u) :=
  existsUnique_mixedAncientAffine_of_bounds_ofJoint (a := 0) (α := 1 / 2) (by norm_num)
    D.dichotomy.ω_lt D.dichotomy.η_pos D.dichotomy.η_le_κ D.dichotomy.Ms_nonneg
    D.dichotomy.Mu_nonneg D.ancientRadius_pos.le D.dichotomy.continuousOn_Ks
    D.dichotomy.continuous_Ku D.dichotomy.norm_Ks_le D.dichotomy.norm_Ku_le
    (cutoffCoefficientPath D R D.dichotomy.η) (-convection) (cutoffForcingPath D R D.dichotomy.η)
    (D.dichotomy.b (s * D.ancientAmplitude)) (ancientCorrection_budgets hR hs).1
    (ancientCorrection_budgets hR hs).2

/-- A fixed point of the ancient equation keeps the unstable terminal coordinate `c e` of its
homogeneous part. -/
theorem projection_terminal_of_fixedPoint {c : ℝ} {u : Iic (0 : ℝ) →ᵇ VectorH 3 3}
    (hu : u = D.dichotomy.b c + D.ancientGreen (ancientForcing D R u)) :
    D.dichotomy.P (u ⟨0, self_mem_Iic⟩) = c • D.dichotomy.e := by
  rw [mixed_fullFixedPoint_terminal_projection_ofJoint (by norm_num) D.dichotomy.ω_lt
    D.dichotomy.η_pos D.dichotomy.η_le_κ D.dichotomy.Ms_nonneg D.dichotomy.Mu_nonneg
    D.dichotomy.continuousOn_Ks D.dichotomy.continuous_Ku D.dichotomy.norm_Ks_le
    D.dichotomy.norm_Ku_le (cutoffCoefficientPath D R D.dichotomy.η) (-convection)
    (cutoffForcingPath D R D.dichotomy.η) D.dichotomy.P D.dichotomy.P_Ks hu,
    D.dichotomy.b_zero, map_smul, D.dichotomy.P_e]

/-- **The ancient family with prescribed unstable coordinate** (Hou, Wang and Yang,
Section 2.2). For an unstable profile there are a threshold `R₀`, an
amplitude `c₀ > 0` and a radius `r` such that for every cutoff radius `R ≥ R₀` and every
`s ∈ [0, 1]` exactly one bounded continuous path `u` in the closed ball of radius `r` solves the
weighted form of (2.15),

`u = b (s c₀) + G (f_R + L_R u - B(u, u))`,

with `G` the mixed Green operator of the dichotomy at terminal time `0`, `L_R` and `f_R` the
cutoff coefficient and forcing paths and `B` the convection; its unstable terminal coordinate is
`P (u 0) = s c₀ e`. -/
theorem exists_ancient_family (D : UnstableProfile) :
    ∃ R₀ c₀ r : ℝ, 0 < c₀ ∧ ∀ R ≥ R₀, ∀ s ∈ Icc (0 : ℝ) 1,
      ∃! u : Iic (0 : ℝ) →ᵇ VectorH 3 3, ‖u‖ ≤ r ∧
        u = D.dichotomy.b (s * c₀) +
          mixedDuhamelOperatorOfJoint (a := 0) (α := 1 / 2) (β := 2 * D.dichotomy.η)
            (by norm_num) D.dichotomy.ω_lt (by linarith [D.dichotomy.η_pos])
            (by linarith [D.dichotomy.η_pos]) D.dichotomy.η_le_κ D.dichotomy.Ms_nonneg
            D.dichotomy.Mu_nonneg D.dichotomy.continuousOn_Ks D.dichotomy.continuous_Ku
            D.dichotomy.norm_Ks_le D.dichotomy.norm_Ku_le
            (fullPathForcing (cutoffCoefficientPath D R D.dichotomy.η) (-convection)
              (cutoffForcingPath D R D.dichotomy.η) u) ∧
        D.dichotomy.P (u ⟨0, self_mem_Iic⟩) = (s * c₀) • D.dichotomy.e := by
  refine ⟨D.ancientThreshold, D.ancientAmplitude, D.ancientRadius, D.ancientAmplitude_pos,
    fun R hR s hs ↦ ?_⟩
  obtain ⟨u, ⟨hu, hfix⟩, huniq⟩ := existsUnique_ancientCorrection D R s hR hs
  exact ⟨u, ⟨hu, hfix, projection_terminal_of_fixedPoint D R hfix⟩,
    fun v ⟨hv, hvfix, _⟩ ↦ huniq v ⟨hv, hvfix⟩⟩

/-! ### The chosen ancient correction -/

/-- The ancient correction at cutoff radius `R` with unstable terminal coordinate `s c₀ e`: the
fixed point of `u = b (s c₀) + G (N u)` in the closed ball of radius `r`, unique above the
threshold radius for `s ∈ [0, 1]` (`existsUnique_ancientCorrection`), and zero when the ball
contains no fixed point. -/
def ancientCorrection : Iic (0 : ℝ) →ᵇ VectorH 3 3 := by
  classical
  exact if h : ∃ u : Iic (0 : ℝ) →ᵇ VectorH 3 3, ‖u‖ ≤ D.ancientRadius ∧
      u = D.dichotomy.b (s * D.ancientAmplitude) + D.ancientGreen (ancientForcing D R u)
    then h.choose else 0

variable {D R s}

/-- Above the threshold radius and for `s ∈ [0, 1]` the ancient correction lies in the ball of
radius `r` and solves the ancient fixed-point equation. -/
theorem ancientCorrection_spec (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖ancientCorrection D R s‖ ≤ D.ancientRadius ∧
      ancientCorrection D R s = D.dichotomy.b (s * D.ancientAmplitude) +
        D.ancientGreen (ancientForcing D R (ancientCorrection D R s)) := by
  have h := (existsUnique_ancientCorrection D R s hR hs).exists
  rw [ancientCorrection, dite_eq_left h]
  exact h.choose_spec

/-- Every fixed point in the ball of radius `r` is the ancient correction. -/
theorem eq_ancientCorrection (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {u : Iic (0 : ℝ) →ᵇ VectorH 3 3} (hu : ‖u‖ ≤ D.ancientRadius)
    (hfix : u = D.dichotomy.b (s * D.ancientAmplitude) + D.ancientGreen (ancientForcing D R u)) :
    u = ancientCorrection D R s :=
  (existsUnique_ancientCorrection D R s hR hs).unique ⟨hu, hfix⟩ (ancientCorrection_spec hR hs)

/-- The unstable terminal coordinate of the ancient correction is `s c₀ e`. -/
theorem projection_ancientCorrection_terminal (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    D.dichotomy.P (ancientCorrection D R s ⟨0, self_mem_Iic⟩) =
      (s * D.ancientAmplitude) • D.dichotomy.e :=
  projection_terminal_of_fixedPoint D R (ancientCorrection_spec hR hs).2

/-- Distinct parameters `s ∈ [0, 1]` give ancient corrections with distinct terminal values. -/
theorem injOn_ancientCorrection_terminal (hR : D.ancientThreshold ≤ R) :
    InjOn (fun s ↦ ancientCorrection D R s ⟨0, self_mem_Iic⟩) (Icc (0 : ℝ) 1) := by
  intro s hs s' hs' h
  have h' := congrArg D.dichotomy.P h
  simp only at h'
  rw [projection_ancientCorrection_terminal hR hs,
    projection_ancientCorrection_terminal hR hs'] at h'
  exact mul_right_cancel₀ D.ancientAmplitude_pos.ne'
    (smul_left_injective ℝ D.dichotomy.e_ne_zero h')

/-- In weight `η` the decoded ancient correction has size at most `r e^{ητ}`. -/
theorem norm_ancientLift_ancientCorrection_le (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) (τ : ℝ) :
    ‖ancientLift D.dichotomy.η (ancientCorrection D R s) τ‖ ≤
      D.ancientRadius * Real.exp (D.dichotomy.η * τ) :=
  (norm_ancientLift_le _ _ τ).trans
    (mul_le_mul_of_nonneg_right (ancientCorrection_spec hR hs).1 (Real.exp_nonneg _))

end NavierStokes.Nonuniqueness
