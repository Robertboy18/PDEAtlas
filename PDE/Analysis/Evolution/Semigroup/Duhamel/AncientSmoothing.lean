/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Ancient Duhamel integrals with a loss of derivatives

A kernel from a forcing space to a stronger solution space may have the singular
bound `M * r ^ (-α) * exp (ω * r)`. If `α < 1` and the forcing decays backwards
with rate `β > ω`, its past integral converges and has an explicit Gamma-function
bound. No value or continuity of the kernel at zero is required.

The majorant `r ^ (-α) * exp (-(β - ω) * r)` has the exact mass
`smoothingMass α (β - ω) = Γ(1 - α) / (β - ω) ^ (1 - α)` (`integral_smoothingWeight`), which
is `√π / √(β - ω)` for `α = 1/2`. A forcing bounded by `D * exp (β * s)` gives the past integral
at time `t` the bound `M * D * exp (β * t)` times this mass (`norm_ancientDuhamel_le`). Measured
in a weight `η ≤ β` at times `t ≤ a`, the factor `exp ((β - η) * a)` appears
(`norm_weighted_ancientDuhamel_le`), so a weight gap makes the integral small on an early
enough half-line.

The two Banach spaces allow a smoothing semigroup to recover derivatives lost by
the nonlinearity. The estimates include the half-derivative kernel used in the
ancient evolution argument of Hou--Wang--Yang, Section 2.2, equations (2.17)--(2.18).
They do not construct the smoothing semigroup or its spectral decomposition.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

/-- The integrable singular exponential majorant in the time-lag variable. -/
def smoothingWeight (α gap r : ℝ) : ℝ := r ^ (-α) * Real.exp (-(gap * r))

/-- The mass of the majorant, expressed in terms of the Gamma function. -/
def smoothingMass (α gap : ℝ) : ℝ :=
  (1 / gap) ^ (1 - α) * Real.Gamma (1 - α)

/-- The convolution constant is nonnegative in the integrable range. -/
theorem smoothingMass_nonneg {α gap : ℝ} (hα : α < 1) (hgap : 0 < gap) :
    0 ≤ smoothingMass α gap := by
  unfold smoothingMass
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.Gamma_pos_of_pos (by linarith)).le

/-- At order one half the mass is `√π / √gap`. -/
theorem smoothingMass_one_half (gap : ℝ) :
    smoothingMass (1 / 2) gap = Real.sqrt Real.pi / Real.sqrt gap := by
  unfold smoothingMass
  rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sqrt_div zero_le_one, Real.sqrt_one, Real.Gamma_one_half_eq]
  ring

/-- A singularity of order less than one is integrable against exponential decay. -/
theorem integrableOn_smoothingWeight {α gap : ℝ} (hα : α < 1) (hgap : 0 < gap) :
    IntegrableOn (smoothingWeight α gap) (Ioi 0) := by
  change IntegrableOn (fun r : ℝ ↦ r ^ (-α) * Real.exp (-(gap * r))) (Ioi 0)
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < -α)
      zero_lt_one hgap)

/-- The exact convolution constant, including its dependence on the spectral gap. -/
theorem integral_smoothingWeight {α gap : ℝ} (hα : α < 1) (hgap : 0 < gap) :
    (∫ r in Ioi (0 : ℝ), smoothingWeight α gap r) = smoothingMass α gap := by
  have hpower : (1 - α) - 1 = -α := by ring
  simpa only [smoothingWeight, smoothingMass, hpower] using
    (Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < 1 - α) hgap)

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The past Duhamel integral, written with positive lag `r = t - s`.
The kernel need not act on the same space in which the forcing takes values. -/
def ancientDuhamel (K : ℝ → F →L[ℝ] E) (f : ℝ → F) (t : ℝ) : E :=
  ∫ r in Ioi (0 : ℝ), K r (f (t - r))

/-- The integrand at positive lag is dominated by the Gamma majorant. -/
theorem norm_ancientIntegrand_le
    {K : ℝ → F →L[ℝ] E} {f : ℝ → F} {α ω β M D t r : ℝ}
    (hM : 0 ≤ M)
    (hK : ‖K r‖ ≤ M * r ^ (-α) * Real.exp (ω * r))
    (hr : 0 < r) (hf : ‖f (t - r)‖ ≤ D * Real.exp (β * (t - r))) :
    ‖K r (f (t - r))‖ ≤
      (M * D * Real.exp (β * t)) * smoothingWeight α (β - ω) r := by
  calc
    ‖K r (f (t - r))‖ ≤ ‖K r‖ * ‖f (t - r)‖ := (K r).le_opNorm _
    _ ≤ (M * r ^ (-α) * Real.exp (ω * r)) *
        (D * Real.exp (β * (t - r))) :=
      mul_le_mul hK hf (norm_nonneg _) (by positivity)
    _ = (M * D * Real.exp (β * t)) * smoothingWeight α (β - ω) r := by
      unfold smoothingWeight
      have hexp : Real.exp (ω * r) * Real.exp (β * (t - r)) =
          Real.exp (β * t) * Real.exp (-((β - ω) * r)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (M * D * r ^ (-α)) *
            (Real.exp (ω * r) * Real.exp (β * (t - r))) := by ring
        _ = _ := by rw [hexp]; ring

/-- A backwards exponential forcing bound makes the ancient integral a genuine
Bochner integral despite the short-time loss of derivatives. -/
theorem integrableOn_ancientIntegrand
    {K : ℝ → F →L[ℝ] E} {f : ℝ → F} {α ω β M D t : ℝ}
    (hα : α < 1) (hgap : ω < β) (hM : 0 ≤ M)
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-α) * Real.exp (ω * r))
    (hf : ∀ s, s ≤ t → ‖f s‖ ≤ D * Real.exp (β * s))
    (hmeas : AEStronglyMeasurable (fun r ↦ K r (f (t - r)))
      (volume.restrict (Ioi 0))) :
    IntegrableOn (fun r ↦ K r (f (t - r))) (Ioi 0) := by
  refine ((integrableOn_smoothingWeight hα (sub_pos.mpr hgap)).const_mul
    (M * D * Real.exp (β * t))).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact norm_ancientIntegrand_le hM (hK r hr) hr
    (hf (t - r) (sub_le_self t (le_of_lt hr)))

/-- The ancient Duhamel integral preserves the forcing's exponential weight with
constant `M * Γ(1 - α) / (β - ω)^(1 - α)`. -/
theorem norm_ancientDuhamel_le
    {K : ℝ → F →L[ℝ] E} {f : ℝ → F} {α ω β M D t : ℝ}
    (hα : α < 1) (hgap : ω < β) (hM : 0 ≤ M)
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-α) * Real.exp (ω * r))
    (hf : ∀ s, s ≤ t → ‖f s‖ ≤ D * Real.exp (β * s)) :
    ‖ancientDuhamel K f t‖ ≤
      (M * D * Real.exp (β * t)) * smoothingMass α (β - ω) := by
  unfold ancientDuhamel
  have hi := (integrableOn_smoothingWeight hα (sub_pos.mpr hgap)).const_mul
    (M * D * Real.exp (β * t))
  have hbound : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      ‖K r (f (t - r))‖ ≤
        (M * D * Real.exp (β * t)) * smoothingWeight α (β - ω) r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact norm_ancientIntegrand_le hM (hK r hr) hr
      (hf (t - r) (sub_le_self t (le_of_lt hr)))
  convert norm_integral_le_of_norm_le hi hbound using 1
  rw [integral_const_mul, integral_smoothingWeight hα (sub_pos.mpr hgap)]

/-- The same weighted bound applies to differences; the two forcings must be
integrable individually so that subtraction commutes with the Bochner integral. -/
theorem norm_ancientDuhamel_sub_le
    {K : ℝ → F →L[ℝ] E} {f g : ℝ → F} {α ω β M D t : ℝ}
    (hα : α < 1) (hgap : ω < β) (hM : 0 ≤ M)
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-α) * Real.exp (ω * r))
    (hf : IntegrableOn (fun r ↦ K r (f (t - r))) (Ioi 0))
    (hg : IntegrableOn (fun r ↦ K r (g (t - r))) (Ioi 0))
    (hfg : ∀ s, s ≤ t → ‖f s - g s‖ ≤ D * Real.exp (β * s)) :
    ‖ancientDuhamel K f t - ancientDuhamel K g t‖ ≤
      (M * D * Real.exp (β * t)) * smoothingMass α (β - ω) := by
  have heq : ancientDuhamel K f t - ancientDuhamel K g t =
      ancientDuhamel K (fun s ↦ f s - g s) t := by
    simp only [ancientDuhamel, map_sub, integral_sub hf hg]
  rw [heq]
  exact norm_ancientDuhamel_le hα hgap hM hK hfg

/-- Extra forcing decay gives a small operator bound on a sufficiently early
past half-line. This is the weight gain used to control quadratic nonlinearities. -/
theorem norm_weighted_ancientDuhamel_le
    {K : ℝ → F →L[ℝ] E} {f : ℝ → F} {α ω β η M D t a : ℝ}
    (hα : α < 1) (hgap : ω < β) (hweight : η ≤ β)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (ht : t ≤ a)
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-α) * Real.exp (ω * r))
    (hf : ∀ s, s ≤ t → ‖f s‖ ≤ D * Real.exp (β * s)) :
    ‖Real.exp (-(η * t)) • ancientDuhamel K f t‖ ≤
      (M * smoothingMass α (β - ω) * Real.exp ((β - η) * a)) * D := by
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
  calc
    _ ≤ Real.exp (-(η * t)) *
        ((M * D * Real.exp (β * t)) * smoothingMass α (β - ω)) :=
      mul_le_mul_of_nonneg_left (norm_ancientDuhamel_le hα hgap hM hK hf)
        (Real.exp_nonneg _)
    _ = (M * smoothingMass α (β - ω) * Real.exp ((β - η) * t)) * D := by
      have hexp : Real.exp (-(η * t)) * Real.exp (β * t) =
          Real.exp ((β - η) * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (M * smoothingMass α (β - ω) * D) *
            (Real.exp (-(η * t)) * Real.exp (β * t)) := by ring
        _ = _ := by rw [hexp]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hD
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg hM (smoothingMass_nonneg hα (sub_pos.mpr hgap)))
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr hweight))

/-- A map annihilating the kernel at positive lag annihilates its convergent past
integral. -/
theorem map_ancientDuhamel_eq_zero [CompleteSpace E]
    (P : E →L[ℝ] E) {K : ℝ → F →L[ℝ] E} {f : ℝ → F} {t : ℝ}
    (hi : IntegrableOn (fun r ↦ K r (f (t - r))) (Ioi 0))
    (hP : ∀ r, 0 < r → ∀ x, P (K r x) = 0) :
    P (ancientDuhamel K f t) = 0 := by
  rw [ancientDuhamel, ← P.integral_comp_comm hi]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact hP r hr _

end PDE.Analysis.Evolution
