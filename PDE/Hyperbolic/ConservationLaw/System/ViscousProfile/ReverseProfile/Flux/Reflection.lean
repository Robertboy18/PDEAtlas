/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.CoordinateReflection
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Switch.Monotonicity
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Concrete
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Feedback

import CAS.ExactTactic

/-!
# Reversal and central equilibria of the prescribed clock flux

The signed coordinate swap reverses the gated flux when the middle law is even.
The fast law, cutoff, feedback and signed gate need no parity assumptions. Including
linear speed damping changes the speed sign under reversal.

For the feedback thresholds of the retained linear reference clock, the central
axis has the exact equilibria `a = 0` and `a = 2000000 * μ` within `|a| ≤ 100`.
The fast law may have arbitrary parameter `δ`; its feedback thresholds stay fixed
at the reference clock.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.GatedFlux

/-- Swap the fast coordinates and negate the middle coordinate, using the
coordinate permutation and coordinate reflection isometries. -/
def reversal : ℝ^3 ≃ₗᵢ[ℝ] ℝ^3 :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 3) 2)).trans
    (PDE.Common.coordinateReflectionLinearIsometryEquiv 1)

/-- The signed coordinate swap acts by `(x, y, z) ↦ (z, -y, x)`. -/
@[simp]
theorem reversal_apply (q : ℝ^3) : reversal q = !₂[q 2, -q 1, q 0] := by
  have hswap : Equiv.swap (0 : Fin 3) 2 1 = 1 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  ext i
  fin_cases i <;> simp [reversal, PDE.Common.coordinateReflectionLinearIsometryEquiv,
      LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', hswap]

/-- Reversal of the same gated flux changes the speed sign. Only the middle law
is required to be even; in particular, the signed gate is unchanged. -/
theorem flux_sub_smul_reversal (k g C φ b : ℝ → ℝ) (hg : Function.Even g) (μ : ℝ) (q : ℝ^3) :
    flux k g C φ b (reversal q) - μ • reversal q = -reversal (flux k g C φ b q - (-μ) • q) := by
  simp only [reversal_apply]
  ext i
  fin_cases i
  · change -k (q 2) + b (-q 1) * q 0 - μ * q 2 = -(k (q 2) - b (-q 1) * q 0 - (-μ) * q 2)
    generalize k (q 2) = kz, b (-q 1) = bn, q 0 = x, q 2 = z
    cas
  · change (g (-q 1) + C (-(-q 1)) * φ (q 0) + C (-q 1) * φ (q 2)) - μ * (-q 1) =
      -(-(g (q 1) + C (-q 1) * φ (q 2) + C (q 1) * φ (q 0) - (-μ) * q 1))
    rw [hg (q 1)]
    simp only [neg_neg]
    generalize g (q 1) = gy, C (-q 1) = cn, C (q 1) = cp, φ (q 0) = px, φ (q 2) = pz, q 1 = y
    cas
  · change k (q 0) - b (-(-q 1)) * q 2 - μ * q 0 = -(-k (q 0) + b (q 1) * q 2 - (-μ) * q 0)
    simp only [neg_neg]
    generalize k (q 0) = kx, b (q 1) = bp, q 0 = x, q 2 = z
    cas

end PDE.Hyperbolic.ConservationLaw.System.GatedFlux

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

open PDE.Analysis

/-- The reference thresholds make the feedback vanish at zero. Hence the
central equilibria of the full speed-damped flux are exactly the two roots of its
quadratic middle law, within that law's central interval. The gate may
be signed, and the fast parameter does not change the retained thresholds. -/
theorem concreteGatedFlux_sub_smul_center_eq_zero_iff {Z : ℝ → ℝ} {T : ℝ}
    (hZ : ∀ t, HasDerivAt Z (2 * Z t) t) (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t) (hT : 0 ≤ T)
    (δ μ a : ℝ) (b : ℝ → ℝ) (ha : |a| ≤ 100) :
    concreteGatedFlux δ (clockFeedback (Z T) (Z (T + 1 / 2))) b !₂[0, a, 0] -
        μ • !₂[0, a, 0] = 0 ↔ a = 0 ∨ a = 2000000 * μ := by
  have hZfast : ∀ t, HasDerivAt Z (fastLogCosh 0 (Z t)) t := by
    intro t
    simpa only [fastLogCosh, zero_mul, add_zero] using hZ t
  have hZsq := ClockSwitch.strictMonoOn_fast_clock_sq (δ := 0)
    (by cas) hZfast hZlower
  have hstep : T < T + 1 / 2 := by cas
  have hAB : Z T ^ 2 < Z (T + 1 / 2) ^ 2 := hZsq hT (hT.trans hstep.le) hstep
  have hZT : 1 ≤ Z T := (le_add_of_nonneg_right hT).trans (hZlower T hT)
  have hA : 1 ≤ Z T ^ 2 := by
    calc
      1 = (1 : ℝ) ^ 2 := by cas
      _ ≤ Z T ^ 2 := pow_le_pow_left₀ zero_le_one hZT 2
  have hφzero : clockFeedback (Z T) (Z (T + 1 / 2)) 0 = 0 :=
    clockFeedback_eq_zero_of_abs_le_one hA hAB (by cas)
  simp only [one_div] at hφzero
  have hkzero : fastLogCosh δ 0 = 0 := by
    unfold fastLogCosh
    cas
  have hg := MiddleClock.g_of_abs_le ha
  have hfield : concreteGatedFlux δ (clockFeedback (Z T) (Z (T + 1 / 2))) b !₂[0, a, 0] -
          μ • !₂[0, a, 0] = !₂[0, (1 / 1000000 : ℝ) * a ^ 2 / 2 - μ * a, 0] := by
    ext i
    fin_cases i <;> simp [concreteGatedFlux, GatedFlux.flux, hkzero, hφzero, hg]
  have hfactor : (1 / 1000000 : ℝ) * a ^ 2 / 2 - μ * a =
      (1 / 2000000 : ℝ) * a * (a - 2000000 * μ) := by cas
  have hn : (1 / 2000000 : ℝ) ≠ 0 := by cas
  have hroots : (1 / 1000000 : ℝ) * a ^ 2 / 2 - μ * a = 0 ↔
      a = 0 ∨ a = 2000000 * μ := by
    rw [hfactor]
    simp only [mul_eq_zero, hn, false_or, sub_eq_zero]
  rw [hfield]
  constructor
  · exact fun h ↦ hroots.mp (congrArg (fun q : ℝ^3 ↦ q 1) h)
  · intro h
    have hm := hroots.mpr h
    ext i
    fin_cases i
    · rfl
    · exact hm
    · rfl

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
