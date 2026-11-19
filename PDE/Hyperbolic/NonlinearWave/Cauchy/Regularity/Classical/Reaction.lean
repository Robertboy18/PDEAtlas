/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Multiplication
import CAS.ExactTactic

/-!
# A smooth globally Lipschitz reaction on higher Sobolev spaces

The reaction `s / (1 + s²)` fixes zero, is smooth, and is globally 1-Lipschitz. These are the
hypotheses on the reaction in the wave theory for smooth globally Lipschitz reactions
(`PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General`), so that theory applies to
it.

Above the classical Sobolev threshold its composition operator has an explicit form: multiplication
by `1 + u²` is a bounded linear isomorphism of the higher Sobolev space (`higherResolventEquiv`),
with inverse the multiplication by `1 / (1 + u²)` that the weak chain rule constructs, and the
composition operator sends `u` to that inverse applied to `u`
(`higherComposition_saturatingReaction_eq_inverse`). Smoothness of the composition operator is
`contDiff_higherComposition` of `Classical.General.SmoothOperator` for this reaction.

The results hold in every positive spatial dimension.
-/

@[expose] public noncomputable section

open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- A smooth saturating reaction with bounded derivative. -/
def saturatingReaction (s : ℝ) : ℝ := s / (1 + s ^ 2)

/-- The reaction fixes the zero state. -/
theorem saturatingReaction_zero : saturatingReaction 0 = 0 := by
  simp [saturatingReaction]

/-- The reaction is smooth on the whole real line. -/
theorem contDiff_saturatingReaction : ContDiff ℝ (⊤ : ℕ∞) saturatingReaction :=
  contDiff_id.div (contDiff_const.add (contDiff_id.pow 2)) (fun s ↦ by positivity)

/-- Its exact scalar derivative is certified by the checked calculator. -/
theorem hasDerivAt_saturatingReaction (s : ℝ) :
    HasDerivAt saturatingReaction ((1 - s ^ 2) / (1 + s ^ 2) ^ 2) s := by
  have hden : 1 + s ^ 2 ≠ 0 := by positivity
  cas using hden

/-- The reaction is globally 1-Lipschitz, with no restriction on its argument. -/
theorem lipschitzWith_saturatingReaction : LipschitzWith 1 saturatingReaction := by
  apply lipschitzWith_of_nnNorm_deriv_le
    (fun s ↦ (hasDerivAt_saturatingReaction s).differentiableAt)
  intro s
  rw [(hasDerivAt_saturatingReaction s).deriv]
  change ‖(1 - s ^ 2) / (1 + s ^ 2) ^ 2‖ ≤ (1 : ℝ)
  have hd : 0 < (1 + s ^ 2) ^ 2 := sq_pos_of_pos (by positivity)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hd]
  apply (div_le_one hd).mpr
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (s ^ 2), sq_nonneg s]

/-- The decaying part of the reciprocal multiplier vanishes at zero. -/
def reciprocalDefect (s : ℝ) : ℝ := 1 / (1 + s ^ 2) - 1

/-- The reciprocal defect is smooth. -/
theorem contDiff_reciprocalDefect : ContDiff ℝ (⊤ : ℕ∞) reciprocalDefect :=
  (contDiff_const.div (contDiff_const.add (contDiff_id.pow 2))
    (fun s ↦ by positivity)).sub contDiff_const

/-- The reciprocal defect fixes zero, as required by the whole-space chain rule. -/
theorem reciprocalDefect_zero : reciprocalDefect 0 = 0 := by
  simp [reciprocalDefect]

variable {n k : ℕ} [NeZero n]

/-- Multiplication by `1 + u²` on the higher Sobolev space. -/
def higherResolventCLM (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (u : W^{k,2}(ℝ^n)) : W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) :=
  ContinuousLinearMap.id ℝ _ + higherProductCLM hk (higherProductCLM hk u u)

/-- Multiplication by the reciprocal of `1 + u²`. -/
def higherReciprocalCLM (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (u : W^{k,2}(ℝ^n)) : W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) :=
  ContinuousLinearMap.id ℝ _ +
    higherProductCLM hk (higherComposition hk contDiff_reciprocalDefect reciprocalDefect_zero u)

/-- The resolvent multiplier has its stated pointwise action. -/
theorem classicalRepresentative_higherResolventCLM
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (u v : W^{k,2}(ℝ^n)) (x : ℝ^n) :
    classicalRepresentativeCLM hk (higherResolventCLM hk u v) x =
      (1 + classicalRepresentativeCLM hk u x ^ 2) * classicalRepresentativeCLM hk v x := by
  simp only [higherResolventCLM, add_apply, ContinuousLinearMap.id_apply,
    map_add, add_apply, classicalRepresentative_higherProductCLM]
  ring

/-- The reciprocal multiplier has its stated pointwise action. -/
theorem classicalRepresentative_higherReciprocalCLM
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (u v : W^{k,2}(ℝ^n)) (x : ℝ^n) :
    classicalRepresentativeCLM hk (higherReciprocalCLM hk u v) x =
      classicalRepresentativeCLM hk v x / (1 + classicalRepresentativeCLM hk u x ^ 2) := by
  simp only [higherReciprocalCLM, add_apply, ContinuousLinearMap.id_apply,
    map_add, add_apply, classicalRepresentative_higherProductCLM,
    classicalRepresentative_higherComposition, reciprocalDefect]
  ring

/-- The positive multiplier is a bounded linear isomorphism on Hᵏ. -/
def higherResolventEquiv (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (u : W^{k,2}(ℝ^n)) : W^{k,2}(ℝ^n) ≃L[ℝ] W^{k,2}(ℝ^n) :=
  ContinuousLinearEquiv.equivOfInverse (higherResolventCLM hk u) (higherReciprocalCLM hk u)
    (by
      intro v
      apply classicalRepresentativeCLM_injective hk
      ext x
      rw [classicalRepresentative_higherReciprocalCLM,
        classicalRepresentative_higherResolventCLM, mul_div_cancel_left₀]
      positivity)
    (by
      intro v
      apply classicalRepresentativeCLM_injective hk
      ext x
      rw [classicalRepresentative_higherResolventCLM,
        classicalRepresentative_higherReciprocalCLM, mul_div_cancel₀]
      positivity)

/-- Higher composition is an operator inverse applied to the input. -/
theorem higherComposition_saturatingReaction_eq_inverse
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (u : W^{k,2}(ℝ^n)) :
    higherComposition hk contDiff_saturatingReaction saturatingReaction_zero u =
      (higherResolventCLM hk u).inverse u := by
  change _ = ((higherResolventEquiv hk u : _ ≃L[ℝ] _).toContinuousLinearMap).inverse u
  rw [ContinuousLinearMap.inverse_equiv]
  apply classicalRepresentativeCLM_injective hk
  ext x
  exact (classicalRepresentative_higherComposition hk contDiff_saturatingReaction
    saturatingReaction_zero u x).trans (classicalRepresentative_higherReciprocalCLM hk u u x).symm

end PDE.Hyperbolic.NonlinearWave.Cauchy
