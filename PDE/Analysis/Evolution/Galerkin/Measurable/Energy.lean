/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import PDE.Analysis.Evolution.Gelfand.Triple
import Mathlib.MeasureTheory.Function.L2Space
import PDE.Analysis.Evolution.Core.EnergyEstimate
import PDE.Analysis.Evolution.LionsMagenes.Basic.EnergyIdentity
import PDE.Analysis.MeasureTheory.Lp.Continuous
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Energy estimate for measurable Galerkin trajectories

Let `u : [a, b] → S` be absolutely continuous with a square-integrable derivative and satisfy
the projected equation `⟪ι u', ι v⟫_H + B(t)(u, v) = ℓ(t)(v)` almost everywhere. If
`C ‖w‖² ≤ B(t)(w, w)` with `C > 0`, then

`½ ‖ι u(b)‖²_H + (C/2) ∫_a^b ‖u‖²_V ≤ ½ ‖ι u(a)‖²_H + (1/(2C)) ∫_a^b ‖ℓ‖²_{V*}`,

and with `‖ℓ(t)‖ ≤ M` the same holds on every `[a, t]` with `M² (t - a) / (2C)` on the right.
Under a Gårding inequality `θ ‖w‖² ≤ B(t)(w, w) + γ ‖ι w‖²` an extra term
`γ ∫ ‖ι u‖²_H` appears. The proof uses the energy identity for absolutely continuous
Hilbert-valued curves.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 2 (energy estimates) and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open AbsolutelyContinuousOnInterval Filter Function MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution

section GalerkinCaratheodory

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Integrating a differential energy inequality for an absolutely continuous
curve retains the terminal energy. The derivative is only required almost
everywhere, and both dissipation and forcing are integrable. -/
private theorem integrated_energy_inequality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : E →L[ℝ] H) {u du : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (huAC : AbsolutelyContinuousOnInterval u a b)
    (hdu : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (du t) t)
    (hduMem : MemLp du 2 (volume.restrict (Ioc a b)))
    {d f : ℝ → ℝ}
    (hd : Integrable d (volume.restrict (Ioc a b)))
    (hf : Integrable f (volume.restrict (Ioc a b)))
    (hpoint : ∀ᵐ t ∂volume.restrict (Ioc a b),
      inner ℝ (J (du t)) (J (u t)) + d t ≤ f t) :
    (1 / 2 : ℝ) * ‖J (u b)‖ ^ 2 + ∫ t in Ioc a b, d t ≤
      (1 / 2 : ℝ) * ‖J (u a)‖ ^ 2 + ∫ t in Ioc a b, f t := by
  have huCont : ContinuousOn u (Icc a b) := by
    simpa only [uIcc_of_le hab] using huAC.continuousOn
  have huJMem : MemLp (fun t ↦ J (u t)) 2 (volume.restrict (Ioc a b)) :=
    (J.continuous.comp_continuousOn huCont).memLp_of_subset_isCompact
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  have hduJMem : MemLp (fun t ↦ J (du t)) 2 (volume.restrict (Ioc a b)) :=
    J.comp_memLp' hduMem
  have hinnerInt : Integrable (fun t ↦ inner ℝ (J (du t)) (J (u t)))
      (volume.restrict (Ioc a b)) := by
    apply (L2.integrable_inner (𝕜 := ℝ)
      (hduJMem.toLp _) (huJMem.toLp _)).congr
    filter_upwards [hduJMem.coeFn_toLp, huJMem.coeFn_toLp] with t hduJ huJ
    rw [hduJ, huJ]
  have hduGlobal : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (fun s ↦ J (u s)) (J (du t)) t := by
    have hduVolume := (ae_restrict_iff' measurableSet_Ioc).1 hdu
    have hneA : ∀ᵐ t ∂volume, t ≠ a := by
      apply MeasureTheory.ae_iff.2
      simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
        (measure_singleton a : volume ({a} : Set ℝ) = 0)
    filter_upwards [hduVolume, hneA] with t ht hta htUIcc
    have htIcc : t ∈ Icc a b := by
      simpa only [uIcc_of_le hab] using htUIcc
    exact J.hasFDerivAt.comp_hasDerivAt t
      (ht ⟨lt_of_le_of_ne htIcc.1 (Ne.symm hta), htIcc.2⟩)
  have huJAC : AbsolutelyContinuousOnInterval (fun t ↦ J (u t)) a b := by
    simpa only [Function.comp_def] using
      J.lipschitzWith.comp_absolutelyContinuousOnInterval huAC
  have henergy := absolutelyContinuous_energy_identity huJAC hduGlobal
  rw [intervalIntegral.integral_of_le hab, integral_const_mul] at henergy
  have hint := integral_mono_ae (hinnerInt.add hd) hf hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_add hinnerInt hd] at hint
  linarith

omit [CompleteSpace V] [CompleteSpace H] in
/-- Gårding energy inequality with `L²` forcing: if `θ ‖w‖² ≤ B(t)(w, w) + γ ‖ι w‖²` with
`θ > 0` and the projected equation hold almost everywhere, then
`½ ‖ι u(b)‖² + (θ/2) ∫ ‖u‖²_V ≤ ½ ‖ι u(a)‖² + (1/(2θ)) ∫ ‖ℓ‖² + γ ∫ ‖ι u‖²_H`. -/
theorem gelfandGalerkin_garding_energy_bound_of_forcing_memLp
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    (u du : ℝ → S) {a b theta gamma : ℝ} (hab : a ≤ b) (htheta : 0 < theta)
    (huAC : AbsolutelyContinuousOnInterval u a b)
    (hdu : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (du t) t)
    (hduMem : MemLp du 2 (volume.restrict (Ioc a b)))
    (hGarding : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ w : V,
      theta * ‖w‖ ^ 2 ≤ B t w w + gamma * ‖T.inclusion w‖ ^ 2)
    (hell : MemLp ell 2 (volume.restrict (Ioc a b)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : S,
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
        B t (u t : V) (v : V) = ell t (v : V)) :
    (1 / 2 : ℝ) * ‖T.inclusion (u b : V)‖ ^ 2 +
        (theta / 2) * ∫ t in Ioc a b, ‖(u t : V)‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖T.inclusion (u a : V)‖ ^ 2 +
        (1 / (2 * theta)) * (∫ t in Ioc a b, ‖ell t‖ ^ 2) +
        gamma * (∫ t in Ioc a b, ‖T.inclusion (u t : V)‖ ^ 2) := by
  let J : S →L[ℝ] H := T.inclusion.comp S.subtypeL
  have huCont : ContinuousOn u (Icc a b) := by
    simpa only [uIcc_of_le hab] using huAC.continuousOn
  have huMem : MemLp (fun t ↦ (u t : V)) 2 (volume.restrict (Ioc a b)) :=
    (S.subtypeL.continuous.comp_continuousOn huCont).memLp_of_subset_isCompact
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  have hJMem : MemLp (fun t ↦ J (u t)) 2 (volume.restrict (Ioc a b)) :=
    (J.continuous.comp_continuousOn huCont).memLp_of_subset_isCompact
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioc a b),
      inner ℝ (J (du t)) (J (u t)) + (theta / 2) * ‖(u t : V)‖ ^ 2 ≤
        ‖ell t‖ ^ 2 / (2 * theta) + gamma * ‖J (u t)‖ ^ 2 := by
    filter_upwards [heq, hGarding] with t hEq hGt
    have hellNorm : ell t (u t : V) ≤ ‖ell t‖ * ‖(u t : V)‖ :=
      (le_abs_self _).trans ((ell t).le_opNorm (u t : V))
    have hyoung := mul_le_sq_div_add_mul_sq_half htheta ‖ell t‖ ‖(u t : V)‖
    change inner ℝ (T.inclusion (du t : V)) (T.inclusion (u t : V)) +
      (theta / 2) * ‖(u t : V)‖ ^ 2 ≤
        ‖ell t‖ ^ 2 / (2 * theta) + gamma * ‖T.inclusion (u t : V)‖ ^ 2
    nlinarith [hEq (u t), hGt (u t : V)]
  have hforcing := (hell.integrable_norm_pow (by norm_num)).div_const (2 * theta)
  have hpivot := (hJMem.integrable_norm_pow (by norm_num)).const_mul gamma
  have hbound := integrated_energy_inequality J hab huAC hdu hduMem
    ((huMem.integrable_norm_pow (by norm_num)).const_mul (theta / 2))
    (hforcing.add hpivot) hpoint
  simp only [Pi.add_apply] at hbound
  rw [integral_const_mul, integral_add hforcing hpivot, integral_div,
    integral_const_mul] at hbound
  simpa only [J, ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL,
    Submodule.subtype_apply, one_div, div_eq_mul_inv, mul_comm _ (2 * theta)⁻¹,
    one_mul, mul_one, add_assoc] using hbound

omit [CompleteSpace V] [CompleteSpace H] in
/-- Coercive energy inequality with `L²` forcing, the case `γ = 0` of the Gårding bound:
`½ ‖ι u(b)‖² + (C/2) ∫ ‖u‖²_V ≤ ½ ‖ι u(a)‖² + (1/(2C)) ∫ ‖ℓ‖²`. -/
theorem gelfandGalerkin_integrated_energy_bound_of_forcing_memLp
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    (u du : ℝ → S) {a b C : ℝ} (hab : a ≤ b) (hC : 0 < C)
    (huAC : AbsolutelyContinuousOnInterval u a b)
    (hdu : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (du t) t)
    (hduMem : MemLp du 2 (volume.restrict (Ioc a b)))
    (hcoercive : ∀ t ∈ Icc a b, ∀ w : V, C * ‖w‖ ^ 2 ≤ B t w w)
    (hell : MemLp ell 2 (volume.restrict (Ioc a b)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : S,
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
        B t (u t : V) (v : V) = ell t (v : V)) :
    (1 / 2 : ℝ) * ‖T.inclusion (u b : V)‖ ^ 2 +
        (C / 2) * ∫ t in Ioc a b, ‖(u t : V)‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖T.inclusion (u a : V)‖ ^ 2 +
        (1 / (2 * C)) * ∫ t in Ioc a b, ‖ell t‖ ^ 2 := by
  have hGarding : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w + 0 * ‖T.inclusion w‖ ^ 2 :=
    (ae_restrict_mem measurableSet_Ioc).mono fun t ht w ↦ by
      simpa only [zero_mul, add_zero] using hcoercive t (Ioc_subset_Icc_self ht) w
  simpa only [zero_mul, add_zero] using
    gelfandGalerkin_garding_energy_bound_of_forcing_memLp T S B ell u du hab hC huAC hdu
      hduMem hGarding hell heq

omit [CompleteSpace V] [CompleteSpace H] in
/--
Integrated energy estimate (Evans §7.1.2, Theorem 2) for an absolutely continuous Galerkin
trajectory whose
derivative and projected equation hold almost everywhere: if `‖ℓ(t)‖ ≤ M`, then
`½ ‖ι u(t)‖² + (C/2) ∫_a^t ‖u‖²_V ≤ ½ ‖ι u(a)‖² + M² (t - a) / (2C)` on `[a, b]`. This is
the almost-everywhere counterpart of `gelfandGalerkin_integrated_energy_bound`.
-/
theorem gelfandGalerkin_integrated_energy_bound_ae
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    (u du : ℝ → S) {a b C M : ℝ}
    (hab : a ≤ b) (hC : 0 < C) (hM : 0 ≤ M)
    (huAC : AbsolutelyContinuousOnInterval u a b)
    (hdu : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      HasDerivAt u (du t) t)
    (hduMem : MemLp du 2 (volume.restrict (Set.Ioc a b)))
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (hell : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (heq : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ∀ v : S,
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
        B t (u t : V) (v : V) = ell t (v : V)) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 +
          (C / 2) * ∫ s in a..t, ‖(u s : V)‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖T.inclusion (u a : V)‖ ^ 2 +
          (M ^ 2 / (2 * C)) * (t - a) := by
  intro t ht
  let J : S →L[ℝ] H := T.inclusion.comp S.subtypeL
  have hsub : Ioc a t ⊆ Ioc a b := fun s hs ↦ ⟨hs.1, hs.2.trans ht.2⟩
  have hmeasure := (volume : Measure ℝ).restrict_mono_set hsub
  have huACAt : AbsolutelyContinuousOnInterval u a t :=
    huAC.mono (uIcc_subset_uIcc_left (by simpa only [uIcc_of_le hab] using ht))
  have huCont : ContinuousOn u (Icc a t) := by
    simpa only [uIcc_of_le ht.1] using huACAt.continuousOn
  have huMem : MemLp (fun s ↦ (u s : V)) 2 (volume.restrict (Ioc a t)) :=
    (S.subtypeL.continuous.comp_continuousOn huCont).memLp_of_subset_isCompact
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  have hpoint : ∀ᵐ s ∂volume.restrict (Ioc a t),
      inner ℝ (J (du s)) (J (u s)) + (C / 2) * ‖(u s : V)‖ ^ 2 ≤
        M ^ 2 / (2 * C) := by
    filter_upwards [heq.filter_mono (ae_mono hmeasure), ae_restrict_mem measurableSet_Ioc]
      with s hEq hs
    have hsIcc := Ioc_subset_Icc_self (hsub hs)
    have hellNorm : ell s (u s : V) ≤ ‖ell s‖ * ‖(u s : V)‖ :=
      (le_abs_self _).trans ((ell s).le_opNorm (u s : V))
    have hyoung := mul_le_sq_div_add_mul_sq_half hC ‖ell s‖ ‖(u s : V)‖
    have hsquare : ‖ell s‖ ^ 2 ≤ M ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hM).2 (hell s hsIcc)
    have hdiv := div_le_div_of_nonneg_right hsquare (by positivity : 0 ≤ 2 * C)
    change inner ℝ (T.inclusion (du s : V)) (T.inclusion (u s : V)) +
      (C / 2) * ‖(u s : V)‖ ^ 2 ≤ M ^ 2 / (2 * C)
    nlinarith [hEq (u s), hcoercive s hsIcc (u s : V)]
  have hbound := integrated_energy_inequality J ht.1 huACAt
    (hdu.filter_mono (ae_mono hmeasure)) (hduMem.mono_measure hmeasure)
    ((huMem.integrable_norm_pow (by norm_num)).const_mul (C / 2))
    (integrable_const (M ^ 2 / (2 * C))) hpoint
  rw [integral_const_mul, ← intervalIntegral.integral_of_le ht.1,
    ← intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_const] at hbound
  simpa only [J, ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL,
    Submodule.subtype_apply, smul_eq_mul, mul_comm (t - a)] using hbound

end GalerkinCaratheodory

end PDE.Analysis.Evolution
