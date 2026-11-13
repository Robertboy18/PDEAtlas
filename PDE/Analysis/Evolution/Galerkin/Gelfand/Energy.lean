/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PDE.Analysis.Evolution.Gelfand.Triple
public import Mathlib.Analysis.Calculus.Deriv.Basic
import PDE.Analysis.Evolution.Core.EnergyEstimate
import PDE.Analysis.Evolution.Core.EnergyIdentity
import PDE.Analysis.Evolution.Galerkin.Gelfand.Existence

/-!
# Gelfand Galerkin energy estimates

Let `u : [a, b] → S` be a differentiable trajectory in a trial space `S ⊆ V` with
`⟪ι u'(t), ι u(t)⟫_H + B(t)(u(t), u(t)) = ℓ(t)(u(t))`, where `C ‖w‖²_V ≤ B(t)(w, w)` with
`C > 0` and `‖ℓ(t)‖ ≤ M`. Differentiating the pivot energy and using Young's inequality gives

`½ ‖ι u(t)‖²_H + (C/2) ∫_a^t ‖u‖²_V ≤ ½ ‖ι u(a)‖²_H + M² (t - a) / (2C)`,

with constants independent of the trial space. The pointwise bound without the integral holds
under differentiability alone, and the integrated bound when `B` and `ℓ` are also continuous.
Both apply to the projected Galerkin equation and, since only the state test is used, to
equations whose skew nonlinear term cancels in that test.

These are steps 1-3 of the proof of the energy estimates of Evans, §7.1.2, Theorem 2, for
Galerkin approximations in a Gelfand triple. The tested equation is his (21), and `hcoercive`
is his (22) with `γ = 0`. Since the load is bounded in the dual of `V`, Young's inequality
absorbs it into the coercive term, and the bounds follow by integration, without the Grönwall
step (26). The bound on `u_m'` in step 4 of his proof is not part of these statements.

## Main results

* `gelfandGalerkin_energy_bound_of_test_state`, `gelfandGalerkin_energy_bound`: the pivot
  bound `½ ‖ι u(t)‖²_H ≤ ½ ‖ι u(a)‖²_H + M² (t - a) / (2C)`.
* `gelfandGalerkin_integrated_energy_bound_of_test_state`,
  `gelfandGalerkin_integrated_energy_bound`: the same with `(C/2) ∫_a^t ‖u‖²_V` added on the
  left, for continuous `B` and `ℓ`.
* `exists_gelfandGalerkin_nonauto_on_Icc_with_energy`: a Galerkin solution with a given
  initial value that satisfies both bounds.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 2 (Energy estimates) and steps 1-3 of
  its proof, (20)-(26), pp. 376-377. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section


open MeasureTheory Set

namespace PDE.Analysis.Evolution

open Function Filter
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Galerkin
section GelfandGalerkinMass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Pivot-energy bound from the equation tested against the state: if
`⟪ι u', ι u⟫_H + B(t)(u, u) = ℓ(t)(u)` on `[a, b]`, `C ‖w‖² ≤ B(t)(w, w)` and `‖ℓ(t)‖ ≤ M`,
then `½ ‖ι u(t)‖²_H ≤ ½ ‖ι u(a)‖²_H + M² (t - a) / (2C)`.
-/
theorem gelfandGalerkin_energy_bound_of_test_state
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) {a b : ℝ} (hab : a ≤ b)
    (ell : ℝ → StrongDual ℝ V) (u du : ℝ → S)
    {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hu : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt u (du t) (Set.Icc a b) t)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (hell : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (heq : ∀ t ∈ Set.Icc a b,
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (u t : V)) +
        B t (u t : V) (u t : V) = ell t (u t : V)) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖T.inclusion (u a : V)‖ ^ 2 +
          (M ^ 2 / (2 * C)) * (t - a) := by
  let E : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2
  have hmap (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivWithinAt (fun s ↦ T.inclusion (u s : V))
        (T.inclusion (du t : V)) (Set.Icc a b) t :=
    (T.inclusion.comp S.subtypeL).hasFDerivAt.comp_hasDerivWithinAt t (hu t ht)
  have hEderivWithin (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivWithinAt E
        (inner ℝ (T.inclusion (du t : V)) (T.inclusion (u t : V)))
        (Set.Icc a b) t :=
    hasDerivWithinAt_half_norm_sq (hmap t ht)
  have hEcont : ContinuousOn E (Set.Icc a b) := by
    intro t ht
    exact (hEderivWithin t ht).continuousWithinAt
  have hEdiff : DifferentiableOn ℝ E (interior (Set.Icc a b)) := by
    intro t ht
    exact ((hEderivWithin t (interior_subset ht)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)).differentiableAt.differentiableWithinAt
  have hEderivLe (t : ℝ) (ht : t ∈ interior (Set.Icc a b)) :
      deriv E t ≤ M ^ 2 / (2 * C) := by
    have htIcc := interior_subset ht
    have heqSelf := heq t htIcc
    have hellNorm : ell t (u t : V) ≤ ‖ell t‖ * ‖(u t : V)‖ :=
      (le_abs_self _).trans ((ell t).le_opNorm (u t : V))
    have hyoung := mul_le_sq_div_add_mul_sq_half hC ‖ell t‖ ‖(u t : V)‖
    have hsquare : ‖ell t‖ ^ 2 ≤ M ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hM).2 (hell t htIcc)
    rw [((hEderivWithin t htIcc).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)).deriv]
    have hdiv : ‖ell t‖ ^ 2 / (2 * C) ≤ M ^ 2 / (2 * C) :=
      div_le_div_of_nonneg_right hsquare (by positivity)
    nlinarith [hcoercive t htIcc (u t : V),
      mul_nonneg (le_of_lt hC) (sq_nonneg ‖(u t : V)‖)]
  intro t ht
  have hEa : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hmv := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    hEcont hEdiff hEderivLe a hEa t ht ht.1
  simpa [E, add_comm] using hmv

/-- The pivot-energy bound for a solution of the projected Galerkin equation. -/
theorem gelfandGalerkin_energy_bound
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) {a b : ℝ} (hab : a ≤ b)
    (ell : ℝ → StrongDual ℝ V) (u du : ℝ → S)
    {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hu : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt u (du t) (Set.Icc a b) t)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (hell : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (heq : ∀ t ∈ Set.Icc a b, ∀ v : S,
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
        B t (u t : V) (v : V) = ell t (v : V)) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖T.inclusion (u a : V)‖ ^ 2 +
          (M ^ 2 / (2 * C)) * (t - a) :=
  gelfandGalerkin_energy_bound_of_test_state
    T S B hab ell u du hC hM hu hcoercive hell
      (fun t ht ↦ heq t ht (u t))

/--
Integrated coercive bound from the equation tested against the state: under the hypotheses of
`gelfandGalerkin_energy_bound_of_test_state` with `B` and `ℓ` continuous,
`½ ‖ι u(t)‖²_H + (C/2) ∫_a^t ‖u‖²_V ≤ ½ ‖ι u(a)‖²_H + M² (t - a) / (2C)`.
-/
theorem gelfandGalerkin_integrated_energy_bound_of_test_state
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) {a b : ℝ}
    (ell : ℝ → StrongDual ℝ V) (u du : ℝ → S)
    {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hu : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt u (du t) (Set.Icc a b) t)
    (hB_cont : ContinuousOn B (Set.Icc a b))
    (hell_cont : ContinuousOn ell (Set.Icc a b))
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (hell : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (heq : ∀ t ∈ Set.Icc a b,
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (u t : V)) +
        B t (u t : V) (u t : V) = ell t (u t : V)) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 +
          (C / 2) * ∫ s in a..t, ‖(u s : V)‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖T.inclusion (u a : V)‖ ^ 2 +
          (M ^ 2 / (2 * C)) * (t - a) := by
  let E : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2
  let q : ℝ → ℝ := fun t ↦ ell t (u t : V) - B t (u t : V) (u t : V)
  let r : ℝ → ℝ := fun t ↦ ‖(u t : V)‖ ^ 2
  have hucontS : ContinuousOn u (Set.Icc a b) := by
    intro t ht
    exact (hu t ht).continuousWithinAt
  have hucont : ContinuousOn (fun t ↦ (u t : V)) (Set.Icc a b) :=
    S.subtypeL.continuous.comp_continuousOn hucontS
  have hqcont : ContinuousOn q (Set.Icc a b) := by
    exact (hell_cont.clm_apply hucont).sub
      ((hB_cont.clm_apply hucont).clm_apply hucont)
  have hrcont : ContinuousOn r (Set.Icc a b) :=
    hucont.norm.pow 2
  have hEderivWithin (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivWithinAt E (q t) (Set.Icc a b) t := by
    have hmap : HasDerivWithinAt (fun s ↦ T.inclusion (u s : V))
        (T.inclusion (du t : V)) (Set.Icc a b) t :=
      (T.inclusion.comp S.subtypeL).hasFDerivAt.comp_hasDerivWithinAt t (hu t ht)
    have henergy := hasDerivWithinAt_half_norm_sq hmap
    convert henergy using 1
    dsimp [q]
    linarith [heq t ht]
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc a b) :
      q t + (C / 2) * r t ≤ M ^ 2 / (2 * C) := by
    have hellNorm : ell t (u t : V) ≤ ‖ell t‖ * ‖(u t : V)‖ :=
      (le_abs_self _).trans ((ell t).le_opNorm (u t : V))
    have hyoung := mul_le_sq_div_add_mul_sq_half hC ‖ell t‖ ‖(u t : V)‖
    have hsquare : ‖ell t‖ ^ 2 ≤ M ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hM).2 (hell t ht)
    have hdiv : ‖ell t‖ ^ 2 / (2 * C) ≤ M ^ 2 / (2 * C) :=
      div_le_div_of_nonneg_right hsquare (by positivity)
    dsimp [q, r]
    nlinarith [hcoercive t ht (u t : V),
      mul_nonneg (le_of_lt hC) (sq_nonneg ‖(u t : V)‖)]
  intro t ht
  have hsub : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc_right ht.2
  have hqint : IntervalIntegrable q volume a t := by
    apply (hqcont.mono ?_).intervalIntegrable
    simpa [Set.uIcc_of_le ht.1] using hsub
  have hrint : IntervalIntegrable r volume a t := by
    apply (hrcont.mono ?_).intervalIntegrable
    simpa [Set.uIcc_of_le ht.1] using hsub
  have hsumint : IntervalIntegrable (fun s ↦ q s + (C / 2) * r s) volume a t :=
    hqint.add (hrint.const_mul _)
  have hconstint : IntervalIntegrable (fun _ : ℝ ↦ M ^ 2 / (2 * C)) volume a t :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on ht.1 hsumint hconstint
    (fun s hs ↦ hpoint s (hsub hs))
  have hFTC : (∫ s in a..t, q s) = E t - E a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    · intro s hs
      exact (hEderivWithin s (hsub hs)).continuousWithinAt.mono hsub
    · intro s hs
      have hsb : s < b := hs.2.trans_le ht.2
      exact (hEderivWithin s (hsub (Set.Ioo_subset_Icc_self hs))).hasDerivAt
        (Icc_mem_nhds hs.1 hsb)
    · exact hqint
  rw [intervalIntegral.integral_add hqint (hrint.const_mul _),
    intervalIntegral.integral_const_mul, hFTC, intervalIntegral.integral_const] at hmono
  dsimp [E] at hmono ⊢
  norm_num at hmono
  linarith

/-- The integrated coercive bound for a solution of the projected Galerkin equation. -/
theorem gelfandGalerkin_integrated_energy_bound
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) {a b : ℝ}
    (ell : ℝ → StrongDual ℝ V) (u du : ℝ → S)
    {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hu : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt u (du t) (Set.Icc a b) t)
    (hB_cont : ContinuousOn B (Set.Icc a b))
    (hell_cont : ContinuousOn ell (Set.Icc a b))
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (hell : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (heq : ∀ t ∈ Set.Icc a b, ∀ v : S,
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
        B t (u t : V) (v : V) = ell t (v : V)) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 +
          (C / 2) * ∫ s in a..t, ‖(u s : V)‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖T.inclusion (u a : V)‖ ^ 2 +
          (M ^ 2 / (2 * C)) * (t - a) :=
  gelfandGalerkin_integrated_energy_bound_of_test_state
    T S B ell u du hC hM hu hB_cont hell_cont hcoercive hell
      (fun t ht ↦ heq t ht (u t))

/--
Galerkin existence on `[a, b]` with the two energy estimates. If `B` and `ℓ` are continuous on
`[a, b]` with `‖B(t)‖ ≤ MB`, `‖ℓ(t)‖ ≤ Mell` and `C ‖w‖² ≤ B(t)(w, w)` for some `C > 0`, then
`exists_gelfandGalerkin_nonauto_on_Icc` gives a solution with initial value `u₀`, and it
satisfies the pivot-energy and integrated coercive bounds with constants `C` and `Mell`.
-/
theorem exists_gelfandGalerkin_nonauto_on_Icc_with_energy
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b)
    (hBcont : ContinuousOn B (Set.Icc a b))
    (hellcont : ContinuousOn ell (Set.Icc a b))
    (MB Mell : NNReal) {C : ℝ} (hC : 0 < C)
    (hBnorm : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hellnorm : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (u₀ : S) :
    ∃ u du : ℝ → S,
      u a = u₀ ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivWithinAt u (du t) (Set.Icc a b) t) ∧
      ContinuousOn du (Set.Icc a b) ∧
      (∀ t ∈ Set.Icc a b, ∀ v : S,
        inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
          B t (u t : V) (v : V) = ell t (v : V)) ∧
      (∀ t ∈ Set.Icc a b,
        (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
            ((Mell : ℝ) ^ 2 / (2 * C)) * (t - a)) ∧
      (∀ t ∈ Set.Icc a b,
        (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 +
            (C / 2) * ∫ s in a..t, ‖(u s : V)‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
            ((Mell : ℝ) ^ 2 / (2 * C)) * (t - a)) := by
  obtain ⟨u, du, hu₀, hdu, hducont, heq⟩ :=
    exists_gelfandGalerkin_nonauto_on_Icc T S B ell hab
      hBcont hellcont MB Mell hBnorm hellnorm u₀
  have henergy := gelfandGalerkin_energy_bound T S B hab ell u du hC Mell.2
    hdu hcoercive hellnorm heq
  have hintegrated := gelfandGalerkin_integrated_energy_bound
    T S B ell u du hC Mell.2 hdu hBcont hellcont hcoercive hellnorm heq
  refine ⟨u, du, hu₀, hdu, hducont, heq, ?_, ?_⟩
  · simpa [hu₀] using henergy
  · simpa [hu₀] using hintegrated

end GelfandGalerkinMass

end Galerkin

end PDE.Analysis.Evolution
