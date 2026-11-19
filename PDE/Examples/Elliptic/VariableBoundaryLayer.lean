/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.OneDimensional.BoundaryLayer.Variable.Expansion
import CAS.ExactTactic

/-!
# Examples for the variable boundary-layer expansion

The problem is `ε u'' + a(x) u' = f(x)` on `[0, L]` with `u 0 = A`, `u L = B` and a
positive drift `a`. For constant coefficients every `Expansion` solution is the explicit
solution `solution ε b L A B f` (`constant_solution`), and the corrector differs from
`exp(-b x/ε)` by at most `exp(-b L/ε)` (`constant_profile_tail`). For the drift
`a(x) = 1 + x` on `[0, 1]`, the forcing `f = a` gives an exact decomposition
(`matching_forcing`), and `f = 1` gives a composite error at most `ε (1 - x)`
(`constant_forcing`). When the outer solution matches the left boundary value, the
solutions converge uniformly to it (`zero_mismatch_expansion`).
-/

@[expose] public section

noncomputable section
open Filter Set
open scoped Topology
namespace PDE.Examples.BoundaryLayer
open PDE.Elliptic.BoundaryLayer
open PDE.Elliptic.BoundaryLayer.Variable

/-- For constant drift `b` and forcing `f`, the expansion solution equals the explicit
solution `solution ε b L A B f`. -/
theorem constant_solution {L b A B f ε : ℝ}
    (E : Expansion L b (fun _ ↦ b) (fun _ ↦ f) A B) (hε : 0 < ε) :
    EqOn (E.solution ε) (solution ε b L A B f) (Icc 0 L) := by
  have hs : ContDiff ℝ 2 (solution ε b L A B f) :=
    (solution_contDiff ε b L A B f).of_le (by norm_num)
  exact scalar_uniqueness E.length_pos hε (fun _ ↦ b) (fun _ _ ↦ E.lower_pos.le)
    (E.solution_contDiff ε hε).continuous.continuousOn hs.continuous.continuousOn
    (fun _ _ ↦ (E.solution_contDiff ε hε).contDiffAt) (fun _ _ ↦ hs.contDiffAt)
    (fun x hx ↦ (E.equation ε hε x (Ioo_subset_Icc_self hx)).trans
      (solution_equation hε E.lower_pos E.length_pos A B f x).symm)
    ((E.solution_left ε hε).trans (solution_zero hε E.lower_pos E.length_pos A B f).symm)
    ((E.solution_right ε hε).trans (solution_right ε b L A B f).symm)

/-- For constant coefficients an expansion exists, and its solution is the explicit one for
every `ε > 0`. -/
theorem constant_expansion {L b : ℝ} (hL : 0 < L) (hb : 0 < b) (A B f : ℝ) :
    ∃ E : Expansion L b (fun _ ↦ b) (fun _ ↦ f) A B,
      ∀ ε > 0, EqOn (E.solution ε) (solution ε b L A B f) (Icc 0 L) := by
  obtain ⟨E⟩ := exists_expansion hL hb (U := univ) isOpen_univ (subset_univ _)
    (fun _ ↦ b) (fun _ ↦ f) contDiffOn_const contDiffOn_const (fun _ _ ↦ le_rfl) A B
  exact ⟨E, fun _ hε ↦ constant_solution E hε⟩

/-- For constant drift the corrector differs from `exp(-b x/ε)` by at most `exp(-b L/ε)`,
with no `O(ε)` term. -/
theorem constant_profile_tail {L b A B f ε : ℝ}
    (E : Expansion L b (fun _ ↦ b) (fun _ ↦ f) A B) (hε : 0 < ε) :
    ∀ x ∈ Icc 0 L,
      |E.correction ε x - Real.exp (-b * x / ε)| ≤ Real.exp (-b * L / ε) := by
  have h := frozen_profile_error E.length_pos hε (half_pos E.lower_pos)
    (show (0 : ℝ) ≤ 0 from le_rfl) (fun _ ↦ b) (E.correction ε)
    (fun _ _ ↦ by linarith) (fun _ _ ↦ by simp)
    (E.correction_contDiff ε hε) (E.correction_left ε hε) (E.correction_right ε hε)
    (fun x hx ↦ E.correction_equation ε hε x (Ioo_subset_Icc_self hx))
  simpa only [mul_zero, zero_div, zero_mul, zero_add] using h

/-- For `a = f = 1 + x` on `[0, 1]`, the solution is exactly `B + x - 1 + (A - (B - 1)) H`,
with `H` the boundary layer. -/
theorem matching_forcing {ε : ℝ} (hε : 0 < ε) (A B : ℝ) :
    ∃ u H : ℝ → ℝ, ContDiff ℝ 2 u ∧ ContDiff ℝ 2 H ∧
      u 0 = A ∧ u 1 = B ∧ H 0 = 1 ∧ H 1 = 0 ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        ε * deriv (deriv u) x + (1 + x) * deriv u x = 1 + x) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, ε * deriv (deriv H) x + (1 + x) * deriv H x = 0) ∧
      ∀ x ∈ Icc (0 : ℝ) 1, u x = B + x - 1 + (A - (B - 1)) * H x := by
  have hL : (0 : ℝ) < 1 := by norm_num
  obtain ⟨u, hu, hu0, huL, hopu⟩ := exists_solution_continuousOn hL hε
    (fun x ↦ 1 + x) (fun x ↦ 1 + x) (by fun_prop) (by fun_prop) A B
  obtain ⟨H, hH, hH0, hHL, hopH, _⟩ := exists_localized_layer hL hε hL
    (fun x ↦ 1 + x) (by fun_prop) (fun x hx ↦ by linarith [hx.1])
  let v : ℝ → ℝ := fun x ↦ B + x - 1
  have hv : ContDiff ℝ 2 v := by dsimp [v]; fun_prop
  have hvd (x : ℝ) : HasDerivAt v 1 x := by dsimp [v]; cas
  have hvdeq : deriv v = fun _ ↦ 1 := funext fun x ↦ (hvd x).deriv
  have he := composite_error hL hε hL (show (0 : ℝ) ≤ 0 from le_rfl)
    (fun x ↦ 1 + x) (fun x ↦ 1 + x) (fun _ ↦ 1) u v H A B
    (fun x hx ↦ by linarith [hx.1]) hu hv.continuous.continuousOn hv.contDiffOn hH
    hu0 huL (by simp [v]) hH0 hHL
    (fun x hx ↦ hopu x (Ioo_subset_Icc_self hx))
    (fun x hx ↦ hopH x (Ioo_subset_Icc_self hx))
    (fun x _ ↦ by rw [(hvd x).deriv, mul_one])
    (fun x _ ↦ by rw [hvdeq]) (fun _ _ ↦ by simp)
  refine ⟨u, H, hu, hH, hu0, huL, hH0, hHL, hopu, hopH, fun x hx ↦ ?_⟩
  have hzero : u x - v x - (A - v 0) * H x = 0 :=
    abs_nonpos_iff.mp (by simpa only [mul_zero, zero_mul, zero_div] using he x hx)
  dsimp [v] at hzero
  linarith

/-- For `a = 1 + x` and `f = 1` on `[0, 1]`, the composite expansion with outer solution
`B - ∫ₓ¹ 1/(1 + t) dt` has error at most `ε (1 - x)`. -/
theorem constant_forcing {ε : ℝ} (hε : 0 < ε) (A B : ℝ) :
    ∃ u H v : ℝ → ℝ, ContDiff ℝ 2 u ∧ ContDiff ℝ 2 H ∧ Continuous v ∧
      u 0 = A ∧ u 1 = B ∧ H 0 = 1 ∧ H 1 = 0 ∧ v 1 = B ∧
      (∀ x ∈ Icc (0 : ℝ) 1, v x = B - ∫ t in x..1, 1 / (1 + t)) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, ε * deriv (deriv u) x + (1 + x) * deriv u x = 1) ∧
      ∀ x ∈ Icc (0 : ℝ) 1,
        |u x - v x - (A - v 0) * H x| ≤ ε * (1 - x) := by
  have hL : (0 : ℝ) < 1 := by norm_num
  let q : ℝ → ℝ := fun x ↦ 1 / (1 + x)
  have hq : ContDiffOn ℝ 1 q (Ioi (-1)) :=
    contDiffOn_const.div (contDiffOn_const.add contDiffOn_id)
      (fun x hx ↦ ne_of_gt (by linarith [show -1 < x from hx]))
  obtain ⟨v, hv, hv₂, hvL, hvformula, hvfirst, hvsecond⟩ :=
    exists_outer hL (V := Ioi (-1))
      (fun x hx ↦ by change -1 < x; linarith [hx.1]) q hq B
  obtain ⟨u, hu, hu0, huL, hopu⟩ := exists_solution_continuousOn hL hε
    (fun x ↦ 1 + x) (fun _ ↦ 1) (by fun_prop) continuousOn_const A B
  obtain ⟨H, hH, hH0, hHL, hopH, _⟩ := exists_localized_layer hL hε hL
    (fun x ↦ 1 + x) (by fun_prop) (fun x hx ↦ by linarith [hx.1])
  have hqbound (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : |deriv q x| ≤ 1 := by
    have hpos : 0 < 1 + x := by linarith [hx.1]
    have hd : HasDerivAt q (-1 / (1 + x) ^ 2) x := by
      dsimp [q]
      cas using hpos.ne'
    rw [hd.deriv, abs_div, abs_neg, abs_one, abs_of_nonneg (sq_nonneg _)]
    apply (div_le_one (sq_pos_of_pos hpos)).mpr
    nlinarith [hx.1]
  have he := composite_error hL hε hL (show (0 : ℝ) ≤ 1 from hL.le)
    (fun x ↦ 1 + x) (fun _ ↦ 1) q u v H A B
    (fun x hx ↦ by linarith [hx.1]) hu hv.continuousOn hv₂ hH hu0 huL hvL hH0 hHL
    (fun x hx ↦ hopu x (Ioo_subset_Icc_self hx))
    (fun x hx ↦ hopH x (Ioo_subset_Icc_self hx))
    (fun x hx ↦ by
      rw [hvfirst x hx]
      dsimp [q]
      have hpos : 0 < 1 + x := by linarith [hx.1]
      cas using hpos.ne') hvsecond hqbound
  refine ⟨u, H, v, hu, hH, hv, hu0, huL, hH0, hHL, hvL, hvformula, hopu, ?_⟩
  intro x hx
  simpa only [mul_one, div_one] using he x hx

/-- For `a = f = 1 + x` and `A = B - 1`, the outer solution matches the left boundary value,
and the solutions converge uniformly to it on `[0, 1]` as `ε → 0⁺`. -/
theorem zero_mismatch_expansion (B : ℝ) :
    ∃ E : Expansion 1 1 (fun x ↦ 1 + x) (fun x ↦ 1 + x) (B - 1) B,
      E.outer 0 = B - 1 ∧
      TendstoUniformlyOn E.solution E.outer (𝓝[>] 0) (Icc 0 1) := by
  obtain ⟨E⟩ := exists_expansion (L := 1) (α := 1) (by norm_num) (by norm_num) (U := univ)
    isOpen_univ (subset_univ _) (fun x ↦ 1 + x) (fun x ↦ 1 + x)
    (by fun_prop) (by fun_prop) (fun x hx ↦ by linarith [hx.1]) (B - 1) B
  have hint : (∫ t in (0 : ℝ)..1, (1 + t) / (1 + t)) = 1 := by
    calc
      _ = ∫ _ in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        exact div_self (ne_of_gt (by linarith [hx.1]))
      _ = 1 := by simp
  have hmatch : E.outer 0 = B - 1 := by
    rw [E.outer_formula 0 ⟨le_rfl, by norm_num⟩, hint]
  exact ⟨E, hmatch, E.outer_convergence_of_match hmatch.symm⟩

end PDE.Examples.BoundaryLayer
