/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.OneDimensional.BoundaryLayer.Variable.Profile
public import PDE.Elliptic.OneDimensional.BoundaryLayer.Variable.Limits

/-!
# A variable-coefficient matched expansion from raw data

Let `L > 0` and `α > 0`, and let the drift `a` and the forcing `f` be `C¹` on an open set containing
`[0, L]`, with `a ≥ α` on `[0, L]`. For every `ε > 0`, `exists_expansion` gives a classical solution
of `εu″ + a(x)u′ = f(x)` with prescribed values at both endpoints, together with an outer solution
and error constants that do not depend on `ε` (`Expansion`). These estimates give uniform
convergence away from the left endpoint (`Expansion.outer_convergence`), uniform convergence of the
composite remainder (`Expansion.composite_convergence`), the inner limit at each fixed stretched
coordinate (`Expansion.inner_convergence`) and matching of the inner profile with the outer trace
(`Expansion.matching`).

This is a singular perturbation in the sense of Evans's §4.5.1, with constant positive diffusion and
variable drift on a finite interval. Evans's Example 1 in that subsection treats formally a
two-dimensional transport problem with small diffusion, (1)-(2); the subsection contains no
boundary-layer example.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.1 (Singular perturbations), Example 1 (Transport and
  small diffusion), (1)-(2) and (9), pp. 211-214.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section
open Filter Set
open scoped Topology
namespace PDE.Elliptic.BoundaryLayer.Variable

/-- A leading matched expansion records solutions, their exact homogeneous correction,
and error constants shared by every positive diffusion parameter. -/
structure Expansion (L α : ℝ) (a f : ℝ → ℝ) (A B : ℝ) where
  /-- The nondegenerate interval length. -/
  length_pos : 0 < L
  /-- The strictly positive lower drift bound. -/
  lower_pos : 0 < α
  /-- The drift remains positive throughout the closed interval. -/
  drift_lower : ∀ x ∈ Icc 0 L, α ≤ a x
  /-- The solution of the reduced equation with its right trace prescribed. -/
  outer : ℝ → ℝ
  /-- A classical solution for each positive diffusion parameter. -/
  solution : ℝ → ℝ → ℝ
  /-- The exact homogeneous correction with left value one and right value zero. -/
  correction : ℝ → ℝ → ℝ
  /-- An ε-independent coefficient in the exact-correction remainder estimate. -/
  errorConstant : ℝ
  /-- An ε-independent coefficient in the frozen-profile comparison. -/
  profileConstant : ℝ
  /-- The residual-bound constant is nonnegative. -/
  errorConstant_nonneg : 0 ≤ errorConstant
  /-- The profile-bound constant is nonnegative. -/
  profileConstant_nonneg : 0 ≤ profileConstant
  /-- The reduced solution is continuous, including at both endpoints. -/
  outer_continuous : Continuous outer
  /-- The reduced solution retains the prescribed right trace. -/
  outer_right : outer L = B
  /-- Integrating the original quotient determines the reduced solution on the interval. -/
  outer_formula : ∀ x ∈ Icc 0 L, outer x = B - ∫ t in x..L, f t / a t
  /-- The constructed solution has a global C² extension for positive ε. -/
  solution_contDiff : ∀ ε > 0, ContDiff ℝ 2 (solution ε)
  /-- The homogeneous correction also has a global C² extension. -/
  correction_contDiff : ∀ ε > 0, ContDiff ℝ 2 (correction ε)
  /-- The full solution satisfies the left boundary condition exactly. -/
  solution_left : ∀ ε > 0, solution ε 0 = A
  /-- The full solution satisfies the right boundary condition exactly. -/
  solution_right : ∀ ε > 0, solution ε L = B
  /-- The correction has unit left trace. -/
  correction_left : ∀ ε > 0, correction ε 0 = 1
  /-- The correction has zero right trace. -/
  correction_right : ∀ ε > 0, correction ε L = 0
  /-- The derivatives satisfy the forced equation on the closed interval. -/
  equation : ∀ ε > 0, ∀ x ∈ Icc 0 L,
    ε * deriv (deriv (solution ε)) x + a x * deriv (solution ε) x = f x
  /-- The derivatives of the correction satisfy the homogeneous equation. -/
  correction_equation : ∀ ε > 0, ∀ x ∈ Icc 0 L,
    ε * deriv (deriv (correction ε)) x + a x * deriv (correction ε) x = 0
  /-- The correction is nonnegative and exponentially localized at the left endpoint. -/
  localization : ∀ ε > 0, ∀ x ∈ Icc 0 L,
    0 ≤ correction ε x ∧ correction ε x ≤ Real.exp (-α * x / ε)
  /-- Removing the exact correction leaves a uniformly controlled zero-trace remainder. -/
  exact_error : ∀ ε > 0, ∀ x ∈ Icc 0 L,
    |solution ε x - outer x - (A - outer 0) * correction ε x| ≤
      ε * errorConstant * (L - x) / α
  /-- Away from the left boundary, the outer error consists of an exponential and an O(ε) term. -/
  outer_error : ∀ ε > 0, ∀ x ∈ Icc 0 L,
    |solution ε x - outer x| ≤ |A - outer 0| * Real.exp (-α * x / ε) +
      ε * errorConstant * (L - x) / α
  /-- Freezing the drift at the left boundary incurs an O(ε) profile error and an endpoint tail. -/
  profile_error : ∀ ε > 0, ∀ x ∈ Icc 0 L,
    |correction ε x - Real.exp (-a 0 * x / ε)| ≤
      profileConstant * ε * Real.exp (-(α / 2) * x / ε) + Real.exp (-a 0 * L / ε)

/-- Raw local C¹ coefficients produce a single family satisfying the equation, both traces,
and all exact, outer, and frozen-profile estimates with fixed constants. -/
theorem exists_expansion {L α : ℝ} (hL : 0 < L) (hα : 0 < α)
    {U : Set ℝ} (hU : IsOpen U) (hIU : Icc 0 L ⊆ U) (a f : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a U) (hf : ContDiffOn ℝ 1 f U)
    (hlower : ∀ x ∈ Icc 0 L, α ≤ a x) (A B : ℝ) :
    Nonempty (Expansion L α a f A B) := by
  classical
  obtain ⟨v, hv, hvL, hvformula, M, hM, hs⟩ :=
    raw_outer_approximation hL hα hU hIU a f ha hf hlower A B
  obtain ⟨K, hK, hvariation⟩ := drift_bound hL hU hIU a ha
  choose u H hu hH hu0 huL hH0 hHL hopu hopH hHb hexact houter using hs
  let us : ℝ → ℝ → ℝ := fun ε ↦ if hε : 0 < ε then u ε hε else fun _ ↦ 0
  let Hs : ℝ → ℝ → ℝ := fun ε ↦ if hε : 0 < ε then H ε hε else fun _ ↦ 0
  have hus (ε : ℝ) (hε : 0 < ε) : us ε = u ε hε := dite_eq_left hε
  have hHs (ε : ℝ) (hε : 0 < ε) : Hs ε = H ε hε := dite_eq_left hε
  have ha0 : 0 < a 0 := hα.trans_le (hlower 0 ⟨le_rfl, hL.le⟩)
  exact ⟨{
    length_pos := hL
    lower_pos := hα
    drift_lower := hlower
    outer := v
    solution := us
    correction := Hs
    errorConstant := M
    profileConstant := a 0 * K / (α / 2) ^ 3
    errorConstant_nonneg := hM
    profileConstant_nonneg := by positivity
    outer_continuous := hv
    outer_right := hvL
    outer_formula := hvformula
    solution_contDiff := fun ε hε ↦ hus ε hε ▸ hu ε hε
    correction_contDiff := fun ε hε ↦ hHs ε hε ▸ hH ε hε
    solution_left := fun ε hε ↦ hus ε hε ▸ hu0 ε hε
    solution_right := fun ε hε ↦ hus ε hε ▸ huL ε hε
    correction_left := fun ε hε ↦ hHs ε hε ▸ hH0 ε hε
    correction_right := fun ε hε ↦ hHs ε hε ▸ hHL ε hε
    equation := fun ε hε ↦ hus ε hε ▸ hopu ε hε
    correction_equation := fun ε hε ↦ hHs ε hε ▸ hopH ε hε
    localization := fun ε hε ↦ hHs ε hε ▸ hHb ε hε
    exact_error := fun ε hε ↦ hus ε hε ▸ hHs ε hε ▸ hexact ε hε
    outer_error := fun ε hε ↦ hus ε hε ▸ houter ε hε
    profile_error := fun ε hε ↦ hHs ε hε ▸ frozen_profile_error hL hε (half_pos hα) hK a (H ε hε)
      (fun x hx ↦ by linarith [hlower x hx]) hvariation (hH ε hε) (hH0 ε hε) (hHL ε hε)
      (fun x hx ↦ hopH ε hε x (Ioo_subset_Icc_self hx)) }⟩

namespace Expansion

variable {L α A B : ℝ} {a f : ℝ → ℝ} (E : Expansion L α a f A B)

/-- The composite error keeps the spatially decaying profile term and the endpoint tail. -/
theorem composite_error_with_tail {ε : ℝ} (hε : 0 < ε) :
    ∀ x ∈ Icc 0 L,
      |E.solution ε x - (E.outer x + (A - E.outer 0) * Real.exp (-a 0 * x / ε))| ≤
        ε * E.errorConstant * (L - x) / α +
          |A - E.outer 0| * (E.profileConstant * ε * Real.exp (-(α / 2) * x / ε) +
            Real.exp (-a 0 * L / ε)) :=
  composite_pointwise_bound (E.solution ε) E.outer (E.correction ε) (A - E.outer 0)
    (E.exact_error ε hε) (E.profile_error ε hε)

/-- The composite approximation is uniformly accurate with one explicit ε-independent constant. -/
theorem composite_error {ε : ℝ} (hε : 0 < ε) :
    ∀ x ∈ Icc 0 L,
      |E.solution ε x - (E.outer x + (A - E.outer 0) * Real.exp (-a 0 * x / ε))| ≤
        ε * (E.errorConstant * L / α + |A - E.outer 0| *
          (E.profileConstant + 1 / (a 0 * L))) :=
  composite_linear_bound E.length_pos hε E.lower_pos (half_pos E.lower_pos)
    (E.lower_pos.trans_le (E.drift_lower 0 ⟨le_rfl, E.length_pos.le⟩))
    E.errorConstant_nonneg E.profileConstant_nonneg (E.solution ε) E.outer (E.correction ε)
    (A - E.outer 0) (E.exact_error ε hε) (E.profile_error ε hε)

/-- Every compact interval separated from the left boundary has uniform outer convergence. -/
theorem outer_convergence {δ : ℝ} (hδ : 0 < δ) :
    TendstoUniformlyOn E.solution E.outer (𝓝[>] 0) (Icc δ L) :=
  outer_tendstoUniformlyOn E.lower_pos E.errorConstant_nonneg hδ
    E.solution E.outer (A - E.outer 0) E.outer_error

/-- When the outer solution already has the left trace, its convergence is uniform up to it. -/
theorem outer_convergence_of_match (hmatch : A = E.outer 0) :
    TendstoUniformlyOn E.solution E.outer (𝓝[>] 0) (Icc 0 L) := by
  apply outer_tendstoUniformlyOn_of_zero_mismatch E.lower_pos E.errorConstant_nonneg
    E.solution E.outer
  intro ε hε x hx
  simpa only [hmatch, sub_self, abs_zero, zero_mul, zero_add] using E.outer_error ε hε x hx

/-- A mismatch prevents uniform convergence of the outer approximation on the full interval. -/
theorem not_outer_convergence (hD : A - E.outer 0 ≠ 0) :
    ¬TendstoUniformlyOn E.solution E.outer (𝓝[>] 0) (Icc 0 L) :=
  not_outer_tendstoUniformlyOn E.length_pos.le E.solution E.outer E.solution_left hD

/-- Removing the exact homogeneous correction gives uniform convergence of its remainder. -/
theorem exact_remainder_convergence :
    TendstoUniformlyOn
      (fun ε x ↦ E.solution ε x - E.outer x - (A - E.outer 0) * E.correction ε x)
      (fun _ ↦ 0) (𝓝[>] 0) (Icc 0 L) := by
  apply outer_tendstoUniformlyOn_of_zero_mismatch E.lower_pos E.errorConstant_nonneg
  intro ε hε x hx
  simpa only [sub_zero] using E.exact_error ε hε x hx

/-- The composite remainder tends uniformly to zero, including at both boundaries. -/
theorem composite_convergence :
    TendstoUniformlyOn
      (fun ε x ↦ E.solution ε x - (E.outer x + (A - E.outer 0) * Real.exp (-a 0 * x / ε)))
      (fun _ ↦ 0) (𝓝[>] 0) (Icc 0 L) :=
  composite_tendstoUniformlyOn E.solution E.outer (A - E.outer 0)
    (fun _ hε ↦ E.composite_error hε)

/-- The constructed family has the physical inner limit at each fixed nonnegative coordinate. -/
theorem inner_convergence {y : ℝ} (hy : 0 ≤ y) :
    Tendsto (fun ε ↦ E.solution ε (ε * y)) (𝓝[>] 0)
      (𝓝 (E.outer 0 + (A - E.outer 0) * Real.exp (-a 0 * y))) :=
  stretched_tendsto E.length_pos E.solution E.outer E.outer_continuous (A - E.outer 0)
    (fun _ hε ↦ E.composite_error hε) hy

/-- The far end of the inner profile matches the outer trace. -/
theorem matching :
    Tendsto (fun y ↦ E.outer 0 + (A - E.outer 0) * Real.exp (-a 0 * y))
      atTop (𝓝 (E.outer 0)) :=
  inner_matching (E.lower_pos.trans_le (E.drift_lower 0 ⟨le_rfl, E.length_pos.le⟩))
    (E.outer 0) (A - E.outer 0)

/-- A nonzero mismatch forces different inner values at stretched coordinates zero and one. -/
theorem inner_nonconstant (hD : A - E.outer 0 ≠ 0) :
    E.outer 0 + (A - E.outer 0) * Real.exp (-a 0 * 0) ≠
      E.outer 0 + (A - E.outer 0) * Real.exp (-a 0 * 1) :=
  Variable.inner_nonconstant
    (E.lower_pos.trans_le (E.drift_lower 0 ⟨le_rfl, E.length_pos.le⟩)) hD (E.outer 0)

end Expansion
end PDE.Elliptic.BoundaryLayer.Variable
