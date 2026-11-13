/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.FactoredOperator
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Weak maximum principle for variable coefficients

For `Lu = -∑ D²u[σₖ,σₖ] + Du[b] + cu` with `c ≥ 0`, a subsolution on an open set with compact
closure stays below every boundary upper bound `M` with `cM ≥ 0`
(`subsolution_le_of_boundary_le_of_nonneg_mul`). For `c = 0` this is Evans's §6.4.1, Theorem 1 (Weak
maximum principle), and for `M ≥ 0` it is his Theorem 2 (Weak maximum principle for `c ≥ 0`), (11).
The principal matrix is presented through its factors.

## Main results

* `subsolution_le_of_boundary_le_of_nonneg_mul`: the bound under the compatibility condition
  `cM ≥ 0`.
* `subsolution_le_of_boundary_le`: nonnegative potential and a nonnegative boundary bound.
* `le_of_operator_le_of_boundary_le`: comparison of two classical functions with ordered residuals
  and boundary values.
* `eqOn_of_operator_eq_of_boundary_eq`: uniqueness for the classical Dirichlet problem.

## How it works

Evans first treats `c = 0`, perturbing to `u + εe^{λx₁}`, and then reduces `c ≥ 0` to that case by
applying it to `Lu - cu` on the open set `{u > 0}`. We use one barrier for both. Given a continuous
linear functional `ℓ` with `∑ (ℓ σₖ)² ≥ α > 0` and `ℓ b ≤ B` throughout the domain, choosing
`μα > B` makes `exp (μℓ)` a strict subsolution of the principal-and-drift operator. Subtracting its
maximum over the closure gives a nonpositive barrier `q`, so the potential term `cq` is nonpositive
as well and `Lq < 0` without any upper bound on `c`. Then `u + εq` is a strict subsolution below `M`
on the boundary, `strict_subsolution_le_of_boundary_le` excludes an interior maximum above `M`, and
a small `ε` gives the claim.

## Implementation notes

The domain need only be open with compact closure; no boundary regularity is assumed. The
coefficients may vary with position without continuity. The one-direction lower bound is weaker than
uniform ellipticity and states exactly what this barrier uses; Evans's step 4 uses it for `ℓ = x₁`,
as `a¹¹ ≥ θ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.4.1, Theorem 1 (Weak maximum principle) and its proof,
  pp. 344-346, and Theorem 2 (Weak maximum principle for `c ≥ 0`), (11), and its proof, pp. 346-347.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace EllipticMaximum

open Set

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- Weak maximum principle with the more general compatibility condition `cM ≥ 0`.
In particular, a zero potential allows a boundary bound of either sign. -/
theorem subsolution_le_of_boundary_le_of_nonneg_mul
    {Ω : Set E} (hΩopen : IsOpen Ω) (hΩcompact : IsCompact (closure Ω))
    (σ : E → ι → E) (b : E → E) (c : E → ℝ)
    (ℓ : E →L[ℝ] ℝ) {α B : ℝ} (hαpos : 0 < α)
    (hprincipal : ∀ x ∈ Ω, α ≤ ∑ k, (ℓ (σ x k)) ^ 2)
    (hdrift : ∀ x ∈ Ω, ℓ (b x) ≤ B)
    {u : E → ℝ} {M : ℝ}
    (hc : ∀ x ∈ Ω, 0 ≤ c x) (hcM : ∀ x ∈ Ω, 0 ≤ c x * M)
    (hucont : ContinuousOn u (closure Ω))
    (hureg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ Ω, factoredOperator σ b c u x ≤ 0)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ M) :
    ∀ x ∈ closure Ω, u x ≤ M := by
  classical
  intro x hx
  by_contra hnot
  let μ : ℝ := (|B| + 1) / α
  have hμ : 0 < μ := div_pos (by positivity) hαpos
  have hμα : B < μ * α := by
    rw [div_mul_cancel₀ _ hαpos.ne']
    linarith [le_abs_self B]
  let e : E → ℝ := fun y ↦ Real.exp (μ * ℓ y)
  have he : ContDiff ℝ 2 e := by dsimp [e]; fun_prop
  obtain ⟨z, hz, hzmax⟩ :=
    hΩcompact.exists_isMaxOn ⟨x, hx⟩ he.continuous.continuousOn
  let C : ℝ := e z
  have hC : 0 < C := Real.exp_pos _
  let q : E → ℝ := fun y ↦ e y - C
  have hqreg : ContDiff ℝ 2 q := he.sub contDiff_const
  have hqnonpos : ∀ y ∈ closure Ω, q y ≤ 0 := fun y hy ↦ sub_nonpos.mpr (hzmax hy)
  have hqstrict : ∀ y ∈ Ω, factoredOperator σ b c q y < 0 := by
    intro y hy
    have hnegative : -(μ ^ 2 * ∑ k, (ℓ (σ y k)) ^ 2) + μ * ℓ (b y) < 0 := by
      nlinarith [mul_pos hμ (sub_pos.mpr hμα), mul_le_mul_of_nonneg_left (hprincipal y hy)
        (sq_nonneg μ), mul_le_mul_of_nonneg_left (hdrift y hy) hμ.le]
    have hformula : factoredOperator σ b c q y =
        e y * (-(μ ^ 2 * ∑ k, (ℓ (σ y k)) ^ 2) + μ * ℓ (b y)) + c y * q y := by
      rw [show q = (fun y ↦ e y - C) from rfl, factoredOperator_sub_const]
      dsimp [e]
      rw [factoredOperator_exp_clm]
      ring
    rw [hformula]
    exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (Real.exp_pos _) hnegative)
      (mul_nonpos_of_nonneg_of_nonpos (hc y hy) (hqnonpos y (subset_closure hy)))
  let d : ℝ := u x - M
  have hd : 0 < d := sub_pos.mpr (lt_of_not_ge hnot)
  let ε : ℝ := d / (2 * (C + 1))
  have hε : 0 < ε := div_pos hd (by positivity)
  let v : E → ℝ := fun y ↦ u y + ε * q y
  have hvcont : ContinuousOn v (closure Ω) :=
    hucont.add (hqreg.continuous.const_mul ε).continuousOn
  have hvreg : ∀ y ∈ Ω, ContDiffAt ℝ 2 v y := fun y hy ↦
    (hureg y hy).add (hqreg.contDiffAt.const_smul ε)
  have hvsub : ∀ y ∈ Ω, factoredOperator σ b c v y < 0 := by
    intro y hy
    have hqε : ContDiffAt ℝ 2 (fun z ↦ ε * q z) y := hqreg.contDiffAt.const_smul ε
    rw [show v = (fun y ↦ u y + ε * q y) from rfl,
      factoredOperator_add σ b c (hureg y hy) hqε,
      factoredOperator_const_mul σ b c (hqreg.differentiable (by norm_num) y)]
    exact add_neg_of_nonpos_of_neg (hsub y hy) (mul_neg_of_pos_of_neg hε (hqstrict y hy))
  have hvboundary : ∀ y ∈ frontier Ω, v y ≤ M := fun y hy ↦ (add_le_of_nonpos_right
    (mul_nonpos_of_nonneg_of_nonpos hε.le (hqnonpos y (frontier_subset_closure hy)))).trans
      (hboundary y hy)
  have hvle := strict_subsolution_le_of_boundary_le hΩopen hΩcompact σ b c hc hcM
    hvcont hvreg hvsub hvboundary x hx
  have hεeq : ε * (2 * (C + 1)) = d := div_mul_cancel₀ _ (by positivity)
  have hqbound : -C < q x := by
    dsimp [q]
    linarith [Real.exp_pos (μ * ℓ x)]
  have hεq : -ε * C < ε * q x := by nlinarith [mul_pos hε (sub_pos.mpr hqbound)]
  dsimp [v, d] at hvle hεeq
  nlinarith

/-- For nonnegative potential, a nonnegative boundary upper bound controls the whole closure.
The principal coefficient and drift satisfy the one-direction bounds stated above. -/
theorem subsolution_le_of_boundary_le
    {Ω : Set E} (hΩopen : IsOpen Ω) (hΩcompact : IsCompact (closure Ω))
    (σ : E → ι → E) (b : E → E) (c : E → ℝ)
    (ℓ : E →L[ℝ] ℝ) {α B : ℝ} (hαpos : 0 < α)
    (hprincipal : ∀ x ∈ Ω, α ≤ ∑ k, (ℓ (σ x k)) ^ 2)
    (hdrift : ∀ x ∈ Ω, ℓ (b x) ≤ B)
    {u : E → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ x ∈ Ω, 0 ≤ c x)
    (hucont : ContinuousOn u (closure Ω))
    (hureg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ Ω, factoredOperator σ b c u x ≤ 0)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ M) :
    ∀ x ∈ closure Ω, u x ≤ M :=
  subsolution_le_of_boundary_le_of_nonneg_mul hΩopen hΩcompact σ b c ℓ hαpos
    hprincipal hdrift hc (fun x hx ↦ mul_nonneg (hc x hx) hM)
    hucont hureg hsub hboundary

/-- Ordered operator values and boundary data order two classical functions throughout
the closure. This is the weak maximum principle applied to their difference. -/
theorem le_of_operator_le_of_boundary_le
    {Ω : Set E} (hΩopen : IsOpen Ω) (hΩcompact : IsCompact (closure Ω))
    (σ : E → ι → E) (b : E → E) (c : E → ℝ)
    (ℓ : E →L[ℝ] ℝ) {α B : ℝ} (hαpos : 0 < α)
    (hprincipal : ∀ x ∈ Ω, α ≤ ∑ k, (ℓ (σ x k)) ^ 2)
    (hdrift : ∀ x ∈ Ω, ℓ (b x) ≤ B)
    {u v : E → ℝ} (hc : ∀ x ∈ Ω, 0 ≤ c x)
    (hucont : ContinuousOn u (closure Ω)) (hvcont : ContinuousOn v (closure Ω))
    (hureg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hvreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 v x)
    (hoperator : ∀ x ∈ Ω, factoredOperator σ b c u x ≤ factoredOperator σ b c v x)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ v x) :
    ∀ x ∈ closure Ω, u x ≤ v x := by
  have hsub : ∀ x ∈ Ω, factoredOperator σ b c (fun y ↦ u y - v y) x ≤ 0 := by
    intro x hx
    rw [factoredOperator_sub σ b c (hureg x hx) (hvreg x hx)]
    exact sub_nonpos.mpr (hoperator x hx)
  have hbound := subsolution_le_of_boundary_le hΩopen hΩcompact σ b c ℓ hαpos
    hprincipal hdrift (M := 0) le_rfl hc (hucont.sub hvcont)
    (fun x hx ↦ (hureg x hx).sub (hvreg x hx)) hsub
    (fun x hx ↦ sub_nonpos.mpr (hboundary x hx))
  exact fun x hx ↦ sub_nonpos.mp (hbound x hx)

/-- Uniqueness for the classical Dirichlet problem under the coefficient bounds of the
weak maximum principle. Equal residuals and boundary values give equality on the closure. -/
theorem eqOn_of_operator_eq_of_boundary_eq
    {Ω : Set E} (hΩopen : IsOpen Ω) (hΩcompact : IsCompact (closure Ω))
    (σ : E → ι → E) (b : E → E) (c : E → ℝ)
    (ℓ : E →L[ℝ] ℝ) {α B : ℝ} (hαpos : 0 < α)
    (hprincipal : ∀ x ∈ Ω, α ≤ ∑ k, (ℓ (σ x k)) ^ 2)
    (hdrift : ∀ x ∈ Ω, ℓ (b x) ≤ B)
    {u v : E → ℝ} (hc : ∀ x ∈ Ω, 0 ≤ c x)
    (hucont : ContinuousOn u (closure Ω)) (hvcont : ContinuousOn v (closure Ω))
    (hureg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hvreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 v x)
    (hoperator : ∀ x ∈ Ω, factoredOperator σ b c u x = factoredOperator σ b c v x)
    (hboundary : EqOn u v (frontier Ω)) :
    EqOn u v (closure Ω) := by
  intro x hx
  exact le_antisymm
    (le_of_operator_le_of_boundary_le hΩopen hΩcompact σ b c ℓ hαpos hprincipal hdrift
      hc hucont hvcont hureg hvreg (fun y hy ↦ (hoperator y hy).le)
      (fun y hy ↦ (hboundary hy).le) x hx)
    (le_of_operator_le_of_boundary_le hΩopen hΩcompact σ b c ℓ hαpos hprincipal hdrift
      hc hvcont hucont hvreg hureg (fun y hy ↦ (hoperator y hy).ge)
      (fun y hy ↦ (hboundary hy).ge) x hx)

end EllipticMaximum
