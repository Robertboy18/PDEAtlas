/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixSymmetrization

/-!
# Strict positivity for classical matrix operators

Let `Lf = -∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼf + Df[b] + cf` on an open connected domain. Under uniform
quadratic ellipticity and continuity of the principal trace and drift, a nonnegative
classical supersolution which is positive somewhere is positive everywhere, provided
the potential is bounded above.

Replacing the potential by a nonnegative constant upper bound preserves the supersolution
inequality. At a hypothetical zero, `-f` attains its maximum zero; the strong maximum principle,
here in the form of Evans's §6.4.2, Theorem 4, then makes `f` identically zero. The zero-potential
eigenfunction statement is a specialization with potential `-λ`.

No symmetry, boundary condition, or continuity of the individual principal entries or
potential is required. The results prove positivity of a given classical function.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.4.2, Theorem 4 (Strong maximum principle with `c ≥ 0`),
  pp. 350-351.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace EllipticMaximum

open Set Metric

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A nonnegative classical supersolution with bounded-above potential, positive
somewhere on a connected open domain, is positive throughout that domain. -/
theorem pos_of_nonneg_of_matrix_supersolution
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n)
    (htrace : ContinuousOn (fun x ↦ ∑ i : Fin n, a x i i) Ω)
    (hb : ContinuousOn b Ω) {alpha : ℝ} (halpha : 0 < alpha)
    (helliptic : ∀ x ∈ Ω, ∀ v : ℝ^n,
      alpha * ‖v‖ ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, a x i j * v i * v j)
    (c : ℝ^n → ℝ) {C : ℝ} (hc : ∀ x ∈ Ω, c x ≤ C)
    {f : ℝ^n → ℝ}
    (hreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 f x)
    (hsuper : ∀ x ∈ Ω, 0 ≤ matrixOperator a b c f x)
    (hnonneg : ∀ x ∈ Ω, 0 ≤ f x) (hpositive : ∃ y ∈ Ω, 0 < f y) :
    ∀ x ∈ Ω, 0 < f x := by
  let D : ℝ := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hcD (x : ℝ^n) (hx : x ∈ Ω) : c x ≤ D :=
    (hc x hx).trans (le_max_left _ _)
  have hlocal := matrix_local_bounds_of_continuous_trace_drift
    hΩ a b htrace hb halpha helliptic D hD
  have hsub : ∀ y ∈ Ω, matrixOperator a b (fun _ ↦ D) (fun z ↦ -f z) y ≤ 0 := by
    intro y hy
    have hzero : matrixOperator a b (fun _ ↦ D) (fun _ ↦ 0) y = 0 :=
      (matrixOperator_const a b (fun _ ↦ D) 0 y).trans (mul_zero _)
    have hpotential : matrixOperator a b (fun _ ↦ D) f y =
        matrixOperator a b c f y + (D - c y) * f y := by
      simp only [matrixOperator_apply]
      ring
    have hnegative : matrixOperator a b (fun _ ↦ D) (fun z ↦ -f z) y =
        -(matrixOperator a b c f y + (D - c y) * f y) := by
      have h := matrixOperator_sub a b (fun _ ↦ D)
        (u := fun _ ↦ 0) (v := f) (x := y) contDiffAt_const (hreg y hy)
      simp only [zero_sub] at h
      rw [h, hzero, hpotential, zero_sub]
    rw [hnegative]
    exact neg_nonpos.mpr
      (add_nonneg (hsuper y hy) (mul_nonneg (sub_nonneg.mpr (hcD y hy)) (hnonneg y hy)))
  intro x hx
  by_contra hnot
  have hzero : f x = 0 := le_antisymm (le_of_not_gt hnot) (hnonneg x hx)
  have hmax : IsMaxOn (fun y ↦ -f y) Ω x := by
    intro y hy
    change -f y ≤ -f x
    rw [hzero, neg_zero]
    exact neg_nonpos.mpr (hnonneg y hy)
  have hconstant := matrix_eqOn_const_of_isPreconnected_of_isMaxOn_of_elliptic
    hΩ hconn a b (fun _ ↦ D) hlocal (fun y hy ↦ (hreg y hy).neg) hsub hx hmax
    (fun _ _ ↦ by simp only [hzero, neg_zero, mul_zero, le_refl])
  obtain ⟨y, hy, hfy⟩ := hpositive
  have hsame := hconstant hy
  change -f y = -f x at hsame
  linarith

/-- A classical matrix eigenfunction that is nonnegative on an open connected domain and
positive at one point is positive throughout the domain. Assume uniform quadratic ellipticity,
continuity of the principal trace, and continuity of the drift. The principal matrix need not
be symmetric, and the eigenvalue may be any real number. -/
theorem pos_of_nonneg_of_matrix_eigenfunction
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n)
    (htrace : ContinuousOn (fun x ↦ ∑ i : Fin n, a x i i) Ω)
    (hb : ContinuousOn b Ω) {alpha : ℝ} (halpha : 0 < alpha)
    (helliptic : ∀ x ∈ Ω, ∀ v : ℝ^n,
      alpha * ‖v‖ ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, a x i j * v i * v j)
    {lambda : ℝ} {f : ℝ^n → ℝ}
    (hreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 f x)
    (heq : ∀ x ∈ Ω, matrixOperator a b (fun _ ↦ 0) f x = lambda * f x)
    (hnonneg : ∀ x ∈ Ω, 0 ≤ f x) (hpositive : ∃ y ∈ Ω, 0 < f y) :
    ∀ x ∈ Ω, 0 < f x := by
  apply pos_of_nonneg_of_matrix_supersolution hΩ hconn a b htrace hb halpha helliptic
    (fun _ ↦ -lambda) (fun _ _ ↦ le_rfl) hreg ?_ hnonneg hpositive
  intro x hx
  have hshift : matrixOperator a b (fun _ ↦ -lambda) f x =
      matrixOperator a b (fun _ ↦ 0) f x - lambda * f x := by
    simp only [matrixOperator_apply]
    ring
  rw [hshift, heq x hx, sub_self]

end EllipticMaximum
