/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.DirichletNemytskii
import PDE.Elliptic.Semilinear.Monotonicity

/-!
# Monotonicity for semilinear Dirichlet equations

We specialize the abstract monotone-operator estimates to
semilinear Dirichlet equations on `H¹₀(Ω)`. Pointwise monotonicity or
semimonotonicity of a represented Nemytskii map yields a priori bounds,
continuous dependence on the forcing, zero-forcing rigidity, and uniqueness.

The direct-method existence theorem is in `VariationalDirichlet`; the
results here give quantitative stability and uniqueness under weaker
one-sided assumptions that need not come from a convex potential.

## Main results

* `dirichletNemytskii_pairing_nonneg_of_monotone`,
  `neg_mul_norm_sq_le_dirichletNemytskii_pairing_of_semimonotone`: pointwise
  monotonicity of `g(x, ·)`, or semimonotonicity with loss `L`, transfers to
  the represented Nemytskii operator in the `L²` pairing.
* `norm_le_forcing_norm_div_of_nonneg`,
  `eq_zero_of_dirichlet_semilinear_of_nonneg`: a priori bound and
  zero-forcing rigidity under the sign condition `g(x, s) s ≥ 0`.
* `norm_sub_le_forcing_sub_norm_div_of_monotone`,
  `norm_sub_le_forcing_sub_norm_div_of_semimonotone`: Lipschitz dependence on
  the forcing with constants `1/c` and `1/(c - L)`, where `c` is the given
  coercivity modulus of the Dirichlet form.
* `eq_of_dirichlet_semilinear_of_monotone`,
  `eq_of_dirichlet_semilinear_of_semimonotone`: uniqueness.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.1 (monotonicity methods).
  <https://doi.org/10.1090/gsm/019>
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Universitext, Springer, 2011, Chapter 5 (Hilbert Spaces), pp. 131-156.
  <https://doi.org/10.1007/978-0-387-70914-7_5>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A pointwise sign condition on `g(x,s) * s` makes the represented
Nemytskii load pair nonnegatively with its argument. -/
theorem dirichletNemytskii_self_pairing_nonneg
    (g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (hgsign : ∀ᵐ x ∂domainMeasure n Ω, ∀ s, 0 ≤ g x s * s)
    (u : H¹₀(Ω)) :
    0 ≤ loadFunctional (n := n) (Ω := Ω) (N u) u := by
  rw [dirichletNemytskii_pairing_eq_integral
    (n := n) (Ω := Ω) g N hNrep u u]
  apply integral_nonneg_of_ae
  filter_upwards [hgsign] with x hx
  exact hx _

private theorem dirichletNemytskii_sub_ae_eq
    (g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (u w : H¹₀(Ω)) :
    (((N u - N w : DerivLp n 2 Ω) : ℝ^n → ℝ)) =ᵐ[
        domainMeasure n Ω]
      fun x ↦
        g x
            ((baseCoordCLM (n := n) (Ω := Ω) u :
                ℝ^n → ℝ) x) -
          g x
            ((baseCoordCLM (n := n) (Ω := Ω) w :
                ℝ^n → ℝ) x) := by
  filter_upwards [Lp.coeFn_sub (N u) (N w), hNrep u, hNrep w] with x hxsub hxu hxw
  rw [hxsub, Pi.sub_apply, hxu, hxw]

private theorem baseCoord_sub_ae_eq
    (u w : H¹₀(Ω)) :
    ((baseCoordCLM (n := n) (Ω := Ω) (u - w) :
        DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦
        (baseCoordCLM (n := n) (Ω := Ω) u :
            ℝ^n → ℝ) x -
          (baseCoordCLM (n := n) (Ω := Ω) w :
            ℝ^n → ℝ) x := by
  rw [map_sub]
  exact MeasureTheory.Lp.coeFn_sub _ _

private theorem mul_sub_nonneg_of_monotone
    (f : ℝ → ℝ) (hf : Monotone f) (a b : ℝ) :
    0 ≤ (a - b) * (f a - f b) := by
  simpa [mul_comm] using
    (hf.monovary monotone_id).sub_mul_sub_nonneg b a

/-- Pointwise monotonicity of `g(x,·)` makes its represented Nemytskii
operator monotone in the `L²` pairing. -/
theorem dirichletNemytskii_pairing_nonneg_of_monotone
    (g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (hgmono : ∀ᵐ x ∂domainMeasure n Ω, Monotone (g x))
    (u w : H¹₀(Ω)) :
    0 ≤ loadFunctional (n := n) (Ω := Ω) (N u - N w) (u - w) := by
  rw [loadFunctional_apply, MeasureTheory.L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hgmono, dirichletNemytskii_sub_ae_eq g N hNrep u w, baseCoord_sub_ae_eq u w]
    with x hxmono hxN hxP
  rw [hxN, hxP]
  exact mul_sub_nonneg_of_monotone (g x) hxmono _ _

/-- If `s ↦ g(x,s) + Ls` is monotone almost everywhere and `L ≥ 0`, then
the represented Nemytskii load can lose at most
`L * ‖u - w‖_{H¹₀}²` in its pairing with `u - w`.

The pointwise hypothesis first gives the sharper `L²` lower bound. The
contraction estimate for the base-coordinate map then converts it to the
`H¹₀` norm used by the coercive Dirichlet form. -/
theorem neg_mul_norm_sq_le_dirichletNemytskii_pairing_of_semimonotone
    (g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (L : ℝ) (hL : 0 ≤ L)
    (hgsemimonotone : ∀ᵐ x ∂domainMeasure n Ω,
      Monotone fun s ↦ g x s + L * s)
    (u w : H¹₀(Ω)) :
    -L * ‖u - w‖ * ‖u - w‖ ≤
      loadFunctional (n := n) (Ω := Ω) (N u - N w) (u - w) := by
  set P := baseCoordCLM (n := n) (Ω := Ω)
  have hMrep (z : H¹₀(Ω)) : ((N z + L • P z : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ g x ((P z : ℝ^n → ℝ) x) + L * (P z : ℝ^n → ℝ) x := by
    filter_upwards [Lp.coeFn_add (N z) (L • P z), hNrep z, Lp.coeFn_smul L (P z)] with
      x hxadd hxN hxsmul
    rw [hxadd, Pi.add_apply, hxN, hxsmul, Pi.smul_apply, smul_eq_mul]
  have h := dirichletNemytskii_pairing_nonneg_of_monotone (fun x s ↦ g x s + L * s)
    (fun z ↦ N z + L • P z) hMrep hgsemimonotone u w
  rw [show N u + L • P u - (N w + L • P w) = (N u - N w) + L • P (u - w) by
    rw [map_sub, smul_sub]; abel, loadFunctional_add, add_apply, loadFunctional_apply (L • _)] at h
  change 0 ≤ _ + inner ℝ (L • P (u - w)) (P (u - w)) at h
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at h
  nlinarith [mul_le_mul_of_nonneg_left (mul_self_le_mul_self (norm_nonneg _)
    (baseCoordCLM_norm_le (n := n) (Ω := Ω) (u - w))) hL]

/-- A semilinear Dirichlet solution is bounded by its `L²` forcing when the
nonlinear term has nonnegative pointwise pairing with the solution. -/
theorem norm_le_forcing_norm_div_of_nonneg
    (g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (hgsign : ∀ᵐ x ∂domainMeasure n Ω, ∀ s, 0 ≤ g x s * s)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ z : H¹₀(Ω),
      c * ‖z‖ * ‖z‖ ≤
        dirichletForm (n := n) (Ω := Ω) z z)
    {f : DerivLp n 2 Ω}
    {u : H¹₀(Ω)}
    (hu : IsDirichletSemilinearWeakSolution g f u) :
    ‖u‖ ≤ ‖f‖ / c := by
  exact (SobolevSpace.Weak.norm_le_load_norm_div_of_nonneg _ c hc hcoercive
    (fun z ↦ loadFunctional (n := n) (Ω := Ω) (N z))
    ((isDirichletSemilinearWeakSolution_iff_nemytskii_load g N hNrep f u).mp hu)
    (dirichletNemytskii_self_pairing_nonneg g N hNrep hgsign u)).trans
    (div_le_div_of_nonneg_right (norm_loadFunctional_le f) hc.le)

/-- A bounded-domain semilinear Dirichlet equation with zero forcing has
only the zero weak solution when `g(x,s) * s` is nonnegative. -/
theorem eq_zero_of_dirichlet_semilinear_of_nonneg
    (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω)
    (g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (hgsign : ∀ᵐ x ∂domainMeasure n Ω, ∀ s, 0 ≤ g x s * s)
    {u : H¹₀(Ω)}
    (hu : IsDirichletSemilinearWeakSolution g 0 u) :
    u = 0 := by
  exact SobolevSpace.Weak.eq_zero_of_coercive_of_nonneg _ (dirichletForm_isCoercive hn hΩbounded)
    (fun z ↦ loadFunctional (n := n) (Ω := Ω) (N z)) (fun v ↦ by
      simpa only [loadFunctional_zero, zero_apply] using
        (isDirichletSemilinearWeakSolution_iff_nemytskii_load g N hNrep 0 u).mp hu v)
    (dirichletNemytskii_self_pairing_nonneg g N hNrep hgsign u)

/-- Continuous dependence of monotone semilinear Dirichlet solutions on the
`L²` forcing data. The constant is the reciprocal of the given coercivity
modulus of the Dirichlet form. -/
theorem norm_sub_le_forcing_sub_norm_div_of_monotone
    (g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (hgmono : ∀ᵐ x ∂domainMeasure n Ω, Monotone (g x))
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ z : H¹₀(Ω),
      c * ‖z‖ * ‖z‖ ≤
        dirichletForm (n := n) (Ω := Ω) z z)
    {f₁ f₂ : DerivLp n 2 Ω}
    {u₁ u₂ : H¹₀(Ω)}
    (hu₁ : IsDirichletSemilinearWeakSolution g f₁ u₁)
    (hu₂ : IsDirichletSemilinearWeakSolution g f₂ u₂) :
    ‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖ / c := by
  refine (SobolevSpace.Weak.norm_sub_le_load_sub_norm_div _ c hc hcoercive
    (fun z ↦ loadFunctional (n := n) (Ω := Ω) (N z))
    ((isDirichletSemilinearWeakSolution_iff_nemytskii_load g N hNrep f₁ u₁).mp hu₁)
    ((isDirichletSemilinearWeakSolution_iff_nemytskii_load g N hNrep f₂ u₂).mp hu₂)
    (by simpa only [loadFunctional_sub] using
      dirichletNemytskii_pairing_nonneg_of_monotone g N hNrep hgmono u₁ u₂)).trans ?_
  rw [← loadFunctional_sub]
  exact div_le_div_of_nonneg_right (norm_loadFunctional_le _) hc.le

/-- Continuous dependence for semilinear Dirichlet equations whose
nonlinearity is semimonotone with one-sided constant `L`. If `c` is a
coercivity modulus for the Dirichlet form and `L < c`, the solution map has
Lipschitz constant `1 / (c - L)` with respect to the `L²` forcing. -/
theorem norm_sub_le_forcing_sub_norm_div_of_semimonotone
    (g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (L : ℝ) (hL : 0 ≤ L)
    (hgsemimonotone : ∀ᵐ x ∂domainMeasure n Ω,
      Monotone fun s ↦ g x s + L * s)
    (c : ℝ)
    (hcoercive : ∀ z : H¹₀(Ω),
      c * ‖z‖ * ‖z‖ ≤
        dirichletForm (n := n) (Ω := Ω) z z)
    (hLc : L < c)
    {f₁ f₂ : DerivLp n 2 Ω}
    {u₁ u₂ : H¹₀(Ω)}
    (hu₁ : IsDirichletSemilinearWeakSolution g f₁ u₁)
    (hu₂ : IsDirichletSemilinearWeakSolution g f₂ u₂) :
    ‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖ / (c - L) := by
  refine (SobolevSpace.Weak.norm_sub_le_load_sub_norm_div_of_semimonotone _ c hcoercive
    (fun z ↦ loadFunctional (n := n) (Ω := Ω) (N z)) L hLc
    ((isDirichletSemilinearWeakSolution_iff_nemytskii_load g N hNrep f₁ u₁).mp hu₁)
    ((isDirichletSemilinearWeakSolution_iff_nemytskii_load g N hNrep f₂ u₂).mp hu₂)
    (by simpa only [loadFunctional_sub] using
          neg_mul_norm_sq_le_dirichletNemytskii_pairing_of_semimonotone g N hNrep L hL
            hgsemimonotone u₁ u₂)).trans ?_
  rw [← loadFunctional_sub]
  exact div_le_div_of_nonneg_right (norm_loadFunctional_le _) (sub_pos.mpr hLc).le

/-- Pointwise monotonicity of the nonlinearity gives uniqueness for the
semilinear Dirichlet equation. This result depends only on the two weak
equations and the coercivity of the Dirichlet form, not on the variational
existence hypotheses above. -/
theorem eq_of_dirichlet_semilinear_of_monotone
    (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω)
    (g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (hgmono : ∀ᵐ x ∂domainMeasure n Ω, Monotone (g x))
    {f : DerivLp n 2 Ω}
    {u w : H¹₀(Ω)}
    (hu : IsDirichletSemilinearWeakSolution g f u)
    (hw : IsDirichletSemilinearWeakSolution g f w) :
    u = w := by
  obtain ⟨c, hc, hcoercive⟩ := dirichletForm_isCoercive (n := n) (Ω := Ω) hn hΩbounded
  have h := norm_sub_le_forcing_sub_norm_div_of_monotone g N hNrep hgmono c hc hcoercive hu hw
  rw [sub_self, norm_zero, zero_div] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- A semimonotone semilinear Dirichlet equation has at most one weak
solution whenever its one-sided loss `L` is strictly smaller than the
coercivity modulus `c`. -/
theorem eq_of_dirichlet_semilinear_of_semimonotone
    (g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (L : ℝ) (hL : 0 ≤ L)
    (hgsemimonotone : ∀ᵐ x ∂domainMeasure n Ω,
      Monotone fun s ↦ g x s + L * s)
    (c : ℝ)
    (hcoercive : ∀ z : H¹₀(Ω),
      c * ‖z‖ * ‖z‖ ≤
        dirichletForm (n := n) (Ω := Ω) z z)
    (hLc : L < c)
    {f : DerivLp n 2 Ω}
    {u w : H¹₀(Ω)}
    (hu : IsDirichletSemilinearWeakSolution g f u)
    (hw : IsDirichletSemilinearWeakSolution g f w) :
    u = w := by
  have h := norm_sub_le_forcing_sub_norm_div_of_semimonotone g N hNrep L hL hgsemimonotone c
    hcoercive hLc hu hw
  rw [sub_self, norm_zero, zero_div] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

end SobolevSpace.GraphSpace
