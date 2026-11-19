/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Scalar.OddPower
public import PDE.Elliptic.Semilinear.DirichletNemytskii
import PDE.Elliptic.Semilinear.DirichletMonotonicity

/-!
# Monotonicity for odd-power semilinear Dirichlet equations

We specialize the monotone Dirichlet theory to

`-Delta u + linear * u + nonlinear * u ^ (2 * k + 1) = f`.

Nonnegative coefficients make the scalar nonlinearity monotone, so coercivity
of the Dirichlet form gives continuous dependence on the forcing and
uniqueness. The same conclusions hold for a signed linear coefficient when
its negative part `linear⁻` is smaller than the coercivity modulus: shifting
the scalar polynomial by `linear⁻ * z` makes it monotone, and the exact
remaining modulus is `c - linear⁻`.

The represented Nemytskii map remains an explicit hypothesis: membership of
the odd power in `L2` depends on the dimension, exponent, and available
Sobolev embedding. Variational existence is developed separately in
`OddPower.Variational`.

## Main results

* `norm_le_forcing_norm_div_of_odd_power`,
  `norm_le_forcing_norm_div_of_odd_power_of_negPart_lt_coercivity`: a priori
  bounds `‖u‖ ≤ ‖f‖/c` and `‖u‖ ≤ ‖f‖/(c - linear⁻)`.
* `norm_sub_le_forcing_sub_norm_div_of_odd_power`,
  `norm_sub_le_forcing_sub_norm_div_of_odd_power_of_negPart_lt_coercivity`:
  continuous dependence on the forcing.
* `eq_zero_of_dirichlet_odd_power`, `eq_of_dirichlet_odd_power`,
  `eq_of_dirichlet_odd_power_of_negPart_lt_coercivity`: zero-forcing rigidity
  and uniqueness.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.1 (monotonicity methods).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set

variable {n : ℕ} {Ω : Set (ℝ^n)}

section

local notation "L2" => DerivLp n 2 Ω
local notation "P" =>
  baseCoordCLM (n := n) (Ω := Ω)

/-- An odd-power semilinear Dirichlet solution is bounded by its `L2`
forcing, with the reciprocal coercivity modulus as constant. -/
theorem norm_le_forcing_norm_div_of_odd_power
    (linear nonlinear : ℝ) (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear)
    (N : H¹₀(Ω) → L2)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : L2) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦
          PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k
            ((P u : ℝ^n → ℝ) x))
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ z : H¹₀(Ω),
      c * ‖z‖ * ‖z‖ ≤
        dirichletForm (n := n) (Ω := Ω) z z)
    {f : L2} {u : H¹₀(Ω)}
    (hu : IsDirichletSemilinearWeakSolution
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
      f u) :
    ‖u‖ ≤ ‖f‖ / c := by
  exact norm_le_forcing_norm_div_of_nonneg
    (n := n) (Ω := Ω)
    (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
    N hNrep
    (Filter.Eventually.of_forall fun _ _ ↦
      PDE.Analysis.Scalar.oddPowerPolynomial_mul_self_nonneg
        k hlinear hnonlinear _)
    c hc hcoercive hu

/-- The zero-forcing odd-power Dirichlet equation has only the zero weak
solution when both coefficients are nonnegative. -/
theorem eq_zero_of_dirichlet_odd_power
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (linear nonlinear : ℝ) (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear)
    (N : H¹₀(Ω) → L2)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : L2) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦
          PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k
            ((P u : ℝ^n → ℝ) x))
    {u : H¹₀(Ω)}
    (hu : IsDirichletSemilinearWeakSolution
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
      0 u) :
    u = 0 := by
  exact eq_zero_of_dirichlet_semilinear_of_nonneg
    (n := n) (Ω := Ω) hn hΩbounded
    (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
    N hNrep
    (Filter.Eventually.of_forall fun _ _ ↦
      PDE.Analysis.Scalar.oddPowerPolynomial_mul_self_nonneg
        k hlinear hnonlinear _)
    hu

/-- Solutions of an odd-power semilinear Dirichlet equation depend
continuously on their `L2` forcing data. -/
theorem norm_sub_le_forcing_sub_norm_div_of_odd_power
    (linear nonlinear : ℝ) (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear)
    (N : H¹₀(Ω) → L2)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : L2) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦
          PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k
            ((P u : ℝ^n → ℝ) x))
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ z : H¹₀(Ω),
      c * ‖z‖ * ‖z‖ ≤
        dirichletForm (n := n) (Ω := Ω) z z)
    {f₁ f₂ : L2} {u₁ u₂ : H¹₀(Ω)}
    (hu₁ : IsDirichletSemilinearWeakSolution
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
      f₁ u₁)
    (hu₂ : IsDirichletSemilinearWeakSolution
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
      f₂ u₂) :
    ‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖ / c := by
  exact norm_sub_le_forcing_sub_norm_div_of_monotone
    (n := n) (Ω := Ω)
    (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
    N hNrep
    (Filter.Eventually.of_forall fun _ ↦
      PDE.Analysis.Scalar.monotone_oddPowerPolynomial
        k hlinear hnonlinear)
    c hc hcoercive hu₁ hu₂

/-- Odd-power Dirichlet solutions remain stable when the linear coefficient
is negative, provided its negative part is smaller than the coercivity
modulus. The higher-order coefficient only needs to be nonnegative. -/
theorem norm_sub_le_forcing_sub_norm_div_of_odd_power_of_negPart_lt_coercivity
    (linear nonlinear : ℝ) (k : ℕ)
    (hnonlinear : 0 ≤ nonlinear)
    (N : H¹₀(Ω) → L2)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : L2) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦
          PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k
            ((P u : ℝ^n → ℝ) x))
    (c : ℝ)
    (hcoercive : ∀ z : H¹₀(Ω),
      c * ‖z‖ * ‖z‖ ≤
        dirichletForm (n := n) (Ω := Ω) z z)
    (hsmall : linear⁻ < c)
    {f₁ f₂ : L2} {u₁ u₂ : H¹₀(Ω)}
    (hu₁ : IsDirichletSemilinearWeakSolution
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
      f₁ u₁)
    (hu₂ : IsDirichletSemilinearWeakSolution
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
      f₂ u₂) :
    ‖u₁ - u₂‖ ≤
      ‖f₁ - f₂‖ / (c - linear⁻) := by
  exact norm_sub_le_forcing_sub_norm_div_of_semimonotone
    (n := n) (Ω := Ω)
    (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
    N hNrep
    linear⁻ (negPart_nonneg linear)
    (Filter.Eventually.of_forall fun _ ↦
      PDE.Analysis.Scalar.monotone_oddPowerPolynomial_add_negPart
        k hnonlinear)
    c hcoercive hsmall hu₁ hu₂

/-- A weak odd-power Dirichlet solution satisfies the expected coercive
bound even when the linear coefficient is negative, provided its negative
part is smaller than the Dirichlet coercivity modulus. -/
theorem norm_le_forcing_norm_div_of_odd_power_of_negPart_lt_coercivity
    (linear nonlinear : ℝ) (k : ℕ)
    (hnonlinear : 0 ≤ nonlinear)
    (N : H¹₀(Ω) → L2)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : L2) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦
          PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k
            ((P u : ℝ^n → ℝ) x))
    (c : ℝ)
    (hcoercive : ∀ z : H¹₀(Ω),
      c * ‖z‖ * ‖z‖ ≤
        dirichletForm (n := n) (Ω := Ω) z z)
    (hsmall : linear⁻ < c)
    {f : L2} {u : H¹₀(Ω)}
    (hu : IsDirichletSemilinearWeakSolution
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
      f u) :
    ‖u‖ ≤ ‖f‖ / (c - linear⁻) := by
  have hzero : IsDirichletSemilinearWeakSolution
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
      0 (0 : H¹₀(Ω)) :=
    isDirichletSemilinearWeakSolution_zero
      (n := n) (Ω := Ω)
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
      (Filter.Eventually.of_forall fun _ ↦
        PDE.Analysis.Scalar.oddPowerPolynomial_zero linear nonlinear k)
  have hbound :=
    norm_sub_le_forcing_sub_norm_div_of_odd_power_of_negPart_lt_coercivity
      linear nonlinear k hnonlinear N hNrep
      c hcoercive hsmall hu hzero
  simpa only [sub_zero, norm_zero] using hbound

/-- A bounded-domain odd-power semilinear Dirichlet equation with
nonnegative coefficients has at most one weak `H1_0` solution. -/
theorem eq_of_dirichlet_odd_power
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (linear nonlinear : ℝ) (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear)
    (N : H¹₀(Ω) → L2)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : L2) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦
          PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k
            ((P u : ℝ^n → ℝ) x))
    {f : L2} {u w : H¹₀(Ω)}
    (hu : IsDirichletSemilinearWeakSolution
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
      f u)
    (hw : IsDirichletSemilinearWeakSolution
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
      f w) :
    u = w := by
  exact eq_of_dirichlet_semilinear_of_monotone
    (n := n) (Ω := Ω) hn hΩbounded
    (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
    N hNrep
    (Filter.Eventually.of_forall fun _ ↦
      PDE.Analysis.Scalar.monotone_oddPowerPolynomial
        k hlinear hnonlinear)
    hu hw

/-- An odd-power Dirichlet equation has at most one weak solution when the
negative part of its linear coefficient is dominated by coercivity. -/
theorem eq_of_dirichlet_odd_power_of_negPart_lt_coercivity
    (linear nonlinear : ℝ) (k : ℕ)
    (hnonlinear : 0 ≤ nonlinear)
    (N : H¹₀(Ω) → L2)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : L2) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦
          PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k
            ((P u : ℝ^n → ℝ) x))
    (c : ℝ)
    (hcoercive : ∀ z : H¹₀(Ω),
      c * ‖z‖ * ‖z‖ ≤
        dirichletForm (n := n) (Ω := Ω) z z)
    (hsmall : linear⁻ < c)
    {f : L2} {u w : H¹₀(Ω)}
    (hu : IsDirichletSemilinearWeakSolution
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
      f u)
    (hw : IsDirichletSemilinearWeakSolution
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
      f w) :
    u = w := by
  have hnorm :
      ‖u - w‖ ≤
        ‖f - f‖ / (c - linear⁻) :=
    norm_sub_le_forcing_sub_norm_div_of_odd_power_of_negPart_lt_coercivity
      linear nonlinear k hnonlinear N hNrep
      c hcoercive hsmall hu hw
  have hzero : ‖u - w‖ = 0 :=
    le_antisymm (by simpa using hnorm) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end

end SobolevSpace.GraphSpace
