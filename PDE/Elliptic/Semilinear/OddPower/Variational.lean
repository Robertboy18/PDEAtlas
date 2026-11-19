/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.VariationalDirichlet
public import PDE.Analysis.Scalar.OddPower
import PDE.Elliptic.Semilinear.Variational
import PDE.Elliptic.Variational.ModifiedHelmholtz

/-!
# Variational existence for odd-power semilinear Dirichlet equations

We prove existence and uniqueness for

`-Delta u + linear * u + nonlinear * u ^ (2 * k + 1) = f`

by the direct method. The represented Nemytskii map and differentiability of
the integral potential remain explicit hypotheses because their proofs depend
on the dimension, exponent, and available Sobolev embedding.

For a signed linear coefficient, the linear term is absorbed into the
modified Helmholtz form. Coercivity is retained whenever the negative part
of the coefficient is smaller than the given Dirichlet coercivity
modulus.

## Main results

* `existsUnique_dirichlet_odd_power`: existence and uniqueness for
  nonnegative `linear` and `nonlinear`.
* `existsUnique_dirichlet_odd_power_of_negPart_lt_coercivity`: the same for a
  signed linear coefficient whose negative part is below the given
  coercivity modulus of the Dirichlet form.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, Theorem 2 (Existence of minimizer) and
  Theorem 3 (Uniqueness of minimizer), and §8.2.3, Theorem 4.
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

/-- The direct method gives a unique weak solution of the odd-power
Dirichlet equation

`-Delta u + linear * u + nonlinear * u ^ (2 * k + 1) = f`.

The analytic hypotheses require integrability of the potential energy,
an `L²` representative `N u` of the polynomial nonlinearity for every `u ∈ H¹₀`,
and Fréchet differentiability of the integral potential with derivative
`loadFunctional (N u)`. The theorem assumes these inputs; it does not derive
them from a dimension or exponent restriction. By Sobolev embedding the representability
`hNrep` holds for every `k` when `n ≤ 2`, and for `2 * k + 1 ≤ n / (n - 2)` when `n ≥ 3`.
Above that range, with `nonlinear ≠ 0` and `Ω` open and nonempty, it fails and the theorem
is vacuous. -/
theorem existsUnique_dirichlet_odd_power
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (linear nonlinear : ℝ) (k : ℕ)
    (hlinear : 0 ≤ linear) (hnonlinear : 0 ≤ nonlinear)
    (N : H¹₀(Ω) → L2)
    (hpotentialIntegrable : ∀ u : H¹₀(Ω),
      Integrable
        (fun x ↦
          PDE.Analysis.Scalar.oddPowerPotential linear nonlinear k
            ((P u : ℝ^n → ℝ) x))
        (domainMeasure n Ω))
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : L2) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦
          PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k
            ((P u : ℝ^n → ℝ) x))
    (hpotentialDerivative : ∀ u : H¹₀(Ω),
      HasFDerivAt
        (dirichletIntegralPotential (n := n) (Ω := Ω)
          (fun _ ↦
            PDE.Analysis.Scalar.oddPowerPotential linear nonlinear k))
        (loadFunctional (n := n) (Ω := Ω) (N u)) u)
    (f : L2) :
    ∃! u : H¹₀(Ω),
      IsDirichletSemilinearWeakSolution
        (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
        f u :=
  existsUnique_dirichlet_semilinear_of_variational (n := n) (Ω := Ω) hn hΩbounded
    (fun _ ↦ PDE.Analysis.Scalar.oddPowerPotential linear nonlinear k)
    (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k) N hpotentialIntegrable
    (.of_forall fun _ ↦ PDE.Analysis.Scalar.convexOn_oddPowerPotential k hlinear hnonlinear)
    hNrep hpotentialDerivative f

/-- The direct method also covers a signed linear coefficient when its
negative part is smaller than a given Dirichlet coercivity modulus.

The linear term is absorbed into the modified Helmholtz form. The remaining
higher-power potential is nonnegative and convex. The analytic inputs are
its integrability, an `L²` representative of the higher-power nonlinearity
for every `u ∈ H¹₀`, and the stated Fréchet derivative of its integral. -/
theorem existsUnique_dirichlet_odd_power_of_negPart_lt_coercivity
    (linear nonlinear : ℝ) (k : ℕ)
    (hnonlinear : 0 ≤ nonlinear)
    (N : H¹₀(Ω) → L2)
    (hpotentialIntegrable : ∀ u : H¹₀(Ω),
      Integrable
        (fun x ↦
          PDE.Analysis.Scalar.oddPowerPotential 0 nonlinear k
            ((P u : ℝ^n → ℝ) x))
        (domainMeasure n Ω))
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : L2) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦
          PDE.Analysis.Scalar.oddPowerPolynomial 0 nonlinear k
            ((P u : ℝ^n → ℝ) x))
    (hpotentialDerivative : ∀ u : H¹₀(Ω),
      HasFDerivAt
        (dirichletIntegralPotential (n := n) (Ω := Ω)
          (fun _ ↦
            PDE.Analysis.Scalar.oddPowerPotential 0 nonlinear k))
        (loadFunctional (n := n) (Ω := Ω) (N u)) u)
    (c : ℝ)
    (hcoercive : ∀ z : H¹₀(Ω),
      c * ‖z‖ * ‖z‖ ≤
        dirichletForm (n := n) (Ω := Ω) z z)
    (hsmall : linear⁻ < c)
    (f : L2) :
    ∃! u : H¹₀(Ω),
      IsDirichletSemilinearWeakSolution
        (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k)
        f u := by
  let Nfull : H¹₀(Ω) → L2 := fun u ↦ linear • P u + N u
  have hNfullRep (u : H¹₀(Ω)) : ((Nfull u : L2) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
      PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k ((P u : ℝ^n → ℝ) x) := by
    filter_upwards [Lp.coeFn_add (linear • P u) (N u), Lp.coeFn_smul linear (P u), hNrep u]
      with x hxadd hxlinear hxnonlinear
    rw [show Nfull u = linear • P u + N u from rfl, hxadd, Pi.add_apply, hxlinear,
      Pi.smul_apply, smul_eq_mul, hxnonlinear]
    simp [PDE.Analysis.Scalar.oddPowerPolynomial]
  have hweak_iff (u : H¹₀(Ω)) :
      IsDirichletSemilinearWeakSolution
          (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k) f u ↔
        ∀ v : H¹₀(Ω), modifiedHelmholtzForm (n := n) (Ω := Ω) linear u v +
          loadFunctional (n := n) (Ω := Ω) (N u) v = loadFunctional (n := n) (Ω := Ω) f v := by
    rw [isDirichletSemilinearWeakSolution_iff_nemytskii_load (n := n) (Ω := Ω)
      (fun _ ↦ PDE.Analysis.Scalar.oddPowerPolynomial linear nonlinear k) Nfull hNfullRep f u]
    refine forall_congr' fun v ↦ ?_
    simp only [Nfull, modifiedHelmholtzForm_apply, loadFunctional_add, loadFunctional_smul,
      add_apply, smul_apply, smul_eq_mul, loadFunctional_apply]
    exact ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩
  obtain ⟨u, hu, huUnique⟩ :=
    @PDE.Elliptic.Semilinear.existsUnique_variational_weak_solution H¹₀(Ω) inferInstance
      inferInstance inferInstance (modifiedHelmholtzForm (n := n) (Ω := Ω) linear)
      (modifiedHelmholtzForm_symm (n := n) (Ω := Ω) linear) (c - linear⁻) (sub_pos.mpr hsmall)
      (modifiedHelmholtzForm_coercive_bound_of_dirichlet (n := n) (Ω := Ω) linear c hcoercive)
      (dirichletIntegralPotential (n := n) (Ω := Ω)
        (fun _ ↦ PDE.Analysis.Scalar.oddPowerPotential 0 nonlinear k))
      (convexOn_dirichletIntegralPotential (n := n) (Ω := Ω)
        (fun _ ↦ PDE.Analysis.Scalar.oddPowerPotential 0 nonlinear k) hpotentialIntegrable
        (.of_forall fun _ ↦
          PDE.Analysis.Scalar.convexOn_oddPowerPotential k (le_refl 0) hnonlinear))
      (fun w ↦ loadFunctional (n := n) (Ω := Ω) (N w)) hpotentialDerivative
      (loadFunctional (n := n) (Ω := Ω) f)
  exact ⟨u, (hweak_iff u).mpr hu, fun w hw ↦ huUnique w ((hweak_iff w).mp hw)⟩

end

end SobolevSpace.GraphSpace
