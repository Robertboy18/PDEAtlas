/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
import PDE.Spaces.Sobolev.GraphSpace.FiniteSums
public import PDE.Spaces.Sobolev.Calculus.Differentiation.WeakDerivativeData

/-!
# Arbitrary-order diagonal-flux recovery

In the boundary regularity bootstrap, pure normal derivatives cannot be
reached by tangential difference quotients and must be read off from the
equation. Writing the divergence equation as

`∂ₙ(∑ⱼ aₙⱼ ∂ⱼ u) = -F - ∑_{i ≠ n} ∂ᵢ(∑ⱼ aᵢⱼ ∂ⱼ u)`

gives the normal derivative of the total normal flux `∑ⱼ aₙⱼ ∂ⱼ u`. The cross
terms `aₙⱼ ∂ⱼ u` with `j ≠ n` contain a tangential derivative, so their
normal derivatives are known from the tangential step. Subtracting them
leaves the normal derivative of the diagonal flux `aₙₙ ∂ₙ u`, from which
`∂ₙ² u` follows once one divides by `aₙₙ ≥ α`. We record the
finite-sum subtraction at an arbitrary Sobolev order `r`.

## Main results

* `nonempty_diagonalFluxHigher_normalDerivative_of_totalFlux`: given an `H^r`
  representative of the normal derivative of the total flux and `H^r`
  weak-derivative data for the normal derivative of every cross flux, the
  normal derivative of the diagonal flux has `H^r` weak-derivative data.

## Implementation notes

Only `L∞` coefficients and `L²` gradient components are needed here. The
higher regularity of the coefficients enters when the caller constructs the
cross-flux witnesses, and the division by `aₙₙ` happens downstream.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 5 of the proof of Theorem 4, (52)-(55),
  pp. 336-337, and step 4 of the proof of Theorem 5, (91)-(94), pp. 342-343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal BigOperators Sobolev

variable {n r : ℕ} {Omega : Set (ℝ^n)}

/--
Subtracting the normally differentiated cross fluxes from the normally
differentiated total flux gives an `H^r` representative for the normal
derivative of the diagonal flux.

The coefficient row is only required in `L∞` and the gradient components in
`L2` here.  Their higher regularity enters when callers construct the
cross-flux derivative witnesses.
-/
theorem nonempty_diagonalFluxHigher_normalDerivative_of_totalFlux
    (normal : Fin n)
    (coeff : Fin n → DerivLp n ∞ Omega)
    (gradient : Fin n → DerivLp n 2 Omega)
    (Dtotal : W^{r,2}(Omega))
    (htotal :
      HasWeakDerivativeOn (n := n) Omega [normal]
        (fun x ↦ ∑ j : Fin n,
          (coeff j : ℝ^n → ℝ) x * (gradient j : ℝ^n → ℝ) x)
        ((((Dtotal : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
          DerivLp n 2 Omega) : ℝ^n → ℝ)))
    (hcross : ∀ j : Fin n, j ≠ normal →
      Nonempty
        (WeakDerivativeData r 2 Omega [normal]
          (fun x ↦
            (coeff j : ℝ^n → ℝ) x * (gradient j : ℝ^n → ℝ) x))) :
    Nonempty
      (WeakDerivativeData r 2 Omega [normal]
        (fun x ↦
          (coeff normal : ℝ^n → ℝ) x *
            (gradient normal : ℝ^n → ℝ) x)) := by
  classical
  let crossDerivative (j : Fin n) : W^{r,2}(Omega) :=
    if hj : j ≠ normal then (Classical.choice (hcross j hj)).derivative else 0
  let DcrossSum : W^{r,2}(Omega) := ∑ j ∈ Finset.univ.erase normal, crossDerivative j
  have hcrossSum : HasWeakDerivativeOn (n := n) Omega [normal]
      (fun x ↦ ∑ j ∈ Finset.univ.erase normal,
        (coeff j : ℝ^n → ℝ) x * (gradient j : ℝ^n → ℝ) x)
      ((((DcrossSum : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
        DerivLp n 2 Omega) : ℝ^n → ℝ)) := by
    refine (hasWeakDerivativeOn_finsetSum (Finset.univ.erase normal) _
      (fun j ↦ (((crossDerivative j : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
        DerivLp n 2 Omega) : ℝ^n → ℝ)) [normal] fun j hj ↦ ?_).congr_ae .rfl ?_
    · simpa [crossDerivative, Finset.ne_of_mem_erase hj] using
        (Classical.choice (hcross j (Finset.ne_of_mem_erase hj))).derivative_spec
    · simpa [DcrossSum] using (coeFn_finsetSum_coordinate (n := n) (k := r)
        (p := (2 : ENNReal)) (Ω := Omega) (Finset.univ.erase normal) crossDerivative
          (baseIndex n r)).symm
  refine ⟨⟨Dtotal - DcrossSum, (hasWeakDerivativeOn_sub [normal] htotal hcrossSum).congr_ae ?_
    (Lp.coeFn_sub ((Dtotal : WkpAmbientOn n r 2 Omega) (baseIndex n r))
      ((DcrossSum : WkpAmbientOn n r 2 Omega) (baseIndex n r))).symm⟩⟩
  filter_upwards with x
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ normal)]
  ring

end SobolevSpace.GraphSpace.BoundaryRegularity
