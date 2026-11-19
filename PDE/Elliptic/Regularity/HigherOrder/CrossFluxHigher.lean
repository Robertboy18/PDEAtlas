/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Spaces.Sobolev.Calculus.Product.HigherOrderOperator
public import PDE.Spaces.Sobolev.Calculus.Differentiation.WeakDerivativeData

/-!
# Arbitrary-order cross-flux derivatives

In our boundary induction, the previous tangential step supplies `D_j u` in `H^{r+1}` for every
cross index `j`. Multiplication by an `H^{r+1,∞}` coefficient puts `A_{nj} D_j u` in `H^{r+1}`, so
its normal weak derivative has an `H^r` representative
(`nonempty_crossFluxHigher_normalDerivative_of_component`). These representatives discharge the
cross-flux hypotheses in diagonal-flux recovery. In step 4 of Evans's proof of §6.3.2, Theorem 5,
the corresponding terms belong to the part of `D^γ Lu` with fewer normal derivatives than `D^β u`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 4 of the proof of Theorem 5, (91)-(94),
  pp. 342-343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal BigOperators Sobolev

variable {n r : ℕ} {Omega : Set (ℝ^n)}

/--
An `H^{r+1}` representative of a gradient component produces an `H^r`
representative of the normal derivative of its cross flux.

The weak derivative is constructed from the `H^{r+1}` Sobolev product; it is
not assumed as an input.
-/
theorem nonempty_crossFluxHigher_normalDerivative_of_component
    (hOmegaOpen : IsOpen Omega)
    (normal : Fin n)
    (A : W^{r + 1,∞}(Omega))
    (gradient : DerivLp n 2 Omega)
    (component : W^{r + 1,2}(Omega))
    (hcomponent :
      ((((component : WkpAmbientOn n (r + 1) 2 Omega)
        (baseIndex n (r + 1)) : DerivLp n 2 Omega) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] (gradient : ℝ^n → ℝ)) :
    Nonempty
      (WeakDerivativeData r 2 Omega [normal]
        (fun x ↦
          ((((A : WkpAmbientOn n (r + 1) ∞ Omega)
            (baseIndex n (r + 1)) : DerivLp n ∞ Omega) :
              ℝ^n → ℝ) x) *
          (gradient : ℝ^n → ℝ) x)) := by
  let product : W^{r + 1,2}(Omega) :=
    wkTopProduct
      (n := n) (Ω := Omega) (Nat.succ_pos r)
      hOmegaOpen A component
  have hproduct :
      ((((product : WkpAmbientOn n (r + 1) 2 Omega)
        (baseIndex n (r + 1)) : DerivLp n 2 Omega) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] fun x ↦
          ((((A : WkpAmbientOn n (r + 1) ∞ Omega)
            (baseIndex n (r + 1)) : DerivLp n ∞ Omega) : ℝ^n → ℝ) x) *
          ((((component : WkpAmbientOn n (r + 1) 2 Omega)
            (baseIndex n (r + 1)) : DerivLp n 2 Omega) : ℝ^n → ℝ) x) := by
    simpa only [product, baseRepresentative] using
      wkTopProduct_base_ae
        (n := n) (Ω := Omega) (Nat.succ_pos r)
        hOmegaOpen A component
  let Dcross : W^{r,2}(Omega) :=
    derivativeWordCLM
      (n := n) (m := r + 1) (r := r) (p := 2) (Ω := Omega)
      [normal] (by simp [Nat.add_comm]) product
  have hnormal :
      HasWeakDerivativeOn (n := n) Omega [normal]
        ((((product : WkpAmbientOn n (r + 1) 2 Omega)
          (baseIndex n (r + 1)) : DerivLp n 2 Omega) : ℝ^n → ℝ))
        ((((Dcross : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
          DerivLp n 2 Omega) : ℝ^n → ℝ)) := by
    have hcanonical :
        HasWeakDerivativeOn (n := n) Omega [normal]
          ((((product : WkpAmbientOn n (r + 1) 2 Omega)
            (baseIndex n (r + 1)) : DerivLp n 2 Omega) : ℝ^n → ℝ))
          (((product : WkpAmbientOn n (r + 1) 2 Omega)
            (firstDerivIndex n (r + 1) (by omega) normal) :
              DerivLp n 2 Omega) : ℝ^n → ℝ) := by
      exact product.property.hasWeakDerivativeOn_first (by omega) normal
    simpa [Dcross] using hcanonical
  have hsource :
      ((((product : WkpAmbientOn n (r + 1) 2 Omega)
        (baseIndex n (r + 1)) : DerivLp n 2 Omega) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] fun x ↦
          ((((A : WkpAmbientOn n (r + 1) ∞ Omega)
            (baseIndex n (r + 1)) : DerivLp n ∞ Omega) :
              ℝ^n → ℝ) x) *
          (gradient : ℝ^n → ℝ) x := by
    filter_upwards [hproduct, hcomponent] with x hx hcomponentx
    rw [hx, hcomponentx]
  refine ⟨{
    derivative := Dcross
    derivative_spec := ?_
  }⟩
  exact
    (hasWeakDerivativeOn_congr_ae
      (n := n) (Ω := Omega) (α := [normal])
      hsource Filter.EventuallyEq.rfl).1 hnormal

end SobolevSpace.GraphSpace.BoundaryRegularity
