/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.WeakDerivativeData

/-!
# Data for higher-order boundary regularity

`BoundarySuccessorData` collects the two inputs of the pure-normal step of our boundary induction:
coordinate-derivative regularity away from the normal direction, and a Sobolev representative of the
differentiated normal flux. In Evans's proof of §6.3.2, Theorem 5, the first comes from the
tangential derivatives of step 3, and the second takes the place of the differentiated equation
`D^γ Lu = D^γ f` of step 4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, steps 3-4 of the proof of Theorem 5, (85)-(94),
  pp. 341-343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal BigOperators Sobolev

variable {n : ℕ}

/--
The data produced before the pure-normal step of the boundary successor
argument.
-/
structure BoundarySuccessorData
    (r : ℕ)
    {Omega : Set (ℝ^n)}
    (U : W^{r + 2,2}(Omega))
    (normal : Fin n)
    (coefficient : Fin n → W^{r + 1,∞}(Omega)) where
  /-- A higher-order Sobolev representative of each tangential derivative. -/
  tangentialRepresentative :
    ∀ i : Fin n, i ≠ normal → W^{r + 2,2}(Omega)
  /-- Each tangential representative has base coordinate `D_i U`. -/
  tangentialRepresentative_base_eq :
    ∀ (i : Fin n) (hi : i ≠ normal),
      ((tangentialRepresentative i hi :
          WkpAmbientOn n (r + 2) 2 Omega)
        (baseIndex n (r + 2)) : DerivLp n 2 Omega) =
          ((U : WkpAmbientOn n (r + 2) 2 Omega)
            (firstDerivIndex n (r + 2) (by omega) i) :
              DerivLp n 2 Omega)
  /-- The weak normal derivative of the normal flux. -/
  normalFluxDerivative :
    WeakDerivativeData r 2 Omega [normal]
      (fun x ↦ ∑ j : Fin n,
        ((((coefficient j : WkpAmbientOn n (r + 1) ∞ Omega)
          (baseIndex n (r + 1)) : DerivLp n ∞ Omega) :
            ℝ^n → ℝ) x) *
        ((((U : WkpAmbientOn n (r + 2) 2 Omega)
          (secondDerivIndex n (r + 2) (by omega) normal j) :
              DerivLp n 2 Omega) :
              ℝ^n → ℝ) x))

end SobolevSpace.GraphSpace.BoundaryRegularity
