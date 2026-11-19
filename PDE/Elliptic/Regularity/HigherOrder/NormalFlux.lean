/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Elliptic.Regularity.Boundary.H2.FluxDerivatives
import PDE.Spaces.Sobolev.GraphSpace.FiniteSums
public import PDE.Spaces.Sobolev.Calculus.Differentiation.WeakDerivativeData
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace

/-!
# Arbitrary-order normal-flux recovery

Our boundary induction repeatedly uses the divergence equation

`D_n q_n = -F - sum_{i != n} D_i q_i`

in place of the differentiated equation `D^γ Lu = D^γ f` of step 4 of Evans's proof of §6.3.2,
Theorem 5. When the forcing and the tangential flux derivatives belong to `H^r`, the right-hand side
is itself an `H^r` field (`normalFlux.exists_normalDerivative_of_weakDivergence`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 4 of the proof of Theorem 5, (91)-(94),
  pp. 342-343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {n r : ℕ} [Fact (0 < n)]

/--
The normal derivative selected by a weak divergence identity belongs to
`H^r` when the forcing and every matching tangential flux derivative belong
to `H^r`.
-/
theorem normalFlux.exists_normalDerivative_of_weakDivergence
    (q : Fin n → DerivLp n 2 (HalfSpace.upper n))
    (F : W^{r,2}(HalfSpace.upper n))
    (Dq : Fin n → W^{r,2}(HalfSpace.upper n))
    (hdiv : ∀ (phi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)),
      tsupport phi.toFun ⊆ HalfSpace.upper n →
        (∑ i : Fin n,
          ∫ x, (q i : ℝ^n → ℝ) x *
            iteratedPartialDeriv (n := n) [i] phi.toFun x
            ∂domainMeasure n (HalfSpace.upper n)) =
          ∫ x,
            ((((F : WkpAmbientOn n r 2 (HalfSpace.upper n))
              (baseIndex n r) : DerivLp n 2 (HalfSpace.upper n)) :
                ℝ^n → ℝ) x) * phi.toFun x
            ∂domainMeasure n (HalfSpace.upper n))
    (htangential : ∀ i : Fin n, i ≠ PDE.Common.lastIndex (n := n) →
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [i]
        (q i : ℝ^n → ℝ)
        ((((Dq i : WkpAmbientOn n r 2 (HalfSpace.upper n))
          (baseIndex n r) : DerivLp n 2 (HalfSpace.upper n)) :
            ℝ^n → ℝ))) :
    Nonempty
      (WeakDerivativeData r 2 (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (q (PDE.Common.lastIndex (n := n)) : ℝ^n → ℝ)) := by
  classical
  let normal := PDE.Common.lastIndex (n := n)
  let tangential : Finset (Fin n) := Finset.univ.erase normal
  let f : DerivLp n 2 (HalfSpace.upper n) :=
    ((F : WkpAmbientOn n r 2 (HalfSpace.upper n)) (baseIndex n r) : DerivLp n 2 (HalfSpace.upper n))
  let S : DerivLp n 2 (HalfSpace.upper n) :=
    (((∑ i ∈ tangential, Dq i : W^{r,2}(HalfSpace.upper n)) :
      WkpAmbientOn n r 2 (HalfSpace.upper n)) (baseIndex n r) : DerivLp n 2 (HalfSpace.upper n))
  have hraw : HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [normal] (q normal : ℝ^n → ℝ)
      fun x ↦ -(f : ℝ^n → ℝ) x - ∑ i ∈ tangential,
        (((Dq i : WkpAmbientOn n r 2 (HalfSpace.upper n)) (baseIndex n r) :
          DerivLp n 2 (HalfSpace.upper n)) : ℝ^n → ℝ) x :=
    normalFlux.hasWeakDerivative_of_weakDivergence q _ f (by simpa [f] using hdiv)
      fun i hi ↦ htangential i (by simpa [normal] using hi)
  refine ⟨{ derivative := -F - ∑ i ∈ tangential, Dq i, derivative_spec := hraw.congr_ae .rfl ?_ }⟩
  filter_upwards [Lp.coeFn_sub (-f) S, Lp.coeFn_neg f, coeFn_finsetSum_coordinate (n := n) (k := r)
    (p := (2 : ENNReal)) (Ω := HalfSpace.upper n) tangential Dq (baseIndex n r)]
    with x hxsub hxneg hxsum
  refine (hxsub.trans ?_).symm
  rw [Pi.sub_apply, hxneg, hxsum]
  rfl

end SobolevSpace.GraphSpace.BoundaryRegularity
