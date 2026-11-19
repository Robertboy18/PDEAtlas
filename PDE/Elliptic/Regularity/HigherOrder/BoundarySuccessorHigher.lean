/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.HigherOrder.BoundaryData
import PDE.Elliptic.Regularity.HigherOrder.CrossFluxHigher
import PDE.Elliptic.Regularity.HigherOrder.DiagonalFluxHigher
import PDE.Elliptic.Regularity.HigherOrder.PureNormalHigher
import PDE.Spaces.Sobolev.Calculus.Slicing.MissingCoordinate
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Higher-order boundary successor

`exists_boundary_higherOrder_succOrder` is the local algebraic step of our boundary induction.
Tangential first derivatives at the next regularity level provide the mixed second derivatives.
Differentiating the normal flux then isolates its diagonal term, multiplication by the given Sobolev
reciprocal recovers the pure third normal derivative, and Sobolev assembly produces the next
regularity order. This is the counterpart of step 4 of Evans's proof of §6.3.2, Theorem 5, which
recovers the normal derivatives one at a time from `D^γ Lu = D^γ f` and `aⁿⁿ ≥ θ > 0`.

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
The successor step in the higher-order boundary regularity induction.

The flux gradient is the row `D_normal D_j U`.  For every cross index, its
`W^{r+1,2}` representative is constructed by normally differentiating the
given `W^{r+2,2}` representative of `D_j U`; weak-derivative permutation and
uniqueness identify it with the corresponding mixed derivative of `U`.
The `L2` derivative `D_normal^3 U` is then promoted to `W^{r,2}`
through the diagonal flux and used in the final Sobolev assembly.
-/
theorem exists_boundary_higherOrder_succOrder
    (hr : 0 < r)
    (hOmegaOpen : IsOpen Omega)
    (U : W^{r + 2,2}(Omega))
    (normal : Fin n)
    (A : Fin n → W^{r + 1,∞}(Omega))
    (data : BoundarySuccessorData r U normal A)
    (aNormal : ℝ^n → ℝ)
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hpositive :
      ∀ᵐ x ∂domainMeasure n Omega, delta ≤ aNormal x)
    (hANormal :
      ((((A normal : WkpAmbientOn n (r + 1) ∞ Omega)
        (baseIndex n (r + 1)) : DerivLp n ∞ Omega) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] aNormal)
    (reciprocal : W^{r,∞}(Omega))
    (hreciprocal :
      ((((reciprocal : WkpAmbientOn n r ∞ Omega)
        (baseIndex n r) : DerivLp n ∞ Omega) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] fun x ↦ (aNormal x)⁻¹) :
    ∃ W : W^{r + 3,2}(Omega),
      ⇑((W : WkpAmbientOn n (r + 3) 2 Omega)
          (baseIndex n (r + 3)) : DerivLp n 2 Omega)
        =ᵐ[domainMeasure n Omega]
          ⇑((U : WkpAmbientOn n (r + 2) 2 Omega)
            (baseIndex n (r + 2)) : DerivLp n 2 Omega) := by
  let f : ℝ^n → ℝ :=
    ((U : WkpAmbientOn n (r + 2) 2 Omega) (baseIndex n (r + 2)) : DerivLp n 2 Omega)
  let gradient (j : Fin n) : W^{r,2}(Omega) := derivativeWordCLM (n := n) (m := r + 2) (r := r)
    (p := 2) (Ω := Omega) [normal, j] (by simp only [List.length_cons, List.length_nil]; omega) U
  have hgradientBase (j : Fin n) :
      ((gradient j : WkpAmbientOn n r 2 Omega) (baseIndex n r) : DerivLp n 2 Omega) =
        ((U : WkpAmbientOn n (r + 2) 2 Omega) (secondDerivIndex n (r + 2) (by omega) normal j) :
          DerivLp n 2 Omega) :=
    Lp.ext (by simp [gradient, secondDerivIndex])
  have hmixed (j : Fin n) : HasWeakDerivativeOn (n := n) Omega [normal, j] f
      ((((gradient j : WkpAmbientOn n r 2 Omega) (baseIndex n r) : DerivLp n 2 Omega)) :
        ℝ^n → ℝ) := by
    simpa [f, hgradientBase j, secondDerivIndex] using
      U.property.hasWeakDerivativeOn_list [normal, j] (by simp)
  let crossComponent (j : Fin n) (hj : j ≠ normal) : W^{r + 1,2}(Omega) :=
    derivativeWordCLM (n := n) (m := r + 2) (r := r + 1) (p := 2) (Ω := Omega) [normal]
      (by simp only [List.length_singleton]; omega) (data.tangentialRepresentative j hj)
  have hcrossComponent (j : Fin n) (hj : j ≠ normal) :
      ((((crossComponent j hj : WkpAmbientOn n (r + 1) 2 Omega) (baseIndex n (r + 1)) :
        DerivLp n 2 Omega) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Omega]
          ((((gradient j : WkpAmbientOn n r 2 Omega) (baseIndex n r) : DerivLp n 2 Omega) :
            ℝ^n → ℝ)) := by
    have h := (data.tangentialRepresentative j hj).property.hasWeakDerivativeOn_first
      (by omega) normal
    rw [data.tangentialRepresentative_base_eq j hj] at h
    simpa [crossComponent] using h.unique_ae hOmegaOpen
      ((by simpa [f] using U.property.hasWeakDerivativeOn_first (by omega) j :
        HasWeakDerivativeOn (n := n) Omega [j] f _).cancel_prefix_append_single normal
          ((hmixed j).perm (List.Perm.swap normal j []).symm))
  obtain ⟨diagonalData⟩ := nonempty_diagonalFluxHigher_normalDerivative_of_totalFlux normal
    (fun j ↦ (A j : WkpAmbientOn n (r + 1) ∞ Omega) (baseIndex n (r + 1)))
    (fun j ↦ (gradient j : WkpAmbientOn n r 2 Omega) (baseIndex n r))
    data.normalFluxDerivative.derivative
    (by simpa only [hgradientBase] using data.normalFluxDerivative.derivative_spec)
    fun j hj ↦ nonempty_crossFluxHigher_normalDerivative_of_component hOmegaOpen normal (A j)
      ((gradient j : WkpAmbientOn n r 2 Omega) (baseIndex n r)) (crossComponent j hj)
      (hcrossComponent j hj)
  let pureNormalThirdL2 : DerivLp n 2 Omega :=
    (U : WkpAmbientOn n (r + 2) 2 Omega) (pureDerivIndex n (r + 2) 3 (by omega) normal)
  have hpureNormalThirdStep : HasWeakDerivativeOn (n := n) Omega [normal]
      ((((gradient normal : WkpAmbientOn n r 2 Omega) (baseIndex n r) : DerivLp n 2 Omega)) :
        ℝ^n → ℝ) (pureNormalThirdL2 : ℝ^n → ℝ) :=
    (hmixed normal).cancel_prefix_append_single normal (by
      simpa [f, pureNormalThirdL2, pureDerivIndex] using
        U.property.hasWeakDerivativeOn_list [normal, normal, normal]
          (by simp only [List.length_cons, List.length_nil]; omega))
  obtain ⟨pureNormalThird, hpureNormalThirdBase⟩ :=
    exists_pureNormalHigher_representative_of_diagonalFluxDerivative_of_reciprocal
      hr hOmegaOpen normal (A normal) aNormal hdelta hpositive hANormal
      reciprocal hreciprocal (gradient normal) pureNormalThirdL2
      hpureNormalThirdStep diagonalData.derivative diagonalData.derivative_spec
  exact exists_succOrder_of_coordinateDerivatives_except_one hOmegaOpen U normal
    data.tangentialRepresentative data.tangentialRepresentative_base_eq
    { derivative := pureNormalThird
      derivative_spec := hpureNormalThirdStep.congr_ae (by rw [hgradientBase normal])
        hpureNormalThirdBase.symm }

end SobolevSpace.GraphSpace.BoundaryRegularity
