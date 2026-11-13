/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Spaces.Sobolev.Calculus.Composition.Reciprocal
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
import PDE.Spaces.Sobolev.Calculus.Product.HigherOrderOperator
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation

/-!
# Arbitrary-order pure-normal coefficient recovery

If `u` is already in `H^r`, its normal derivative is known in `L²`, and the normal derivative of
`a * u` has an `H^r` representative, then the normal derivative of `u` itself has an `H^r`
representative (`exists_pureNormalHigher_representative_of_diagonalFluxDerivative`).

The proof identifies the weak Leibniz formula by uniqueness, subtracts the coefficient-derivative
commutator, constructs the positive reciprocal of the coefficient, and multiplies in `H^r`. This
plays the role of the division by `aⁿⁿ ≥ θ > 0` in step 4 of Evans's proof of §6.3.2, Theorem 5.

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
open scoped ENNReal Sobolev

variable {n r : ℕ} {Omega : Set (ℝ^n)}

/--
Higher-order recovery of one pure normal derivative after the normal flux
has been differentiated.

No regularity of `du` beyond `L2` is assumed.  The conclusion constructs its
`H^r` representative from the `H^r` normal derivative of the diagonal flux.
-/
theorem exists_pureNormalHigher_representative_of_diagonalFluxDerivative_of_reciprocal
    (hr : 0 < r)
    (hOmegaOpen : IsOpen Omega)
    (normal : Fin n)
    (A : W^{r + 1,∞}(Omega))
    (a : ℝ^n → ℝ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hpositive :
      ∀ᵐ x ∂domainMeasure n Omega, delta ≤ a x)
    (hA :
      ((((A : WkpAmbientOn n (r + 1) ∞ Omega)
        (baseIndex n (r + 1)) : DerivLp n ∞ Omega) :
          ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] a)
    (reciprocal : W^{r,∞}(Omega))
    (hreciprocal :
      ((((reciprocal : WkpAmbientOn n r ∞ Omega)
        (baseIndex n r) : DerivLp n ∞ Omega) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] fun x ↦ (a x)⁻¹)
    (U : W^{r,2}(Omega))
    (du : DerivLp n 2 Omega)
    (hdu :
      HasWeakDerivativeOn (n := n) Omega [normal]
        ((((U : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
          DerivLp n 2 Omega) : ℝ^n → ℝ))
        (du : ℝ^n → ℝ))
    (Ddiag : W^{r,2}(Omega))
    (hdiag :
      HasWeakDerivativeOn (n := n) Omega [normal]
        (fun x ↦
          ((((A : WkpAmbientOn n (r + 1) ∞ Omega)
            (baseIndex n (r + 1)) : DerivLp n ∞ Omega) :
              ℝ^n → ℝ) x) *
          ((((U : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
            DerivLp n 2 Omega) : ℝ^n → ℝ) x))
        ((((Ddiag : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
          DerivLp n 2 Omega) : ℝ^n → ℝ))) :
    ∃ G : W^{r,2}(Omega),
      ((((G : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
        DerivLp n 2 Omega) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] (du : ℝ^n → ℝ) := by
  let A1 : W^{1,∞}(Omega) := lowerOrderCLM (n := n) (p := ∞) (Ω := Omega) (by omega) A
  let DAr : W^{r,∞}(Omega) := derivativeWordCLM (n := n) (m := r + 1) (r := r) (p := ∞)
    (Ω := Omega) [normal] (by simp [Nat.add_comm]) A
  have hDArBase : ((DAr : WkpAmbientOn n r ∞ Omega) (baseIndex n r) : DerivLp n ∞ Omega) =
      ((A1 : WkpAmbientOn n 1 ∞ Omega) (singleDerivIndex n normal) : DerivLp n ∞ Omega) :=
    Lp.ext (by simp [DAr, A1])
  have hraw := A1.hasWeakDerivativeOn_mul_W1Top_first hOmegaOpen normal _ du hdu
  rw [show ((A1 : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1) : DerivLp n ∞ Omega) =
    (A : WkpAmbientOn n (r + 1) ∞ Omega) (baseIndex n (r + 1)) by simp [A1]] at hraw
  let commutator : W^{r,2}(Omega) := wkTopProduct hr hOmegaOpen DAr U
  refine ⟨wkTopProduct hr hOmegaOpen reciprocal (Ddiag - commutator), ?_⟩
  filter_upwards [wkTopProduct_base_ae hr hOmegaOpen reciprocal (Ddiag - commutator),
    baseRepresentative_sub_ae Ddiag commutator, wkTopProduct_base_ae hr hOmegaOpen DAr U,
    hdiag.unique_ae hOmegaOpen hraw, hreciprocal, hA, hpositive]
    with x hG hsub hc hd hrec hAx hpos
  simp only [baseRepresentative] at hG hsub hc
  rw [hG, hsub, hc, hd, hrec, hDArBase, add_sub_cancel_right, hAx,
    inv_mul_cancel_left₀ (hdelta.trans_le hpos).ne']

/--
Bounded-domain form of pure-normal recovery. Boundedness places the
classical reciprocal in `W^{r,infinity}`.
-/
theorem exists_pureNormalHigher_representative_of_diagonalFluxDerivative
    (hr : 0 < r)
    (hOmegaOpen : IsOpen Omega)
    (hOmegaBounded : Bornology.IsBounded Omega)
    (normal : Fin n)
    (A : W^{r + 1,∞}(Omega))
    (a : ℝ^n → ℝ)
    (ha : ContDiff ℝ r a)
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hpositive :
      ∀ᵐ x ∂domainMeasure n Omega, delta ≤ a x)
    (hA :
      ((((A : WkpAmbientOn n (r + 1) ∞ Omega)
        (baseIndex n (r + 1)) : DerivLp n ∞ Omega) :
          ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] a)
    (U : W^{r,2}(Omega))
    (du : DerivLp n 2 Omega)
    (hdu :
      HasWeakDerivativeOn (n := n) Omega [normal]
        ((((U : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
          DerivLp n 2 Omega) : ℝ^n → ℝ))
        (du : ℝ^n → ℝ))
    (Ddiag : W^{r,2}(Omega))
    (hdiag :
      HasWeakDerivativeOn (n := n) Omega [normal]
        (fun x ↦
          ((((A : WkpAmbientOn n (r + 1) ∞ Omega)
            (baseIndex n (r + 1)) : DerivLp n ∞ Omega) :
              ℝ^n → ℝ) x) *
          ((((U : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
            DerivLp n 2 Omega) : ℝ^n → ℝ) x))
        ((((Ddiag : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
          DerivLp n 2 Omega) : ℝ^n → ℝ))) :
    ∃ G : W^{r,2}(Omega),
      ((((G : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
        DerivLp n 2 Omega) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] (du : ℝ^n → ℝ) := by
  obtain ⟨reciprocal, hreciprocal⟩ :=
    WkpSpaceOn.exists_reciprocal_of_contDiff_bounded hOmegaBounded a ha hdelta hpositive
  exact exists_pureNormalHigher_representative_of_diagonalFluxDerivative_of_reciprocal hr
    hOmegaOpen normal A a hdelta hpositive hA reciprocal hreciprocal U du hdu Ddiag hdiag

/--
Whole-domain pure-normal recovery when the normal coefficient is a smooth
compact perturbation of a constant.
-/
theorem exists_pureNormalHigher_representative_of_diagonalFluxDerivative_compactPerturbation
    (hr : 0 < r)
    (hOmegaOpen : IsOpen Omega)
    (normal : Fin n)
    (A : W^{r + 1,∞}(Omega))
    (a : ℝ^n → ℝ)
    (ha : ContDiff ℝ r a)
    (c : ℝ)
    (hcompact : HasCompactSupport (fun x ↦ a x - c))
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hpositive :
      ∀ᵐ x ∂domainMeasure n Omega, delta ≤ a x)
    (hA :
      ((((A : WkpAmbientOn n (r + 1) ∞ Omega)
        (baseIndex n (r + 1)) : DerivLp n ∞ Omega) :
          ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] a)
    (U : W^{r,2}(Omega))
    (du : DerivLp n 2 Omega)
    (hdu :
      HasWeakDerivativeOn (n := n) Omega [normal]
        ((((U : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
          DerivLp n 2 Omega) : ℝ^n → ℝ))
        (du : ℝ^n → ℝ))
    (Ddiag : W^{r,2}(Omega))
    (hdiag :
      HasWeakDerivativeOn (n := n) Omega [normal]
        (fun x ↦
          ((((A : WkpAmbientOn n (r + 1) ∞ Omega)
            (baseIndex n (r + 1)) : DerivLp n ∞ Omega) :
              ℝ^n → ℝ) x) *
          ((((U : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
            DerivLp n 2 Omega) : ℝ^n → ℝ) x))
        ((((Ddiag : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
          DerivLp n 2 Omega) : ℝ^n → ℝ))) :
    ∃ G : W^{r,2}(Omega),
      ((((G : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
        DerivLp n 2 Omega) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] (du : ℝ^n → ℝ) := by
  obtain ⟨reciprocal, hreciprocal⟩ :=
    WkpSpaceOn.exists_reciprocal_of_contDiff_compactPerturbation a ha c hcompact hdelta hpositive
  exact exists_pureNormalHigher_representative_of_diagonalFluxDerivative_of_reciprocal hr
    hOmegaOpen normal A a hdelta hpositive hA reciprocal hreciprocal U du hdu Ddiag hdiag

end SobolevSpace.GraphSpace.BoundaryRegularity
