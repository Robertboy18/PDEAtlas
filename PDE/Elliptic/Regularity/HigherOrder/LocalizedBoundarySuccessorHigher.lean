/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.HigherOrder.BoundaryData
import PDE.Elliptic.Regularity.HigherOrder.BoundarySuccessorHigher
import PDE.Elliptic.Regularity.HigherOrder.HalfSpaceHigher
import PDE.Spaces.Sobolev.Calculus.Composition.Reciprocal
public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace

/-!
# Localized higher-order boundary successor

Evans's boundary induction is local: steps 1-4 of his proof of §6.3.2, Theorem 5, work on the
half-ball (78). Our upper-half-space argument first constructs the tangential derivative
representatives and the differentiated total normal flux on the whole half-space. On an open bounded
patch inside that half-space, the canonical Sobolev restriction map transports those objects and
their weak-derivative identities. The bounded-domain coefficient division theorem then supplies the
missing pure normal derivative and assembles the next Sobolev order
(`exists_localizedBoundary_higherOrder_succOrder_upper_patch`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, steps 1-4 of the proof of Theorem 5, (78)-(94),
  pp. 341-343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {n r : ℕ} [Fact (0 < n)]

/--
Localize the upper-half-space boundary successor step to an open bounded
patch.

The normal coefficient has a global `C^r` representative which is uniformly
positive; only its almost-everywhere agreement with the Sobolev coefficient
is required on `Omega`.  No `W^{r+3,2}` regularity of the solution or any of
its derivatives is assumed.
-/
theorem exists_localizedBoundary_higherOrder_succOrder_upper_patch
    {Omega : Set (ℝ^n)}
    (hr : 0 < r)
    (hOmegaOpen : IsOpen Omega)
    (hOmegaBounded : Bornology.IsBounded Omega)
    (hOmegaUpper : Omega ⊆ HalfSpace.upper n)
    (A : Fin n → Fin n →
      W^{r + 2,∞}(HalfSpace.upper n))
    (F : W^{r + 1,2}(HalfSpace.upper n))
    (U : W^{r + 2,2}(HalfSpace.upper n))
    (htrace0 :
      lowerOrderCLM
          (n := n) (k := 1) (m := r + 2) (p := 2)
          (Ω := HalfSpace.upper n) (by omega) U ∈
        (h10SubmoduleOn
          (n := n) (Ω := HalfSpace.upper n)).toSubmodule)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := HalfSpace.upper n)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (r + 2) ∞ (HalfSpace.upper n))
          (baseIndex n (r + 2)) :
            DerivLp n ∞ (HalfSpace.upper n)))
      ((F : WkpAmbientOn n (r + 1) 2 (HalfSpace.upper n))
        (baseIndex n (r + 1)) : DerivLp n 2 (HalfSpace.upper n))
      ⟨lowerOrderCLM
          (n := n) (p := 2) (Ω := HalfSpace.upper n) (by omega) U,
        htrace0⟩)
    (hprevious :
      ∀ (G : W^{r,2}(HalfSpace.upper n))
        (v : H¹₀(HalfSpace.upper n)),
        IsWeakDivergenceSolution
          (n := n) (Ω := HalfSpace.upper n)
          (fun i j ↦
            ((lowerOrderCLM
                (n := n) (k := r + 1) (m := r + 2) (p := ∞)
                (Ω := HalfSpace.upper n) (by simp) (A i j) :
                  WkpAmbientOn n (r + 1) ∞ (HalfSpace.upper n))
              (baseIndex n (r + 1)) :
                DerivLp n ∞ (HalfSpace.upper n)))
          ((G : WkpAmbientOn n r 2 (HalfSpace.upper n))
            (baseIndex n r) : DerivLp n 2 (HalfSpace.upper n))
          v →
        ∃ V : W^{r + 2,2}(HalfSpace.upper n),
          ⇑((V : WkpAmbientOn n (r + 2) 2 (HalfSpace.upper n))
              (baseIndex n (r + 2)) : DerivLp n 2 (HalfSpace.upper n))
            =ᵐ[domainMeasure n (HalfSpace.upper n)]
              ⇑(((v : H¹(HalfSpace.upper n)) :
                WkpAmbientOn n 1 2 (HalfSpace.upper n))
                  (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n)))
    (aNormal : ℝ^n → ℝ)
    (haNormal : ContDiff ℝ r aNormal)
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hpositive : ∀ x, delta ≤ aNormal x)
    (hANormal :
      ((((A (PDE.Common.lastIndex (n := n)) (PDE.Common.lastIndex (n := n)) :
          WkpAmbientOn n (r + 2) ∞ (HalfSpace.upper n))
        (baseIndex n (r + 2)) :
          DerivLp n ∞ (HalfSpace.upper n)) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] aNormal) :
    ∃ W : W^{r + 3,2}(Omega),
      ⇑((W : WkpAmbientOn n (r + 3) 2 Omega)
          (baseIndex n (r + 3)) : DerivLp n 2 Omega)
        =ᵐ[domainMeasure n Omega]
          ⇑(((restrictCLM
              (n := n) (k := r + 2) (p := 2)
              hOmegaOpen.measurableSet hOmegaUpper U :
                W^{r + 2,2}(Omega)) :
              WkpAmbientOn n (r + 2) 2 Omega)
            (baseIndex n (r + 2)) : DerivLp n 2 Omega) := by
  classical
  let normal := PDE.Common.lastIndex (n := n)
  have hOmegaMeas : MeasurableSet Omega := hOmegaOpen.measurableSet
  obtain ⟨upperData⟩ :=
    exists_principal_higherOrder_boundary_successor_on_upper hr A F U htrace0 hu hprevious
  let UOmega : W^{r + 2,2}(Omega) :=
    restrictCLM (n := n) (k := r + 2) (p := 2) hOmegaMeas hOmegaUpper U
  let coefficientUpper (j : Fin n) : W^{r + 1,∞}(HalfSpace.upper n) := lowerOrderCLM (n := n)
    (k := r + 1) (m := r + 2) (p := ∞) (Ω := HalfSpace.upper n) (by omega) (A normal j)
  let coefficientOmega (j : Fin n) : W^{r + 1,∞}(Omega) :=
    restrictCLM (n := n) (k := r + 1) (p := ∞) hOmegaMeas hOmegaUpper (coefficientUpper j)
  obtain ⟨reciprocal, hreciprocal⟩ := WkpSpaceOn.exists_reciprocal_of_contDiff_bounded
    hOmegaBounded aNormal haNormal hdelta (ae_of_all _ hpositive)
  let data : BoundarySuccessorData r UOmega normal coefficientOmega :=
    { tangentialRepresentative := fun i hi ↦ restrictCLM (n := n) (k := r + 2) (p := 2) hOmegaMeas
        hOmegaUpper (upperData.tangentialRepresentative i hi)
      tangentialRepresentative_base_eq := fun i hi ↦ by
        simpa [UOmega, restrictAmbient_apply] using congrArg
          (restrictDerivLp (n := n) (p := (2 : ENNReal)) hOmegaUpper)
          (upperData.tangentialRepresentative_base_eq i hi)
      normalFluxDerivative :=
        { derivative := restrictCLM (n := n) (k := r) (p := 2) hOmegaMeas hOmegaUpper
            upperData.normalFluxDerivative.derivative
          derivative_spec := by
            refine (upperData.normalFluxDerivative.derivative_spec.mono hOmegaMeas
              hOmegaUpper).congr_ae ?_ (restrictCLM_apply_ae hOmegaMeas hOmegaUpper _ _).symm
            filter_upwards [ae_all_iff.2 fun j ↦ restrictCLM_apply_ae hOmegaMeas hOmegaUpper
                (coefficientUpper j) (baseIndex n (r + 1)),
              ae_all_iff.2 fun j ↦ restrictCLM_apply_ae hOmegaMeas hOmegaUpper U
                (secondDerivIndex n (r + 2) (by omega) normal j)] with x hA hU
            exact Finset.sum_congr rfl fun j _ ↦ congrArg₂ (· * ·) (hA j).symm (hU j).symm } }
  obtain ⟨W, hW⟩ := exists_boundary_higherOrder_succOrder hr hOmegaOpen UOmega normal
    coefficientOmega data aNormal hdelta (ae_of_all _ hpositive)
    ((restrictCLM_apply_ae hOmegaMeas hOmegaUpper (coefficientUpper normal) _).trans
      (by simpa [coefficientUpper, lowerOrderCLM_apply, normal] using hANormal))
    reciprocal hreciprocal
  exact ⟨W, by simpa [UOmega] using hW⟩

end SobolevSpace.GraphSpace.BoundaryRegularity
