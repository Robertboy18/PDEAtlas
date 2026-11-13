/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.HigherOrder.BoundaryData
import PDE.Elliptic.Regularity.Global.PrincipalHigher
import PDE.Elliptic.Regularity.HigherOrder.BoundarySuccessorHigher
import PDE.Elliptic.Regularity.HigherOrder.DifferentiatedEquation
import PDE.Elliptic.Regularity.HigherOrder.NormalFlux
import PDE.Spaces.Sobolev.Calculus.Composition.Reciprocal
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
import PDE.Spaces.Sobolev.Calculus.Product.HigherOrderOperator
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
import PDE.Spaces.Sobolev.GraphSpace.FiniteSums
public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
import PDE.Elliptic.Regularity.HigherOrder.BoundaryHigher

/-!
# Higher-order regularity on the upper half-space

We prove the inductive step of our version of Evans's §6.3.2, Theorem 5 (Higher boundary regularity)
on `Ω⁺ = {xₙ > 0}`, from `H^{r+2}` to `H^{r+3}` for `r > 0`, with the regularity theorem of the
preceding order as a hypothesis. There are two theorems.

`exists_principal_higherOrder_boundary_successor_on_upper` assembles the two induction components
into a `BoundarySuccessorData`: the preceding boundary theorem gives an `H^{r+2}` representative for
every tangential first derivative, and the differentiated equation for the normal first derivative
together with the divergence identity gives an `H^r` normal derivative of its normal flux. The
division by `aₙₙ` is not done there.

`exists_principal_higherOrder_succ_upper_of_previous_compactPerturbation` does the division on the
whole half-space, and needs one hypothesis that Evans does not state because his domain is bounded:
the normal coefficient is a `C^r` compactly supported perturbation of a constant and is bounded
below by a positive constant. That is what makes its Sobolev reciprocal exist on an unbounded domain
(`WkpSpaceOn.exists_reciprocal_of_contDiff_compactPerturbation`). On a bounded patch the same step
is `exists_localizedBoundary_higherOrder_succOrder_upper_patch`, with no perturbation hypothesis.

## How it works

Evans works on the half-ball (78). In step 3 he applies the `H²` estimate to the tangential
derivatives `D^α u` with `|α| = m + 1`, which controls every derivative of order `m + 3` with at
most two normal derivatives, (90). In step 4 he recovers the remaining normal derivatives one at a
time from `D^γ Lu = D^γ f`, dividing by `aⁿⁿ ≥ θ > 0`. We raise the order by one at each step. One
tangential derivative and the preceding-order theorem give all derivatives of the next order with a
tangential index, and the differentiated normal flux, divided by the normal coefficient, gives the
pure normal derivative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 5 (Higher boundary regularity) and steps 1-4
  of its proof, (78)-(94), pp. 340-343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {n r : ℕ} [Fact (0 < n)]

/--
The arbitrary-order upper-half-space tangential and normal-flux data,
conditional on the preceding-order boundary theorem `hprevious`.

For positive `r`, the preceding `H^r -> H^{r+2}` boundary theorem first
promotes every tangential derivative of `U`.  Those representatives make
all matching tangential derivatives of the flux of `D_normal U` into
`H^r` fields.  The weak divergence equation then recovers the normal
derivative of the normal flux in `H^r`.

This is precisely the input to the coefficient-division and pure-normal
derivative assembly used by the arbitrary-order boundary induction.
-/
theorem exists_principal_higherOrder_boundary_successor_on_upper
    (hr : 0 < r)
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
          (n := n) (k := 1) (m := r + 2) (p := 2)
          (Ω := HalfSpace.upper n) (by omega) U,
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
                  (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n))) :
    Nonempty
      (BoundarySuccessorData r U
        (PDE.Common.lastIndex (n := n))
        (fun j ↦
          lowerOrderCLM
            (n := n) (k := r + 1) (m := r + 2) (p := ∞)
            (Ω := HalfSpace.upper n) (by omega)
            (A (PDE.Common.lastIndex (n := n)) j))) := by
  classical
  let Ω := HalfSpace.upper n
  let hΩopen := HalfSpace.isOpen_upper (n := n)
  let normal := PDE.Common.lastIndex (n := n)
  let coeff : Fin n → Fin n → DerivLp n ∞ Ω := fun i j ↦
    ((A i j : WkpAmbientOn n (r + 2) ∞ Ω) (baseIndex n (r + 2)) : DerivLp n ∞ Ω)
  let f0 : ℝ^n → ℝ := ((U : WkpAmbientOn n (r + 2) 2 Ω) (baseIndex n (r + 2)) : DerivLp n 2 Ω)
  let w : H¹(Ω) :=
    derivativeWordCLM (n := n) (m := r + 2) (r := 1) (p := 2) (Ω := Ω) [normal] (by simp) U
  let dw : Fin n → DerivLp n 2 Ω := fun j ↦ (w : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n j)
  let A1 (i j : Fin n) : W^{1,∞}(Ω) := lowerOrderCLM (n := n) (p := ∞) (Ω := Ω) (by omega) (A i j)
  let Ar (i j : Fin n) : W^{r,∞}(Ω) := lowerOrderCLM (n := n) (p := ∞) (Ω := Ω) (by omega) (A i j)
  let DAr (i j k : Fin n) : W^{r,∞}(Ω) := derivativeWordCLM (n := n) (m := r + 2) (r := r)
    (p := ∞) (Ω := Ω) [k] (by simp only [List.length_singleton]; omega) (A i j)
  let S (j : Fin n) : W^{r,2}(Ω) := derivativeWordCLM (n := n) (m := r + 2) (r := r) (p := 2)
    (Ω := Ω) [normal, j] (by simp only [List.length_cons, List.length_nil]; omega) U
  choose V hV using fun i : Fin n ↦ fun hi : i ≠ normal ↦
    exists_principal_higherOrder_tangential_of_previous_upper
      A F U i (by simpa [normal] using hi) htrace0 hu hprevious
  have hVeq (i : Fin n) (hi : i ≠ normal) :
      ((V i hi : WkpAmbientOn n (r + 2) 2 Ω) (baseIndex n (r + 2)) : DerivLp n 2 Ω) =
        ((U : WkpAmbientOn n (r + 2) 2 Ω) (firstDerivIndex n (r + 2) (by omega) i) :
          DerivLp n 2 Ω) :=
    Lp.ext (by simpa [Ω, normal] using hV i hi)
  have hfirstV (i : Fin n) (hi : i ≠ normal) :
      HasWeakDerivativeOn (n := n) Ω [i] f0
        (((V i hi : WkpAmbientOn n (r + 2) 2 Ω) (baseIndex n (r + 2)) : DerivLp n 2 Ω) :
          ℝ^n → ℝ) := by
    rw [hVeq i hi]
    simpa [f0] using U.property.hasWeakDerivativeOn_first (by omega) i
  have hprefix (j : Fin n) : HasWeakDerivativeOn (n := n) Ω [normal, j] f0 (dw j : ℝ^n → ℝ) := by
    simpa [f0, dw, w] using U.property.hasWeakDerivativeOn_list [normal, j] (by simp)
  have hSBase (j : Fin n) :
      ((S j : WkpAmbientOn n r 2 Ω) (baseIndex n r) : DerivLp n 2 Ω) = dw j :=
    Lp.ext (by simp [S, dw, w])
  have hArBase (i j : Fin n) :
      ((Ar i j : WkpAmbientOn n r ∞ Ω) (baseIndex n r) : DerivLp n ∞ Ω) = coeff i j := by
    simp [Ar, coeff]
  have hDArBase (i j k : Fin n) :
      ((DAr i j k : WkpAmbientOn n r ∞ Ω) (baseIndex n r) : DerivLp n ∞ Ω) =
        ((A1 i j : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n k) : DerivLp n ∞ Ω) :=
    Lp.ext (by simp [DAr, A1])
  let Dtan (i : Fin n) (hi : i ≠ normal) (j : Fin n) : W^{r,2}(Ω) :=
    derivativeWordCLM (n := n) (m := r + 2) (r := r) (p := 2) (Ω := Ω) [normal, j]
      (by simp only [List.length_cons, List.length_nil]; omega) (V i hi)
  have hdwTangential (i : Fin n) (hi : i ≠ normal) (j : Fin n) :
      HasWeakDerivativeOn (n := n) Ω [i] (dw j : ℝ^n → ℝ) (baseRepresentative (Dtan i hi j)) := by
    simpa [Dtan, secondDerivIndex, baseRepresentative] using
      (hprefix j).cancel_prefix_append_single i
      ((HasWeakDerivativeOn.append_from_wkp (V i hi) [i] [normal, j] (by simp)
        (hfirstV i hi)).perm List.perm_append_comm)
  let Dterm (i : Fin n) (hi : i ≠ normal) (j : Fin n) : W^{r,2}(Ω) :=
    wkTopProduct (n := n) (Ω := Ω) hr hΩopen (Ar i j) (Dtan i hi j) +
      wkTopProduct (n := n) (Ω := Ω) hr hΩopen (DAr i j i) (S j)
  have htermWeak (i : Fin n) (hi : i ≠ normal) (j : Fin n) :
      HasWeakDerivativeOn (n := n) Ω [i]
        (fun x ↦ (coeff i j : ℝ^n → ℝ) x * (dw j : ℝ^n → ℝ) x)
        (baseRepresentative (Dterm i hi j)) := by
    have hD : baseRepresentative (Dterm i hi j) =ᵐ[domainMeasure n Ω] fun x ↦
        (coeff i j : ℝ^n → ℝ) x * baseRepresentative (Dtan i hi j) x +
          (((A1 i j : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) : DerivLp n ∞ Ω) :
            ℝ^n → ℝ) x * (dw j : ℝ^n → ℝ) x := by
      filter_upwards [baseRepresentative_add_ae (wkTopProduct (n := n) (Ω := Ω) hr hΩopen
          (Ar i j) (Dtan i hi j)) (wkTopProduct (n := n) (Ω := Ω) hr hΩopen (DAr i j i) (S j)),
        wkTopProduct_base_ae hr hΩopen (Ar i j) (Dtan i hi j),
        wkTopProduct_base_ae hr hΩopen (DAr i j i) (S j)] with x h1 h2 h3
      refine h1.trans ?_
      rw [h2, h3]
      simp only [baseRepresentative, hArBase, hDArBase, hSBase]
    refine HasWeakDerivativeOn.congr_ae ?_ .rfl hD.symm
    simpa [A1, coeff, baseRepresentative] using
      (A1 i j).hasWeakDerivativeOn_mul_W1Top_first hΩopen i (dw j) _ (hdwTangential i hi j)
  let q : Fin n → DerivLp n 2 Ω := fun i ↦ ∑ j : Fin n, coeff i j • dw j
  let Dq (i : Fin n) : W^{r,2}(Ω) := if hi : i ≠ normal then ∑ j : Fin n, Dterm i hi j else 0
  obtain ⟨forcing, hidentity⟩ := exists_coordinateDerivative_higherOrder_weakEquation_identity
    hΩopen A F U normal (by simpa using htrace0) (by simpa using hu)
  obtain ⟨normalFluxData⟩ := normalFlux.exists_normalDerivative_of_weakDivergence q forcing Dq
    (fun φ hφ ↦ sum_integral_fluxRow_mul_iteratedPartialDeriv coeff dw _ φ (by
      simpa [Ω, normal, coeff, dw, w, iteratedPartialDeriv] using
        hidentity (⟨φ, hφ⟩ : TestFunctionOn n Ω)))
    fun i hi ↦ by
      have hi' : i ≠ normal := by simpa [normal] using hi
      rw [show Dq i = ∑ j, Dterm i hi' j by simp [Dq, hi']]
      exact (hasWeakDerivativeOn_finsetSum _ _ (fun j ↦ baseRepresentative (Dterm i hi' j)) [i]
        fun j _ ↦ htermWeak i hi' j).congr_ae (fluxRow_coeFn_ae coeff dw i).symm
          (baseRepresentative_sum_ae _).symm
  refine ⟨
    { tangentialRepresentative := V
      tangentialRepresentative_base_eq := fun i hi ↦ by
        simpa [Ω, normal] using hVeq i (by simpa [normal] using hi)
      normalFluxDerivative :=
        { derivative := normalFluxData.derivative
          derivative_spec := ?_ } }⟩
  simpa [lowerOrderCLM_apply, Ω, normal, q, coeff, dw, w, secondDerivIndex] using
    normalFluxData.derivative_spec.congr_ae (fluxRow_coeFn_ae coeff dw normal) .rfl

/--
Whole-half-space successor for the boundary induction.

The hypothesis `hprevious` is the preceding-order regularity theorem.
The only additional global input is that the positive normal coefficient is
a smooth compact perturbation of a constant. This supplies its Sobolev
reciprocal on the unbounded half-space and lets the domain-independent
boundary assembly return the next order globally.
-/
theorem exists_principal_higherOrder_succ_upper_of_previous_compactPerturbation
    (hr : 0 < r)
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
          (n := n) (k := 1) (m := r + 2) (p := 2)
          (Ω := HalfSpace.upper n) (by omega) U,
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
    (c : ℝ)
    (hcompact : HasCompactSupport (fun x ↦ aNormal x - c))
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hpositive :
      ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
        delta ≤ aNormal x)
    (hANormal :
      ((((A (PDE.Common.lastIndex (n := n)) (PDE.Common.lastIndex (n := n)) :
          WkpAmbientOn n (r + 2) ∞ (HalfSpace.upper n))
        (baseIndex n (r + 2)) :
          DerivLp n ∞ (HalfSpace.upper n)) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n (HalfSpace.upper n)] aNormal) :
    ∃ W : W^{r + 3,2}(HalfSpace.upper n),
      ⇑((W : WkpAmbientOn n (r + 3) 2 (HalfSpace.upper n))
          (baseIndex n (r + 3)) :
            DerivLp n 2 (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          ⇑((U : WkpAmbientOn n (r + 2) 2 (HalfSpace.upper n))
            (baseIndex n (r + 2)) :
              DerivLp n 2 (HalfSpace.upper n)) := by
  obtain ⟨data⟩ :=
    exists_principal_higherOrder_boundary_successor_on_upper hr A F U htrace0 hu hprevious
  obtain ⟨reciprocal, hreciprocal⟩ := WkpSpaceOn.exists_reciprocal_of_contDiff_compactPerturbation
    aNormal haNormal c hcompact hdelta hpositive
  exact exists_boundary_higherOrder_succOrder hr (HalfSpace.isOpen_upper (n := n)) U _ _ data
    aNormal hdelta hpositive
    (by simpa only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex] using hANormal)
    reciprocal hreciprocal

end SobolevSpace.GraphSpace.BoundaryRegularity
