/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
import PDE.Elliptic.Regularity.Boundary.H2.NormalFluxRecovery.NormalFlux
import PDE.Elliptic.Regularity.HigherOrder.BoundaryDifferentiatedEquation
import PDE.Elliptic.Regularity.HigherOrder.DifferentiatedEquation
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
import PDE.Spaces.Sobolev.Calculus.Slicing.MissingCoordinate
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
public import PDE.Spaces.Sobolev.Calculus.Product.LipschitzCoefficient

/-!
# Third-order boundary regularity on the half-space

Qualitative `H³` regularity for the flattened Dirichlet problem on
`Ω⁺ = {xₙ > 0}`. Let `U ∈ H²(Ω⁺)` have zero trace and solve

`-∂ᵢ(aᵢⱼ ∂ⱼ U) = F` weakly in `Ω⁺`

with coefficients `aᵢⱼ ∈ W^{2,∞}(Ω⁺)` that are uniformly elliptic with
constant `α` and have Lipschitz representatives, and with `F ∈ H¹(Ω⁺)`. Then
`U` has a representative in `H³(Ω⁺)`.

This is the `m = 1` case of Evans's higher boundary regularity theorem
(§6.3.2, Theorem 5), on the whole half-space, with `W^{2,∞}` coefficient bundles `A i j` whose
Lipschitz representatives `a i j` carry the constants `C i j`; the conclusion is
membership in `H³`.
For each tangential direction `k ≠ n` the derivative `∂ₖ U` again has zero
trace and solves a divergence-form equation with `L²` forcing, so the boundary
`H²` theorem (`exists_flattened_h2_tangentialCoordinateDerivative_upper`)
gives `∂ₖ U ∈ H²(Ω⁺)`, which supplies every third derivative with at least one
tangential index. The pure normal derivative `∂ₙ³ U` is read off from the
equation: the normal derivative of the normal flux `∑ⱼ aₙⱼ ∂ⱼ U` is known
(`normalFlux.exists_weakDerivative_of_weakDivergence`), the cross terms
`aₙⱼ ∂ⱼ U` for `j ≠ n` already lie in `H¹`, and dividing by `aₙₙ ≥ α` is
`positiveReciprocalW1Top`.

## Main results

* `exists_flattened_h3_on_upper`: existence of `W ∈ H³(Ω⁺)` whose
  base function agrees almost everywhere with `U`.

## Implementation notes

The coefficients are carried as `W^{2,∞}` bundles; the weak equation only
sees their `L∞` base coordinates, and the Lipschitz representatives `a i j`
are the form in which the commutator bound of the `H²` step is stated.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 5 (Higher boundary regularity) with `m = 1`
  and steps 2-4 of its proof, (79)-(94), pp. 340-343.
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

variable {n : ℕ} [Fact (0 < n)]

/--
Qualitative `H³` regularity for the flattened Dirichlet problem.

The tangential derivatives gain `H²` regularity from the differentiated weak
equations.  Differentiating the normal equation as a distribution then
recovers the normal derivative of its normal flux.  Subtracting the
tangential cross-flux and dividing by the uniformly positive normal
coefficient gives the remaining pure normal third derivative.
-/
theorem exists_flattened_h3_on_upper
    (A : Fin n → Fin n →
      W^{2,∞}(HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 2 ∞ (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n ∞ (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic
      (n := n) (Ω := HalfSpace.upper n)
      (fun i j ↦
        ((A i j : WkpAmbientOn n 2 ∞ (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n ∞ (HalfSpace.upper n)))
      alpha)
    (halpha : 0 < alpha)
    (F : W^{1,2}(HalfSpace.upper n))
    (U : W^{2,2}(HalfSpace.upper n))
    (htrace0 :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2)
          (Ω := HalfSpace.upper n) (by norm_num) U ∈
        (h10SubmoduleOn
          (n := n) (Ω := HalfSpace.upper n)).toSubmodule)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := HalfSpace.upper n)
      (fun i j ↦
        ((A i j : WkpAmbientOn n 2 ∞ (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n ∞ (HalfSpace.upper n)))
      ((F : WkpAmbientOn n 1 2 (HalfSpace.upper n))
        (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n))
      ⟨lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2)
          (Ω := HalfSpace.upper n) (by norm_num) U,
        htrace0⟩) :
    ∃ W : W^{3,2}(HalfSpace.upper n),
      baseRepresentative W =ᵐ[domainMeasure n (HalfSpace.upper n)]
        (fun x ↦
          ⇑((U : WkpAmbientOn n 2 2 (HalfSpace.upper n))
            (baseIndex n 2) : DerivLp n 2 (HalfSpace.upper n)) x) := by
  classical
  let Ω := HalfSpace.upper n
  have hΩ := HalfSpace.isOpen_upper (n := n)
  let normal := PDE.Common.lastIndex (n := n)
  let coeff : Fin n → Fin n → DerivLp n ∞ Ω := fun i j ↦
    ((A i j : WkpAmbientOn n 2 ∞ Ω) (baseIndex n 2) : DerivLp n ∞ Ω)
  let f0 : ℝ^n → ℝ := ((U : WkpAmbientOn n 2 2 Ω) (baseIndex n 2) : DerivLp n 2 Ω)
  let w : H¹(Ω) :=
    derivativeWordCLM (n := n) (m := 2) (r := 1) (p := 2) (Ω := Ω) [normal] (by simp) U
  let dw : Fin n → DerivLp n 2 Ω := fun j ↦ (w : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n j)
  obtain ⟨forcing, hidentity⟩ :=
    exists_coordinateDerivative_l2_weakEquation_identity hΩ A F U normal htrace0 hu
  choose V hV using fun i : Fin n ↦ fun hi : i ≠ normal ↦
    exists_flattened_h2_tangentialCoordinateDerivative_upper A a C haLip haRep hA halpha F U i
      (by simpa [normal] using hi) htrace0 hu
  have hVeq (i : Fin n) (hi : i ≠ normal) :
      ((V i hi : WkpAmbientOn n 2 2 Ω) (baseIndex n 2) : DerivLp n 2 Ω) =
        ((U : WkpAmbientOn n 2 2 Ω) (firstDerivIndex n 2 (by norm_num) i) : DerivLp n 2 Ω) :=
    Lp.ext (by simpa [Ω, normal] using hV i hi)
  have hfirstV (i : Fin n) (hi : i ≠ normal) :
      HasWeakDerivativeOn (n := n) Ω [i] f0
        (((V i hi : WkpAmbientOn n 2 2 Ω) (baseIndex n 2) : DerivLp n 2 Ω) : ℝ^n → ℝ) := by
    rw [hVeq i hi]
    simpa [f0] using U.property.hasWeakDerivativeOn_first (by norm_num) i
  have hprefix (j : Fin n) : HasWeakDerivativeOn (n := n) Ω [normal, j] f0 (dw j : ℝ^n → ℝ) := by
    simpa [f0, dw, w] using U.property.hasWeakDerivativeOn_list [normal, j] (by simp)
  have hdwTangential (i : Fin n) (hi : i ≠ normal) (j : Fin n) :
      HasWeakDerivativeOn (n := n) Ω [i] (dw j : ℝ^n → ℝ)
        (((V i hi : WkpAmbientOn n 2 2 Ω) (pairDerivIndex n normal j) : DerivLp n 2 Ω) :
          ℝ^n → ℝ) :=
    (hprefix j).cancel_prefix_append_single i
      ((HasWeakDerivativeOn.append_from_wkp (V i hi) [i] [normal, j] (by simp)
        (hfirstV i hi)).perm List.perm_append_comm)
  have hdwNormal (j : Fin n) (hj : j ≠ normal) :
      HasWeakDerivativeOn (n := n) Ω [normal] (dw j : ℝ^n → ℝ)
        (((V j hj : WkpAmbientOn n 2 2 Ω) (pairDerivIndex n normal normal) : DerivLp n 2 Ω) :
          ℝ^n → ℝ) :=
    (hprefix j).cancel_prefix_append_single normal
      ((HasWeakDerivativeOn.append_from_wkp (V j hj) [j] [normal, normal] (by simp)
        (hfirstV j hj)).perm (List.Perm.swap j normal [normal]).symm)
  let A0 (i j : Fin n) : W^{1,∞}(Ω) := lowerOrderCLM (n := n) (p := ∞) (Ω := Ω) (by omega) (A i j)
  let q : Fin n → DerivLp n 2 Ω := fun i ↦ ∑ j : Fin n, coeff i j • dw j
  choose dr hdr using fun (i : Fin n) (hi : i ≠ normal) (j : Fin n) ↦
    show ∃ r : DerivLp n 2 Ω, HasWeakDerivativeOn (n := n) Ω [i]
        (fun x ↦ (coeff i j : ℝ^n → ℝ) x * (dw j : ℝ^n → ℝ) x) (r : ℝ^n → ℝ) by
      simpa [A0, coeff] using
        (A0 i j).exists_weakDerivative_mul_W1Top_first hΩ i (dw j) _ (hdwTangential i hi j)
  let dq : Fin n → DerivLp n 2 Ω := fun i ↦ if hi : i ≠ normal then ∑ j, dr i hi j else 0
  obtain ⟨dqn, hdqn⟩ := normalFlux.exists_weakDerivative_of_weakDivergence q dq forcing
    (fun φ hφ ↦ sum_integral_fluxRow_mul_iteratedPartialDeriv coeff dw _ φ (by
      simpa [Ω, normal, coeff, dw, w, iteratedPartialDeriv] using
        hidentity (⟨φ, hφ⟩ : TestFunctionOn n Ω)))
    fun i hi ↦ by
      have hi' : i ≠ normal := by simpa [normal] using hi
      rw [show dq i = ∑ j, dr i hi' j by simp [dq, hi']]
      exact (hasWeakDerivativeOn_finsetSum Finset.univ _ _ [i] fun j _ ↦ hdr i hi' j).congr_ae
        (fluxRow_coeFn_ae coeff dw i).symm (Lp.coeFn_fun_finsetSum _ _).symm
  choose dc hdc using fun (j : Fin n) (hj : j ≠ normal) ↦
    show ∃ r : DerivLp n 2 Ω, HasWeakDerivativeOn (n := n) Ω [normal]
        (fun x ↦ (coeff normal j : ℝ^n → ℝ) x * (dw j : ℝ^n → ℝ) x) (r : ℝ^n → ℝ) by
      simpa [A0, coeff] using
        (A0 normal j).exists_weakDerivative_mul_W1Top_first hΩ normal (dw j) _ (hdwNormal j hj)
  let dcross : DerivLp n 2 Ω :=
    ∑ j ∈ Finset.univ.erase normal, if hj : j = normal then 0 else dc j hj
  have hcross : HasWeakDerivativeOn (n := n) Ω [normal]
      (fun x ↦ ∑ j ∈ Finset.univ.erase normal, (coeff normal j : ℝ^n → ℝ) x * (dw j : ℝ^n → ℝ) x)
      (dcross : ℝ^n → ℝ) :=
    (hasWeakDerivativeOn_finsetSum (Finset.univ.erase normal) _ _ [normal] fun j hj ↦ by
      simpa [Finset.ne_of_mem_erase hj] using hdc j (Finset.ne_of_mem_erase hj)).congr_ae
      .rfl (Lp.coeFn_fun_finsetSum _ _).symm
  let diag : DerivLp n 2 Ω := coeff normal normal • dw normal
  have hdiag : HasWeakDerivativeOn (n := n) Ω [normal] (diag : ℝ^n → ℝ)
      ((dqn - dcross : DerivLp n 2 Ω) : ℝ^n → ℝ) := by
    refine (hasWeakDerivativeOn_sub [normal] hdqn hcross).congr_ae ?_ (Lp.coeFn_sub _ _).symm
    filter_upwards [fluxRow_coeFn_ae coeff dw normal, Lp.coeFn_lpSMul (r := 2)
      (coeff normal normal) (dw normal)] with x hq hd
    rw [hq, hd, ← Finset.add_sum_erase _ _ (Finset.mem_univ normal), add_sub_cancel_right]
    rfl
  let reciprocal : W^{1,∞}(Ω) := positiveReciprocalW1Top (HalfSpace.measurableSet_upper (n := n))
    halpha (a normal normal) (C normal normal) (haLip normal normal)
  obtain ⟨g, hg⟩ := reciprocal.exists_weakDerivative_mul_W1Top_first hΩ normal diag _ hdiag
  have hrecover : (fun x ↦ (((reciprocal : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
      DerivLp n ∞ Ω) : ℝ^n → ℝ) x * (diag : ℝ^n → ℝ) x)
        =ᵐ[domainMeasure n Ω] (dw normal : ℝ^n → ℝ) := by
    filter_upwards [positiveReciprocalW1Top_base_ae (HalfSpace.measurableSet_upper (n := n))
      halpha (a normal normal) (C normal normal) (haLip normal normal),
      Lp.coeFn_lpSMul (r := 2) (coeff normal normal) (dw normal),
      haRep normal normal, aeUniformlyElliptic_diagonal_lower_bound coeff hA normal]
      with x hr hd hrep hpos
    have hpos : alpha ≤ a normal normal x := hpos.trans_eq hrep
    rw [hr, hd, Pi.smul_apply', smul_eq_mul, show (coeff normal normal : ℝ^n → ℝ) x = _ from hrep,
      positiveReciprocal_eq_inv hpos,
      inv_mul_cancel_left₀ (halpha.trans_le hpos).ne']
  obtain ⟨W, hW⟩ := exists_H3_of_H2_coordinateDerivatives_except_one U normal V hVeq g
    (by simpa [dw, w, pairDerivIndex, secondDerivIndex] using hg.congr_ae hrecover .rfl)
  exact ⟨W, by simpa [baseRepresentative, Ω] using hW⟩

end SobolevSpace.GraphSpace.BoundaryRegularity
