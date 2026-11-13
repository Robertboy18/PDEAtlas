/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
import PDE.Elliptic.Regularity.Localization.CutoffEquation.Flux
import PDE.Elliptic.Regularity.Localization.CutoffEquation.ZeroBoundaryCutoff
public import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
public import PDE.Spaces.Sobolev.Localization.Cutoff.ZeroBoundary

/-!
# Localization of divergence-form weak equations

Let the coefficients `aᵢⱼ` lie in `W^{1,∞}(Ω)`, and let `u` be a weak solution of

`-∂ᵢ (aᵢⱼ ∂ⱼu) = f`

with `f ∈ L²(Ω)`. For a smooth cutoff `ρ`, `w = ρu` lies in `H¹₀(Ω)` and is a weak solution of the
same principal equation with the forcing

`g = ρf - aᵢⱼ (∂ⱼu) (∂ᵢρ) - ∂ᵢ (u aᵢⱼ ∂ⱼρ)`,

which lies in `L²(Ω)` and vanishes outside the support of `ρ`. For `u ∈ H¹₀(Ω)` every cutoff is
allowed (`exists_localized_weakDivergenceSolution`). For `u ∈ H¹(Ω)` that solves the equation
against all tests in `H¹₀(Ω)`, the cutoff must have support in `Ω`
(`exists_localized_interiorWeakDivergenceSolution`).

The last term of `g` is not assumed to lie in `L²`. The weak Leibniz rule
`W^{1,∞} · W^{1,2} ⊆ W^{1,2}` and smooth multiplication give the flux `u aᵢⱼ ∂ⱼρ` an `L²` weak
divergence (`exists_weakDerivative_cutoffFluxRowLp`), and `g` contains its Leibniz expansion.

## How it works

For `φ ∈ H¹₀(Ω)` we test the equation of `u` with `ρφ` (`cutoffH10`) and use the product rules for
`ρφ` and `ρu`; the term with `u ∂ⱼρ` is integrated by parts against `φ`
(`weakDerivative_integrationByParts_H10`). Evans localizes differently: in the proofs of §6.3.1,
Theorem 1, and §6.3.2, Theorem 4, the cutoff enters only through the test function
`v = -D_k^{-h}(ζ² D_k^h u)`, his (11) in §6.3.1, and the solution is not multiplied by a cutoff.
Putting the cutoff on the solution turns a local solution into a zero-trace one at the cost of the
forcing `g`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 1 (Interior H²-regularity), remark (i) after
  it, and its proof, (9)-(11), pp. 327-328; §6.3.2, proof of Theorem 4 (Boundary H²-regularity),
  steps 1-3, p. 335.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open SobolevSpace.CompactSupportLocalization
open scoped BigOperators Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Shared cutoff-equation computation for an `H¹` weak solution and an
`H¹₀` field whose derivative coordinates satisfy the cutoff product rule. -/
private theorem exists_localized_weakDivergenceSolution_core
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (u : H¹(Ω))
    (f : DerivLp n 2 Ω)
    (hu : IsInteriorWeakDivergenceSolution
      (n := n) (Ω := Ω)
      (fun i j ↦ ((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
        DerivLp n ∞ Ω)) f u)
    (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (w : H¹₀(Ω))
    (hwDerivCoord : ∀ j : Fin n,
      derivCoordCLM (n := n) (Ω := Ω) j w =
        testFunctionLpTop (n := n) (Ω := Ω) ρ •
            wkpCoordinateCLM
              (n := n) (m := 1) (p := 2) (Ω := Ω)
              (singleDerivIndex (n := n) j) u +
          partialTestFunctionLpTop (n := n) (Ω := Ω) ρ j •
            wkpBaseCoordinateCLM
              (n := n) (m := 1) (p := 2) (Ω := Ω) u) :
    ∃ g : DerivLp n 2 Ω,
      ((g : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        ρ.toFun x * (f : ℝ^n → ℝ) x -
          (∑ i : Fin n, ∑ j : Fin n,
            ((((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
              (wkpCoordinateCLM
                  (n := n) (m := 1) (p := 2) (Ω := Ω)
                  (singleDerivIndex (n := n) j) u : ℝ^n → ℝ) x *
              iteratedPartialDeriv (n := n) [i] ρ.toFun x)) -
          (∑ i : Fin n, ∑ j : Fin n,
            (iteratedPartialDeriv (n := n) [j] ρ.toFun x *
                (((((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                    DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
                  (wkpCoordinateCLM
                      (n := n) (m := 1) (p := 2) (Ω := Ω)
                      (singleDerivIndex (n := n) i) u :
                    ℝ^n → ℝ) x) +
                  ((((A i j : WkpAmbientOn n 1 ∞ Ω)
                    (singleDerivIndex n i) : DerivLp n ∞ Ω) :
                      ℝ^n → ℝ) x *
                    (wkpBaseCoordinateCLM
                        (n := n) (m := 1) (p := 2) (Ω := Ω) u :
                      ℝ^n → ℝ) x)) +
              iteratedPartialDeriv (n := n) [i, j] ρ.toFun x *
                ((((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                    DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
                  (wkpBaseCoordinateCLM
                      (n := n) (m := 1) (p := 2) (Ω := Ω) u :
                    ℝ^n → ℝ) x)))) ∧
      (tsupport ρ.toFun).indicator (g : ℝ^n → ℝ) =ᵐ[
        domainMeasure n Ω] (g : ℝ^n → ℝ) ∧
      IsWeakDivergenceSolution
        (n := n) (Ω := Ω)
        (fun i j ↦ ((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
          DerivLp n ∞ Ω)) g w := by
  classical
  let a : Fin n → Fin n → DerivLp n ∞ Ω := fun i j ↦
    ((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) : DerivLp n ∞ Ω)
  let r : DerivLp n ∞ Ω := testFunctionLpTop (n := n) (Ω := Ω) ρ
  let dr : Fin n → DerivLp n ∞ Ω := fun i ↦ partialTestFunctionLpTop (n := n) (Ω := Ω) ρ i
  let u0 : DerivLp n 2 Ω := wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Ω) u
  let du : Fin n → DerivLp n 2 Ω := fun i ↦
    wkpCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Ω) (singleDerivIndex (n := n) i) u
  have huDeriv (i : Fin n) :
      HasWeakDerivativeOn (n := n) Ω [i] (u0 : ℝ^n → ℝ) (du i : ℝ^n → ℝ) := by
    simpa [u0, du, wkpBaseCoordinateCLM, wkpCoordinateCLM, firstDerivIndex_one] using
      u.property.hasWeakDerivativeOn_first (by norm_num) i
  choose dq hdqWeak hdqAE using fun i ↦
    exists_weakDerivative_cutoffFluxRowLp hΩopen (A i) u0 (du i) i (huDeriv i) ρ
  let drift : DerivLp n 2 Ω := ∑ i : Fin n, ∑ j : Fin n, dr i • (a i j • du j)
  let divCorrection : DerivLp n 2 Ω := ∑ i : Fin n, dq i
  let g : DerivLp n 2 Ω := r • f - drift - divCorrection
  have hwWeak : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a))
      (loadFunctional (n := n) (Ω := Ω) g) w := by
    intro v
    let v0 : DerivLp n 2 Ω := baseCoordCLM (n := n) (Ω := Ω) v
    let dv : Fin n → DerivLp n 2 Ω := fun i ↦ derivCoordCLM (n := n) (Ω := Ω) i v
    let rv : H¹₀(Ω) := cutoffH10 hΩopen ρ v
    have huRv := hu.2 rv
    change (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (a i j • du j) (derivCoordCLM (n := n) (Ω := Ω) i rv)) =
      inner ℝ f (baseCoordCLM (n := n) (Ω := Ω) rv) at huRv
    have hrvBase : baseCoordCLM (n := n) (Ω := Ω) rv = r • v0 := by
      simpa [rv, r, v0] using baseCoordCLM_cutoffH10 hΩopen ρ v
    have hrvDeriv (i : Fin n) : derivCoordCLM (n := n) (Ω := Ω) i rv = r • dv i + dr i • v0 := by
      simpa [rv, r, dr, dv, v0] using derivCoordCLM_cutoffH10 hΩopen ρ v i
    simp only [hrvBase, hrvDeriv, inner_add_right, ← inner_lpSMul_left_eq_right,
      Finset.sum_add_distrib] at huRv
    have hQ (i : Fin n) : ∑ j, inner ℝ (a i j • (dr j • u0)) (dv i) = -inner ℝ (dq i) v0 := by
      have hc (j : Fin n) : a i j • (dr j • u0) = dr j • (a i j • u0) :=
        lpSMul_top_top_two_comm _ _ _
      simp only [hc, ← sum_inner]
      exact weakDerivative_integrationByParts_H10 i _ (dq i) (hdqWeak i) v
    have hc (i j : Fin n) : a i j • (r • du j) = r • (a i j • du j) :=
      lpSMul_top_top_two_comm _ _ _
    have hwDeriv (j : Fin n) : derivCoordCLM (n := n) (Ω := Ω) j w = r • du j + dr j • u0 :=
      hwDerivCoord j
    change (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (a i j • derivCoordCLM (n := n) (Ω := Ω) j w) (dv i)) = inner ℝ g v0
    simp only [hwDeriv, MeasureTheory.Lp.add_smul, inner_add_left, Finset.sum_add_distrib,
      hQ, hc, g, inner_sub_left, drift, divCorrection, sum_inner, Finset.sum_neg_distrib]
    linarith
  have hterm : ∀ᵐ x ∂domainMeasure n Ω, ∀ i j,
      ((dr i • (a i j • du j) : DerivLp n 2 Ω) : ℝ^n → ℝ) x =
        (a i j : ℝ^n → ℝ) x * (du j : ℝ^n → ℝ) x * iteratedPartialDeriv (n := n) [i] ρ.toFun x := by
    refine ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ ?_
    filter_upwards [partialTestFunctionLpTop_apply_ae (n := n) (Ω := Ω) ρ i,
      Lp.coeFn_lpSMul (r := 2) (a i j) (du j), Lp.coeFn_lpSMul (r := 2) (dr i) (a i j • du j)]
      with x hdx hix hox
    rw [hox, Pi.smul_apply', hix, Pi.smul_apply', hdx, smul_eq_mul, smul_eq_mul]
    ring
  have hgAE : (g : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
      ρ.toFun x * (f : ℝ^n → ℝ) x -
        (∑ i : Fin n, ∑ j : Fin n, (a i j : ℝ^n → ℝ) x * (du j : ℝ^n → ℝ) x *
          iteratedPartialDeriv (n := n) [i] ρ.toFun x) -
        (∑ i : Fin n, ∑ j : Fin n,
          (iteratedPartialDeriv (n := n) [j] ρ.toFun x *
              (((a i j : ℝ^n → ℝ) x * (du i : ℝ^n → ℝ) x) +
                ((((A i j : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) :
                  DerivLp n ∞ Ω) : ℝ^n → ℝ) x * (u0 : ℝ^n → ℝ) x)) +
            iteratedPartialDeriv (n := n) [i, j] ρ.toFun x *
              ((a i j : ℝ^n → ℝ) x * (u0 : ℝ^n → ℝ) x))) := by
    filter_upwards [Lp.coeFn_sub (r • f - drift) divCorrection, Lp.coeFn_sub (r • f) drift,
      Lp.coeFn_lpSMul (r := 2) r f, testFunctionLpTop_apply_ae (n := n) (Ω := Ω) ρ,
      Lp.coeFn_fun_finsetSum Finset.univ fun i ↦ ∑ j, dr i • (a i j • du j),
      ae_all_iff.2 fun i ↦ Lp.coeFn_fun_finsetSum Finset.univ fun j ↦ dr i • (a i j • du j),
      hterm, Lp.coeFn_fun_finsetSum Finset.univ dq, ae_all_iff.2 hdqAE]
      with x h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [show g = r • f - drift - divCorrection from rfl, h1, Pi.sub_apply, h2, Pi.sub_apply, h3,
      Pi.smul_apply', h4, smul_eq_mul, h5, h8]
    simp only [h6, h7, h9]
    rfl
  have hgSupport :
      (tsupport ρ.toFun).indicator (g : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (g : ℝ^n → ℝ) := by
    filter_upwards [hgAE] with x hx
    by_cases hxK : x ∈ tsupport ρ.toFun
    · exact Set.indicator_of_mem hxK _
    have hderiv (α : List (Fin n)) : iteratedPartialDeriv (n := n) α ρ.toFun x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦
        hxK (tsupport_iteratedPartialDeriv_subset_tsupport (n := n) α ρ.toFun h)
    rw [Set.indicator_of_notMem hxK, hx]
    simp only [hderiv, image_eq_zero_of_notMem_tsupport hxK]
    simp
  exact ⟨g, hgAE, hgSupport,
    (isWeakSolution_iff_isWeakDivergenceSolution (n := n) (Ω := Ω) hΩopen a g w).1 hwWeak⟩

/-- Convert an exact `L²` cutoff-coordinate identity into its pointwise
almost-everywhere representative. -/
private theorem baseCoordCLM_eq_cutoff_mul_ae
    (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (u0 : DerivLp n 2 Ω)
    (w : H¹₀(Ω))
    (hw : baseCoordCLM (n := n) (Ω := Ω) w =
      testFunctionLpTop (n := n) (Ω := Ω) ρ • u0) :
    ((baseCoordCLM (n := n) (Ω := Ω) w :
        ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω] fun x ↦
      ρ.toFun x * (u0 : ℝ^n → ℝ) x := by
  rw [hw]
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (testFunctionLpTop (n := n) (Ω := Ω) ρ) u0,
    testFunctionLpTop_apply_ae (n := n) (Ω := Ω) ρ] with x h1 h2
  rw [h1, Pi.smul_apply', h2, smul_eq_mul]

/-- Cutoff localization for zero-trace weak solutions.

Let the coefficient entries belong to `W^{1,∞}(Ω)`, and let `u ∈ H¹₀(Ω)`
solve `-∂ᵢ(aᵢⱼ∂ⱼu)=f`. For every smooth cutoff, this theorem constructs
`w=ρu` in `H¹₀(Ω)` and a scalar `g∈L²(Ω)` satisfying the localized
equation. No support condition on `ρ` is needed because `u` already has zero
trace. -/
theorem exists_localized_weakDivergenceSolution
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (u : H¹₀(Ω))
    (f : DerivLp n 2 Ω)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Ω)
      (fun i j ↦ ((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
        DerivLp n ∞ Ω)) f u)
    (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∃ w : H¹₀(Ω),
      ((baseCoordCLM (n := n) (Ω := Ω) w :
          ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        ρ.toFun x *
          (baseCoordCLM (n := n) (Ω := Ω) u :
            ℝ^n → ℝ) x) ∧
      ∃ g : DerivLp n 2 Ω,
        ((g : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
          ρ.toFun x * (f : ℝ^n → ℝ) x -
            (∑ i : Fin n, ∑ j : Fin n,
              ((((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                  DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
                (derivCoordCLM (n := n) (Ω := Ω) j u :
                  ℝ^n → ℝ) x *
                iteratedPartialDeriv (n := n) [i] ρ.toFun x)) -
            (∑ i : Fin n, ∑ j : Fin n,
              (iteratedPartialDeriv (n := n) [j] ρ.toFun x *
                  (((((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                      DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
                    (derivCoordCLM (n := n) (Ω := Ω) i u : ℝ^n → ℝ) x) +
                    ((((A i j : WkpAmbientOn n 1 ∞ Ω)
                      (singleDerivIndex n i) : DerivLp n ∞ Ω) :
                        ℝ^n → ℝ) x *
                      (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) x)) +
                iteratedPartialDeriv (n := n) [i, j] ρ.toFun x *
                  ((((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                      DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
                    (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) x)))) ∧
        (tsupport ρ.toFun).indicator (g : ℝ^n → ℝ) =ᵐ[
          domainMeasure n Ω] (g : ℝ^n → ℝ) ∧
        IsWeakDivergenceSolution
          (n := n) (Ω := Ω)
          (fun i j ↦ ((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
            DerivLp n ∞ Ω)) g w := by
  obtain ⟨g, hgAE, hgSupport, hgWeak⟩ := exists_localized_weakDivergenceSolution_core hΩopen A
    (h10SubtypeL (n := n) (Ω := Ω) u) f hu.toInterior ρ (cutoffH10 hΩopen ρ u) fun j ↦ by
      simpa only [wkpCoordinateCLM_h10SubtypeL, wkpBaseCoordinateCLM_h10SubtypeL] using
        derivCoordCLM_cutoffH10 hΩopen ρ u j
  refine ⟨_, ?_, g, by simpa only [wkpCoordinateCLM_h10SubtypeL,
    wkpBaseCoordinateCLM_h10SubtypeL] using hgAE, hgSupport, hgWeak⟩
  simpa only [wkpBaseCoordinateCLM_h10SubtypeL] using baseCoordCLM_eq_cutoff_mul_ae ρ
    (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Ω) (h10SubtypeL (n := n) (Ω := Ω) u))
    _ (by simpa only [wkpBaseCoordinateCLM_h10SubtypeL] using baseCoordCLM_cutoffH10 hΩopen ρ u)

/-- Interior cutoff localization for weak solutions without a boundary condition.

Let `u ∈ H¹(Ω)` solve the divergence-form equation against every
`H¹₀(Ω)` test. If the smooth cutoff is supported inside `Ω`, then `w=ρu`
belongs to `H¹₀(Ω)` and satisfies the same localized equation with the commutator
forcing of the statement. This is the localization step for interior regularity without a
trace condition on `u`; Evans's §6.3.1, Theorem 1, also assumes only `u ∈ H¹(U)`. -/
theorem exists_localized_interiorWeakDivergenceSolution
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (u : H¹(Ω))
    (f : DerivLp n 2 Ω)
    (hu : IsInteriorWeakDivergenceSolution
      (n := n) (Ω := Ω)
      (fun i j ↦ ((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
        DerivLp n ∞ Ω)) f u)
    (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hρΩ : tsupport ρ.toFun ⊆ Ω) :
    ∃ w : H¹₀(Ω),
      ((baseCoordCLM (n := n) (Ω := Ω) w :
          ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        ρ.toFun x *
          (wkpBaseCoordinateCLM
            (n := n) (m := 1) (p := 2) (Ω := Ω) u :
              ℝ^n → ℝ) x) ∧
      ∃ g : DerivLp n 2 Ω,
        ((g : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
          ρ.toFun x * (f : ℝ^n → ℝ) x -
            (∑ i : Fin n, ∑ j : Fin n,
              ((((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                  DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
                (wkpCoordinateCLM
                    (n := n) (m := 1) (p := 2) (Ω := Ω)
                    (singleDerivIndex (n := n) j) u :
                      ℝ^n → ℝ) x *
                iteratedPartialDeriv (n := n) [i] ρ.toFun x)) -
            (∑ i : Fin n, ∑ j : Fin n,
              (iteratedPartialDeriv (n := n) [j] ρ.toFun x *
                  (((((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                      DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
                    (wkpCoordinateCLM
                        (n := n) (m := 1) (p := 2) (Ω := Ω)
                        (singleDerivIndex (n := n) i) u :
                      ℝ^n → ℝ) x) +
                    ((((A i j : WkpAmbientOn n 1 ∞ Ω)
                      (singleDerivIndex n i) : DerivLp n ∞ Ω) :
                        ℝ^n → ℝ) x *
                      (wkpBaseCoordinateCLM
                          (n := n) (m := 1) (p := 2) (Ω := Ω) u :
                        ℝ^n → ℝ) x)) +
                iteratedPartialDeriv (n := n) [i, j] ρ.toFun x *
                  ((((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                      DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
                    (wkpBaseCoordinateCLM
                        (n := n) (m := 1) (p := 2) (Ω := Ω) u :
                      ℝ^n → ℝ) x)))) ∧
        (tsupport ρ.toFun).indicator (g : ℝ^n → ℝ) =ᵐ[
          domainMeasure n Ω] (g : ℝ^n → ℝ) ∧
        IsWeakDivergenceSolution
          (n := n) (Ω := Ω)
          (fun i j ↦ ((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
            DerivLp n ∞ Ω)) g w := by
  have hΩopen : IsOpen Ω := hu.isOpen
  obtain ⟨g, hgAE, hgSupport, hgWeak⟩ := exists_localized_weakDivergenceSolution_core hΩopen A u
    f hu ρ (cutoffH1ToH10 hΩopen ρ hρΩ u) fun j ↦ derivCoordCLM_cutoffH1ToH10 hΩopen ρ hρΩ u j
  exact ⟨_, baseCoordCLM_eq_cutoff_mul_ae ρ
    (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Ω) u) _
    (baseCoordCLM_cutoffH1ToH10 hΩopen ρ hρΩ u), g, hgAE, hgSupport, hgWeak⟩

end SobolevSpace.GraphSpace
