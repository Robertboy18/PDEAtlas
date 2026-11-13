/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace

/-!
# Divergence-form flux on the flattened half-space

For a weak solution `u ∈ H¹₀` of `-∂ᵢ(aⁱʲ ∂ⱼ u) = f` on the upper half-space with `L∞`
coefficients, the flux rows `qᵢ = ∑ⱼ aⁱʲ ∂ⱼ u` are `L²` functions. We regard each row as
an element of `L²` and show that the variational weak equation

`∑ᵢⱼ ∫ aⁱʲ ∂ⱼ u ∂ᵢ φ = ∫ f φ` for all `φ ∈ H¹₀`

is the same as the distributional weak-divergence identity `∑ᵢ ∫ qᵢ ∂ᵢ φ = ∫ f φ` for test
functions `φ` supported in the half-space. That identity is the input to our normal-flux recovery
in `NormalFlux`, which replaces the nondivergence form (52)-(53) of the equation used in step 5
of Evans's proof of §6.3.2, Theorem 4.

## Main results

* `divergenceFluxL2`: the `i`-th flux row `∑ⱼ A i j • ∂ⱼ u` as an `L²` element.
* `divergenceFluxL2.apply_ae`: it is represented almost everywhere by the pointwise finite sum.
* `divergenceFluxL2.weakDivergence`: a variational weak solution satisfies the distributional
  divergence identity `∑ᵢ ∫ qᵢ ∂ᵢ φ = ∫ f φ` for every test function supported in the
  half-space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 5 of the proof of Theorem 4, (52)-(53),
  pp. 336-337.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace GraphSpace.BoundaryRegularity

variable {n : ℕ}

private theorem fintypeSumL2_apply_ae
    {ι : Type*} [Fintype ι]
    {S : Set (ℝ^n)} (F : ι → DerivLp n 2 S) :
    (((∑ i, F i) : DerivLp n 2 S) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n S] fun x ↦ ∑ i, (F i : ℝ^n → ℝ) x := by
  classical
  let s : Finset ι := Finset.univ
  have hsum :
      (((∑ i ∈ s, F i) : DerivLp n 2 S) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n S] fun x ↦ ∑ i ∈ s, (F i : ℝ^n → ℝ) x := by
    induction s using Finset.induction_on with
    | empty =>
        change ((0 : DerivLp n 2 S) : ℝ^n → ℝ)
          =ᵐ[domainMeasure n S] fun _ ↦ 0
        filter_upwards [
          MeasureTheory.Lp.coeFn_zero ℝ (2 : ENNReal) (domainMeasure n S)
        ] with x hx
        simpa only [Pi.zero_apply] using hx
    | @insert a s ha ih =>
        have hadd := MeasureTheory.Lp.coeFn_add (F a) (∑ i ∈ s, F i)
        filter_upwards [hadd, ih] with x hxadd hxsum
        simp only [Finset.sum_insert ha]
        rw [hxadd]
        simp only [Pi.add_apply]
        rw [hxsum]
  simpa [s] using hsum

/-- The `i`-th divergence-form flux row
`qᵢ = Σⱼ Aᵢⱼ ∂ⱼu`, represented as an `L²` function. -/
noncomputable def divergenceFluxL2
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (i : Fin n) : DerivLp n 2 (HalfSpace.upper n) :=
  ∑ j : Fin n, A i j •
    derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u

/-- The `L²` flux agrees almost everywhere with the standard finite-sum
representative. -/
theorem divergenceFluxL2.apply_ae
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (i : Fin n) :
    (divergenceFluxL2 A u i : ℝ^n → ℝ) =ᵐ[
        domainMeasure n (HalfSpace.upper n)]
      fun x ↦ ∑ j : Fin n, (A i j : ℝ^n → ℝ) x *
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u : ℝ^n → ℝ) x := by
  let du : Fin n → DerivLp n 2 (HalfSpace.upper n) := fun j ↦
    derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u
  have hsum := fintypeSumL2_apply_ae (n := n)
    (fun j : Fin n ↦ A i j • du j)
  have hterm (j : Fin n) :
      ((A i j • du j : DerivLp n 2 (HalfSpace.upper n)) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          fun x ↦ (A i j : ℝ^n → ℝ) x * (du j : ℝ^n → ℝ) x := by
    filter_upwards [
      MeasureTheory.Lp.coeFn_lpSMul (r := (2 : ENNReal)) (A i j) (du j)
    ] with x hx
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply] using hx
  filter_upwards [hsum, ae_all_iff.2 hterm] with x hx hterms
  rw [show divergenceFluxL2 A u i = ∑ j : Fin n, A i j • du j by
    rfl, hx]
  apply Finset.sum_congr rfl
  intro j _
  rw [hterms j]

private theorem memLp_fluxTerm
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (i j : Fin n) :
    MemLp
      (fun x ↦ (A i j : ℝ^n → ℝ) x *
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u : ℝ^n → ℝ) x)
      2 (domainMeasure n (HalfSpace.upper n)) := by
  exact (MeasureTheory.Lp.memLp (A i j)).fun_mul
    (MeasureTheory.Lp.memLp
      (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u))

private theorem integrable_fluxTerm_mul_iteratedPartialDeriv
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i j : Fin n) :
    Integrable
      (fun x ↦ (A i j : ℝ^n → ℝ) x *
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u : ℝ^n → ℝ) x *
        iteratedPartialDeriv (n := n) [i] φ.toFun x)
      (domainMeasure n (HalfSpace.upper n)) := by
  have hmem := memLp_fluxTerm A u i j
  have hlocal := hmem.locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  let dφ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) φ
  have hdφ_toFun : dφ.toFun =
      fun x ↦ iteratedPartialDeriv (n := n) [i] φ.toFun x := by
    funext x
    change (_root_.TestFunction.lineDerivCLM ℝ
        (EuclideanSpace.single i (1 : ℝ)) φ :
      𝓓((⊤ : Opens (ℝ^n)), ℝ)) x =
        iteratedPartialDeriv (n := n) [i] φ.toFun x
    rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [(φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  have hint := hlocal.integrable_smul_left_of_hasCompactSupport
    dφ.contDiff.continuous dφ.hasCompactSupport
  have hintegrand :
      (fun x ↦ (A i j : ℝ^n → ℝ) x *
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u : ℝ^n → ℝ) x *
        iteratedPartialDeriv (n := n) [i] φ.toFun x) =
      fun x ↦ dφ x • ((A i j : ℝ^n → ℝ) x *
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u : ℝ^n → ℝ) x) := by
    funext x
    rw [← congrFun hdφ_toFun x]
    rw [TestFunction.toFun_eq_coe]
    simp only [smul_eq_mul]
    ring
  rw [hintegrand]
  exact hint

/-- The variational weak equation is exactly the distributional divergence
identity for the flux rows. -/
theorem divergenceFluxL2.weakDivergence
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u) :
    ∀ (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)),
      tsupport φ.toFun ⊆ HalfSpace.upper n →
        (∑ i : Fin n,
          ∫ x, (divergenceFluxL2 A u i : ℝ^n → ℝ) x *
            iteratedPartialDeriv (n := n) [i] φ.toFun x
            ∂domainMeasure n (HalfSpace.upper n)) =
          ∫ x, (f : ℝ^n → ℝ) x * φ.toFun x
            ∂domainMeasure n (HalfSpace.upper n) := by
  intro φ hφ
  have hraw :=
    (isWeakSolution_iff_isWeakDivergenceSolution
      (n := n) (Ω := HalfSpace.upper n)
      (HalfSpace.isOpen_upper (n := n)) A f u).1 hu
      ⟨φ, hφ⟩
  have hrow (i : Fin n) :
      (∫ x, (divergenceFluxL2 A u i : ℝ^n → ℝ) x *
          iteratedPartialDeriv (n := n) [i] φ.toFun x
          ∂domainMeasure n (HalfSpace.upper n)) =
        ∑ j : Fin n,
          ∫ x, (A i j : ℝ^n → ℝ) x *
            (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u : ℝ^n → ℝ) x *
            iteratedPartialDeriv (n := n) [i] φ.toFun x
            ∂domainMeasure n (HalfSpace.upper n) := by
    rw [integral_congr_ae (by
      filter_upwards [divergenceFluxL2.apply_ae A u i] with x hx
      rw [hx, Finset.sum_mul])]
    exact integral_finsetSum Finset.univ fun j _ ↦
      integrable_fluxTerm_mul_iteratedPartialDeriv A u φ i j
  calc
    (∑ i : Fin n,
        ∫ x, (divergenceFluxL2 A u i : ℝ^n → ℝ) x *
          iteratedPartialDeriv (n := n) [i] φ.toFun x
          ∂domainMeasure n (HalfSpace.upper n)) =
      ∑ i : Fin n, ∑ j : Fin n,
        ∫ x, (A i j : ℝ^n → ℝ) x *
          (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u : ℝ^n → ℝ) x *
          iteratedPartialDeriv (n := n) [i] φ.toFun x
          ∂domainMeasure n (HalfSpace.upper n) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hrow i
    _ = ∫ x, (f : ℝ^n → ℝ) x * φ.toFun x
          ∂domainMeasure n (HalfSpace.upper n) := by
      simpa only [iteratedPartialDeriv] using hraw

end GraphSpace.BoundaryRegularity
end SobolevSpace
