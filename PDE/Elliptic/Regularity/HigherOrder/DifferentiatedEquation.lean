/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Elliptic.Regularity.Boundary.Domain
import PDE.Elliptic.Regularity.Global.H2
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
public import PDE.Elliptic.Variational.DivergenceForm

/-!
# Differentiating divergence-form weak equations

We supply the distributional induction step used in higher elliptic
regularity.  Differentiating

`-∂ᵢ(aᵢⱼ ∂ⱼu) = f`

in direction `k` gives

`-∂ᵢ(aᵢⱼ ∂ⱼ∂ₖu) = ∂ₖf + ∂ᵢ((∂ₖaᵢⱼ) ∂ⱼu)`.

`IsWeakDivergenceSolution.coordinateDerivative` performs this calculation from
certified weak derivatives. The product derivatives are `L²` functions, so the
differentiated right-hand side is again an `L²` forcing term. This is the case
`|α| = 1` of the differentiated equation in step 3 of Evans's proof of §6.3.1,
Theorem 2, for an operator without lower-order terms.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, step 3 of the proof of Theorem 2, (33)-(37), p. 333.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {n : ℕ} {Ω : Set (ℝ^n)}

/--
One distributional coordinate derivative of a divergence-form weak equation.

The hypotheses `hflux` and `hcomm` are the two weak Leibniz certificates:

* `hflux` differentiates `aᵢⱼ ∂ⱼu` in direction `k`;
* `hcomm` differentiates `(∂ₖaᵢⱼ) ∂ⱼu` in direction `i`.

The latter derivative is represented by `dq i j ∈ L²`. These certificates
give the divergence identity for `w` with forcing `∂ₖf + ∑ᵢⱼ dqᵢⱼ`.
They do not separately assert that `w = ∂ₖu` or that `da` differentiates `a`;
`exists_coordinateDerivative_l2_weakEquation_identity` constructs the certificates
for those choices from Sobolev bundles. No boundary condition on `w` is needed
because the conclusion is tested only against compactly supported smooth functions.
-/
theorem IsWeakDivergenceSolution.coordinateDerivative
    (a da : Fin n → Fin n → DerivLp n ∞ Ω)
    (f df g : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (w : H¹(Ω))
    (k : Fin n)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Ω) a f u)
    (hf : HasWeakDerivativeOn (n := n) Ω [k]
      (f : ℝ^n → ℝ) (df : ℝ^n → ℝ))
    (hflux : ∀ i j,
      HasWeakDerivativeOn (n := n) Ω [k]
        (fun x ↦ (a i j : ℝ^n → ℝ) x *
          (derivCoordCLM (n := n) (Ω := Ω) j u :
            ℝ^n → ℝ) x)
        (fun x ↦
          (a i j : ℝ^n → ℝ) x *
              (((w : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n j) :
                DerivLp n 2 Ω) : ℝ^n → ℝ) x +
            (da i j : ℝ^n → ℝ) x *
              (derivCoordCLM (n := n) (Ω := Ω) j u :
                ℝ^n → ℝ) x))
    (dq : Fin n → Fin n → DerivLp n 2 Ω)
    (hcomm : ∀ i j,
      HasWeakDerivativeOn (n := n) Ω [i]
        (fun x ↦ (da i j : ℝ^n → ℝ) x *
          (derivCoordCLM (n := n) (Ω := Ω) j u :
            ℝ^n → ℝ) x)
        (dq i j : ℝ^n → ℝ))
    (hg : (g : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
      (df : ℝ^n → ℝ) x + ∑ i : Fin n, ∑ j : Fin n,
        (dq i j : ℝ^n → ℝ) x) :
    ∀ φ : TestFunctionOn n Ω,
      (∑ i : Fin n, ∑ j : Fin n,
        ∫ x, (a i j : ℝ^n → ℝ) x *
          (((w : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n j) :
            DerivLp n 2 Ω) : ℝ^n → ℝ) x *
          (∂[i] φ.1.toFun) x
        ∂domainMeasure n Ω) =
      ∫ x, (g : ℝ^n → ℝ) x * φ.1.toFun x
        ∂domainMeasure n Ω := by
  classical
  intro φ
  let ψ (i : Fin n) : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) φ.1
  have hψ (i : Fin n) : (ψ i).toFun = fun x ↦ (∂[i] φ.1.toFun) x := by
    funext x
    change ψ i x = _
    rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp),
      (φ.1.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  have hψΩ (i : Fin n) : tsupport (ψ i).toFun ⊆ Ω := by
    rw [hψ]
    simpa only [partialDeriv] using (tsupport_fderiv_apply_subset ℝ (f := φ.1.toFun) _).trans φ.2
  have hφLp : MemLp φ.1.toFun 2 (domainMeasure n Ω) :=
    φ.1.contDiff.continuous.memLp_of_hasCompactSupport φ.1.hasCompactSupport
  have hint (h : DerivLp n 2 Ω) :
      Integrable (fun x ↦ (h : ℝ^n → ℝ) x * φ.1.toFun x) (domainMeasure n Ω) :=
    memLp_one_iff_integrable.mp ((Lp.memLp h).fun_mul hφLp)
  have hint' (c : DerivLp n ∞ Ω) (v : DerivLp n 2 Ω) (i : Fin n) :
      Integrable (fun x ↦ (c : ℝ^n → ℝ) x * (v : ℝ^n → ℝ) x * (∂[i] φ.1.toFun) x)
        (domainMeasure n Ω) := by
    refine memLp_one_iff_integrable.mp
      (((Lp.memLp c).fun_mul (r := 2) (Lp.memLp v)).fun_mul (q := 2) ?_)
    have h := (ψ i).contDiff.continuous.memLp_of_hasCompactSupport (μ := domainMeasure n Ω)
      (p := 2) (ψ i).hasCompactSupport
    rwa [show ⇑(ψ i) = _ from hψ i] at h
  have hij (i j : Fin n) :
      ∫ x, (a i j : ℝ^n → ℝ) x * (derivCoordCLM (n := n) (Ω := Ω) j u : ℝ^n → ℝ) x *
          (∂[i] fun y ↦ (∂[k] φ.1.toFun) y) x ∂domainMeasure n Ω =
        -(∫ x, (a i j : ℝ^n → ℝ) x * (((w : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n j) :
          DerivLp n 2 Ω) : ℝ^n → ℝ) x * (∂[i] φ.1.toFun) x ∂domainMeasure n Ω) +
        ∫ x, (dq i j : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n Ω := by
    have h1 := hflux i j (ψ i) (hψΩ i)
    have h2 := hcomm i j φ.1 φ.2
    simp only [iteratedPartialDeriv, List.length_singleton, pow_one, neg_one_mul, add_mul,
      hψ] at h1 h2
    rw [integral_add (hint' _ _ i) (hint' _ _ i), h2] at h1
    simp only [PDE.partialDeriv_partialDeriv_comm (f := φ.1.toFun) i k
      (φ.1.contDiff.of_le (by simp))]
    rw [h1]
    ring
  have hforcing : ∫ x, (g : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n Ω =
      ∫ x, (df : ℝ^n → ℝ) x * φ.1.toFun x +
        ∑ i, ∑ j, (dq i j : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n Ω :=
    integral_congr_ae (hg.mono fun x hx ↦ by simp only [hx, add_mul, Finset.sum_mul])
  have hdqInt (i : Fin n) : ∀ j ∈ Finset.univ, Integrable
      (fun x ↦ (dq i j : ℝ^n → ℝ) x * φ.1.toFun x) (domainMeasure n Ω) := fun j _ ↦ hint _
  have huk := hu ⟨ψ k, hψΩ k⟩
  simp only [hψ] at huk
  simp only [hij, Finset.sum_add_distrib, Finset.sum_neg_distrib] at huk
  rw [hforcing, integral_add (hint df) (integrable_finsetSum _ fun i _ ↦
      integrable_finsetSum _ (hdqInt i)), integral_finsetSum _ fun i _ ↦
      integrable_finsetSum _ (hdqInt i)]
  simp only [integral_finsetSum _ (hdqInt _)]
  have hfk : ∫ x, (f : ℝ^n → ℝ) x * (∂[k] φ.1.toFun) x ∂domainMeasure n Ω =
      -∫ x, (df : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n Ω := by
    simpa [iteratedPartialDeriv] using hf φ.1 φ.2
  linarith only [huk, hfk]

/--
Bundle-level differentiated divergence identity for elliptic regularity.

If the coefficient entries lie in `W^{2,∞}`, the forcing lies in `H¹`, and
the weak solution already has an `H²` representative, then every coordinate
derivative satisfies the differentiated equation against compactly supported
tests.  No trace condition is imposed on that derivative.  All flux and
commutator derivatives are constructed from the Sobolev bundles by the
`W^{1,∞} · W^{1,2}` weak Leibniz rule.
-/
theorem exists_coordinateDerivative_l2_weakEquation_identity
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{2,∞}(Ω))
    (F : W^{1,2}(Ω))
    (U : W^{2,2}(Ω))
    (k : Fin n)
    (htrace0 :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
          (by norm_num) U ∈
        (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Ω)
      (fun i j ↦
        ((A i j : WkpAmbientOn n 2 ∞ Ω) (baseIndex n 2) :
          DerivLp n ∞ Ω))
      ((F : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) :
        DerivLp n 2 Ω)
      ⟨lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
          (by norm_num) U, htrace0⟩) :
    ∃ g : DerivLp n 2 Ω, ∀ φ : TestFunctionOn n Ω,
      (∑ i : Fin n, ∑ j : Fin n,
        ∫ x,
          (((A i j : WkpAmbientOn n 2 ∞ Ω) (baseIndex n 2) :
            DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
          ((((derivativeWordCLM
              (n := n) (m := 2) (r := 1) (p := 2) (Ω := Ω)
              [k] (by simp) U : W^{1,2}(Ω)) :
                WkpAmbientOn n 1 2 Ω) (singleDerivIndex n j) :
                  DerivLp n 2 Ω) : ℝ^n → ℝ) x *
          (∂[i] φ.1.toFun) x
        ∂domainMeasure n Ω) =
      ∫ x, (g : ℝ^n → ℝ) x * φ.1.toFun x
        ∂domainMeasure n Ω := by
  classical
  let u : H¹₀(Ω) :=
    ⟨lowerOrderCLM (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω) (by norm_num) U, htrace0⟩
  let w : H¹(Ω) := derivativeWordCLM (n := n) (m := 2) (r := 1) (p := 2) (Ω := Ω) [k] (by simp) U
  let A0 (i j : Fin n) : W^{1,∞}(Ω) :=
    lowerOrderCLM (n := n) (k := 1) (m := 2) (p := ∞) (Ω := Ω) (by norm_num) (A i j)
  let Ak (i j : Fin n) : W^{1,∞}(Ω) :=
    derivativeWordCLM (n := n) (m := 2) (r := 1) (p := ∞) (Ω := Ω) [k] (by simp) (A i j)
  let Uj (j : Fin n) : W^{1,2}(Ω) :=
    derivativeWordCLM (n := n) (m := 2) (r := 1) (p := 2) (Ω := Ω) [j] (by simp) U
  let a : Fin n → Fin n → DerivLp n ∞ Ω := fun i j ↦
    ((A i j : WkpAmbientOn n 2 ∞ Ω) (baseIndex n 2) : DerivLp n ∞ Ω)
  let da : Fin n → Fin n → DerivLp n ∞ Ω := fun i j ↦
    ((Ak i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) : DerivLp n ∞ Ω)
  let f : DerivLp n 2 Ω := ((F : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) : DerivLp n 2 Ω)
  let df : DerivLp n 2 Ω := ((F : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n k) : DerivLp n 2 Ω)
  have hdu (i j : Fin n) : HasWeakDerivativeOn (n := n) Ω [i]
      (derivCoordCLM (n := n) (Ω := Ω) j u : ℝ^n → ℝ)
      (((Uj j : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i) : DerivLp n 2 Ω) : ℝ^n → ℝ) := by
    simpa [u, Uj, derivCoordCLM_apply, firstDerivIndex_one, derivIndexOfList_singleton] using
      (Uj j).property.hasWeakDerivativeOn_first (by norm_num) i
  have hmixed (j : Fin n) :
      ((Uj j : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n k) : DerivLp n 2 Ω) =
        ((w : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n j) : DerivLp n 2 Ω) := by
    change ((U : WkpAmbientOn n 2 2 Ω) (derivativeWordIndex (n := n) (m := 2) (r := 1) [j]
      (by simp) (singleDerivIndex n k)) : DerivLp n 2 Ω) = (U : WkpAmbientOn n 2 2 Ω)
        (derivativeWordIndex (n := n) (m := 2) (r := 1) [k] (by simp) (singleDerivIndex n j))
    rw [show derivativeWordIndex (n := n) (m := 2) (r := 1) [j] (by simp) (singleDerivIndex n k) =
        derivativeWordIndex (n := n) (m := 2) (r := 1) [k] (by simp) (singleDerivIndex n j) by
      simpa using derivativeWordIndex_singleDerivIndex_comm (n := n) (m := 2) j k (by norm_num)]
  have hflux (i j : Fin n) : HasWeakDerivativeOn (n := n) Ω [k]
      (fun x ↦ (a i j : ℝ^n → ℝ) x * (derivCoordCLM (n := n) (Ω := Ω) j u : ℝ^n → ℝ) x)
      (fun x ↦ (a i j : ℝ^n → ℝ) x * (((w : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n j) :
          DerivLp n 2 Ω) : ℝ^n → ℝ) x +
        (da i j : ℝ^n → ℝ) x * (derivCoordCLM (n := n) (Ω := Ω) j u : ℝ^n → ℝ) x) := by
    simpa [a, da, A0, Ak, derivIndexOfList_singleton] using
      (A0 i j).hasWeakDerivativeOn_mul_W1Top_first hΩopen k _ _ (hmixed j ▸ hdu k j)
  choose dq hdq using fun i j ↦
    (Ak i j).exists_weakDerivative_mul_W1Top_first hΩopen i _ _ (hdu i j)
  refine ⟨df + ∑ i : Fin n, ∑ j : Fin n, dq i j,
    IsWeakDivergenceSolution.coordinateDerivative a da f df _ u w k
      (by simpa [a, f, u] using hu)
      (by simpa [f, df, firstDerivIndex_one] using
        F.property.hasWeakDerivativeOn_first (by norm_num) k) hflux dq hdq ?_⟩
  filter_upwards [Lp.coeFn_add df (∑ i : Fin n, ∑ j : Fin n, dq i j),
    Lp.coeFn_fun_finsetSum Finset.univ fun i ↦ ∑ j : Fin n, dq i j,
    ae_all_iff.2 fun i ↦ Lp.coeFn_fun_finsetSum Finset.univ (dq i)] with x h1 h2 h3
  rw [h1, Pi.add_apply, h2]
  simp only [h3]

/--
One coordinate derivative, equipped with zero trace, is a weak solution with
`L²` forcing.

This is the typed counterpart of
`exists_coordinateDerivative_l2_weakEquation_identity`.  The identity
remains available for normal-flux arguments, where the coordinate derivative
need not satisfy a Dirichlet condition.
-/
theorem exists_coordinateDerivative_l2_weakEquation_solution
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{2,∞}(Ω))
    (F : W^{1,2}(Ω))
    (U : W^{2,2}(Ω))
    (k : Fin n)
    (htrace0 :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
          (by norm_num) U ∈
        (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule)
    (htrace :
      derivativeWordCLM
          (n := n) (m := 2) (r := 1) (p := 2) (Ω := Ω)
          [k] (by simp) U ∈
        (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Ω)
      (fun i j ↦
        ((A i j : WkpAmbientOn n 2 ∞ Ω) (baseIndex n 2) :
          DerivLp n ∞ Ω))
      ((F : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) :
        DerivLp n 2 Ω)
      ⟨lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
          (by norm_num) U, htrace0⟩) :
    ∃ g : DerivLp n 2 Ω,
      IsWeakDivergenceSolution
        (n := n) (Ω := Ω)
        (fun i j ↦
          ((A i j : WkpAmbientOn n 2 ∞ Ω) (baseIndex n 2) :
            DerivLp n ∞ Ω))
        g
        ⟨derivativeWordCLM
            (n := n) (m := 2) (r := 1) (p := 2) (Ω := Ω)
            [k] (by simp) U,
          htrace⟩ := by
  obtain ⟨g, hg⟩ :=
    exists_coordinateDerivative_l2_weakEquation_identity
      hΩopen A F U k htrace0 hu
  refine ⟨g, hΩopen, ?_⟩
  intro φ
  simpa [derivCoordCLM_apply, derivativeWordCLM_apply] using hg φ

/-- The flux row `∑ⱼ aᵢⱼ wⱼ`, formed in `L²` from `L∞` coefficients and `L²` fields, is
represented almost everywhere by the pointwise sum. -/
theorem fluxRow_coeFn_ae
    (coeff : Fin n → Fin n → DerivLp n ∞ Ω) (dw : Fin n → DerivLp n 2 Ω) (i : Fin n) :
    ((∑ j : Fin n, coeff i j • dw j : DerivLp n 2 Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ ∑ j : Fin n,
        (coeff i j : ℝ^n → ℝ) x * (dw j : ℝ^n → ℝ) x := by
  have hsum := MeasureTheory.Lp.coeFn_fun_finsetSum
    (Finset.univ : Finset (Fin n))
    (fun j : Fin n ↦ coeff i j • dw j)
  have hterm (j : Fin n) :
      ((coeff i j • dw j : DerivLp n 2 Ω) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω]
          fun x ↦ (coeff i j : ℝ^n → ℝ) x * (dw j : ℝ^n → ℝ) x := by
    filter_upwards [
      MeasureTheory.Lp.coeFn_lpSMul (r := (2 : ENNReal)) (coeff i j) (dw j)
    ] with x hx
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply] using hx
  filter_upwards [hsum, ae_all_iff.2 hterm] with x hx hterms
  rw [hx]
  apply Finset.sum_congr rfl
  intro j _
  rw [hterms j]

/-- A divergence identity written term by term, `∑ᵢ ∑ⱼ ∫ aᵢⱼ wⱼ ∂ᵢφ = ∫ g φ`, is the
divergence identity for the `L²` flux rows `∑ⱼ aᵢⱼ wⱼ`. -/
theorem sum_integral_fluxRow_mul_iteratedPartialDeriv
    (coeff : Fin n → Fin n → DerivLp n ∞ Ω) (dw : Fin n → DerivLp n 2 Ω)
    (g : ℝ^n → ℝ) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (h : (∑ i : Fin n, ∑ j : Fin n,
        ∫ x, (coeff i j : ℝ^n → ℝ) x * (dw j : ℝ^n → ℝ) x *
          iteratedPartialDeriv (n := n) [i] φ.toFun x ∂domainMeasure n Ω) =
      ∫ x, g x * φ.toFun x ∂domainMeasure n Ω) :
    (∑ i : Fin n,
        ∫ x, ((∑ j : Fin n, coeff i j • dw j : DerivLp n 2 Ω) : ℝ^n → ℝ) x *
          iteratedPartialDeriv (n := n) [i] φ.toFun x ∂domainMeasure n Ω) =
      ∫ x, g x * φ.toFun x ∂domainMeasure n Ω := by
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_congr_ae (by
    filter_upwards [fluxRow_coeFn_ae coeff dw i] with x hx
    rw [hx, Finset.sum_mul])]
  exact integral_finsetSum Finset.univ (fun j _ ↦ by
    have hmem : MemLp
        (fun x ↦ (coeff i j : ℝ^n → ℝ) x * (dw j : ℝ^n → ℝ) x)
        2 (domainMeasure n Ω) :=
      (MeasureTheory.Lp.memLp (coeff i j)).fun_mul (MeasureTheory.Lp.memLp (dw j))
    have hlocal := hmem.locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
    have htestCont :=
      (PDE.contDiff_top_iteratedPartialDeriv (n := n) φ.contDiff [i]).continuous
    have htestCompact := iteratedPartialDeriv_hasCompactSupport (n := n) φ [i]
    have hint := hlocal.integrable_smul_left_of_hasCompactSupport htestCont htestCompact
    simpa [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hint)

namespace BoundaryRegularity

variable [Fact (0 < n)]

/--
An admissible coordinate derivative gains two weak derivatives from the
global `H²` theorem `exists_global_h2_of_isWeakDivergenceSolution`.

This is the first higher-order induction step:
`exists_coordinateDerivative_l2_weakEquation_solution` constructs the
differentiated `L²` forcing, and global boundary regularity then promotes
`Dₖu` from `H¹₀` to `H²`.
-/
theorem exists_coordinateDerivative_h2_of_isWeakDivergenceSolution
    (hOmega : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{2,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 2 ∞ Ω)
          (baseIndex n 2) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (F : W^{1,2}(Ω))
    (U : W^{2,2}(Ω))
    (k : Fin n)
    (htrace0 :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
          (by norm_num) U ∈
        (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule)
    (htracek :
      derivativeWordCLM
          (n := n) (m := 2) (r := 1) (p := 2) (Ω := Ω)
          [k] (by simp) U ∈
        (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Ω)
      (fun i j ↦
        ((A i j : WkpAmbientOn n 2 ∞ Ω) (baseIndex n 2) :
          DerivLp n ∞ Ω))
      ((F : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) :
        DerivLp n 2 Ω)
      ⟨lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
          (by norm_num) U, htrace0⟩)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ W : W^{2,2}(Ω),
      baseRepresentative W =ᵐ[domainMeasure n Ω]
        (fun x ↦
          ⇑((U : WkpAmbientOn n 2 2 Ω)
            (firstDerivIndex n 2 (by norm_num) k) :
              DerivLp n 2 Ω) x) := by
  obtain ⟨g, hg⟩ := exists_coordinateDerivative_l2_weakEquation_solution
    hOmega.toC1ExtensionAtlas.isOpen A F U k htrace0 htracek hu
  let A1 (i j : Fin n) : W^{1,∞}(Ω) :=
    lowerOrderCLM (n := n) (k := 1) (m := 2) (p := ∞) (Ω := Ω) (by norm_num) (A i j)
  obtain ⟨W, hW⟩ := exists_global_h2_of_isWeakDivergenceSolution hOmega A1 a
    (fun i j ↦ by simpa [A1] using haRep i j) haC1 g ⟨_, htracek⟩ (by simpa [A1] using hg)
    alpha halpha hElliptic
  exact ⟨W, by simpa using hW⟩

/--
Qualitative `H³` regularity when every first derivative has zero trace.

Each coordinate derivative first gains an `H²` representative from
`exists_coordinateDerivative_h2_of_isWeakDivergenceSolution`;
the general
Sobolev assembly theorem then combines those representatives into one
`H³` bundle for `u`.

For a general Dirichlet boundary this trace hypothesis is naturally available
for tangential derivatives after flattening.  Recovering the remaining normal
derivatives is the separate boundary-specific step.
-/
theorem exists_global_h3_of_coordinate_derivatives_zero_trace
    (hOmega : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{2,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 2 ∞ Ω)
          (baseIndex n 2) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (F : W^{1,2}(Ω))
    (U : W^{2,2}(Ω))
    (htrace0 :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
          (by norm_num) U ∈
        (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule)
    (htrace : ∀ k : Fin n,
      derivativeWordCLM
          (n := n) (m := 2) (r := 1) (p := 2) (Ω := Ω)
          [k] (by simp) U ∈
        (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Ω)
      (fun i j ↦
        ((A i j : WkpAmbientOn n 2 ∞ Ω) (baseIndex n 2) :
          DerivLp n ∞ Ω))
      ((F : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) :
        DerivLp n 2 Ω)
      ⟨lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
          (by norm_num) U, htrace0⟩)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ W : W^{3,2}(Ω),
      baseRepresentative W =ᵐ[domainMeasure n Ω]
        (fun x ↦
          ⇑((U : WkpAmbientOn n 2 2 Ω)
            (baseIndex n 2) : DerivLp n 2 Ω) x) := by
  classical
  choose V hV using fun k ↦ exists_coordinateDerivative_h2_of_isWeakDivergenceSolution
    hOmega A a haRep haC1 F U k htrace0 (htrace k) hu alpha halpha hElliptic
  exact exists_succOrder_of_firstDerivatives (n := n) (m := 2) (p := 2) (Ω := Ω) (by norm_num)
    U V fun k ↦ Lp.ext (hV k)

end BoundaryRegularity

end SobolevSpace.GraphSpace
