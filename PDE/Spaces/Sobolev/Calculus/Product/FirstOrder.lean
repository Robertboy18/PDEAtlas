/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
import PDE.Spaces.Sobolev.Localization.Cutoff.ZeroBoundary
public import PDE.Spaces.Sobolev.Calculus.Product.LipschitzCoefficient -- shake: keep
public import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport -- shake: keep

/-!
# First-order Sobolev product rule

The weak Leibniz rule for a `W^{1,∞}` coefficient and a `W^{1,2}` field on an open set `Ω`:
if `a ∈ W^{1,∞}(Ω)` and `u ∈ L²(Ω)` has weak derivative `∂ᵢu ∈ L²(Ω)`, then

`∂ᵢ(a u) = a ∂ᵢu + (∂ᵢa) u`

weakly on `Ω`, with the product in `L²` because `a` and `∂ᵢa` are bounded. This is the
coefficient regularity behind the interior `H²` regularity theorem for divergence-form
operators (Evans, PDE, §6.3.1): coefficients `aⁱʲ ∈ C¹(Ω)` lie in `W^{1,∞}` on every subdomain
compactly contained in `Ω`, and the product rule is what lets the equation be differentiated
there.

The proof does not go through smooth approximation of `a`. Instead, the weak derivative identity
`⟪u, ∂ᵢv⟫ = -⟪∂ᵢu, v⟫`, known for smooth compactly supported `v`, is extended by continuity to
all `v ∈ H¹₀(Ω)`; the product `φ a` of a test function with the coefficient is then shown to be
such an `H¹₀(Ω)` test, with explicit base and derivative coordinates, and testing against it
produces the Leibniz identity. Evans proves the case `|α| = 1` of the Leibniz formula by
testing against `ζφ`, which is smooth when `ζ` is; since `φ a` is not smooth, we first extend
the weak derivative identity to `H¹₀(Ω)`.

## Main results

* `weakDerivative_integrationByParts_H10`: a weak derivative identity on `Ω`, tested against
  smooth compactly supported functions, holds against every `v ∈ H¹₀(Ω)`.
* `exists_H10_mul_testFunction_W1Top`: `φ a ∈ H¹₀(Ω)` for a test function `φ` and
  `a ∈ W^{1,∞}(Ω)`, with coordinates `φ a` and `φ ∂ᵢa + (∂ᵢφ) a`.
* `WkpSpaceOn.hasWeakDerivativeOn_mul_W1Top_first`: the Leibniz rule
  `∂ᵢ(a u) = a ∂ᵢu + (∂ᵢa) u` as a weak derivative identity on `Ω`.
* `WkpSpaceOn.exists_weakDerivative_mul_W1Top_first_with_norm`,
  `WkpSpaceOn.exists_weakDerivative_mul_W1Top_first`: forms producing the derivative
  as an `L²(Ω)` element with the bound `‖a‖_∞ ‖∂ᵢu‖₂ + ‖∂ᵢa‖_∞ ‖u‖₂`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 1(iv), (7), pp. 261-262, the Leibniz formula
  for `ζ ∈ C_c^∞(U)`, and step 3 of its proof for the case `|α| = 1`; and §6.3.1, Theorem 1,
  hypothesis (5), p. 327, and Theorem 2, step 3 of the proof, (34)-(36), p. 333, where the equation
  is differentiated and the Leibniz formula falls on the coefficients.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A first weak-derivative identity extends continuously from smooth compactly
supported tests to every `H¹₀` test. -/
theorem weakDerivative_integrationByParts_H10
    (i : Fin n) (f g : DerivLp n 2 Ω)
    (hfg : HasWeakDerivativeOn (n := n) Ω [i]
      (f : ℝ^n → ℝ) (g : ℝ^n → ℝ))
    (v : H¹₀(Ω)) :
    ⟪f, derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ =
      -⟪g, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ := by
  let F : H¹₀(Ω) →L[ℝ] ℝ := (innerSL ℝ f).comp (derivCoordCLM (n := n) (Ω := Ω) i)
  let G : H¹₀(Ω) →L[ℝ] ℝ := -((innerSL ℝ g).comp (baseCoordCLM (n := n) (Ω := Ω)))
  have htest : (F : H¹₀(Ω) → ℝ) ∘ testFunctionToH10Linear (n := n) (Ω := Ω) =
      (G : H¹₀(Ω) → ℝ) ∘ testFunctionToH10Linear (n := n) (Ω := Ω) := by
    funext φ
    have hfint : ⟪f, derivCoordCLM (n := n) (Ω := Ω) i (testFunctionToH10 φ)⟫_ℝ =
        ∫ x, (f : ℝ^n → ℝ) x * (∂[i] φ.1.toFun) x ∂domainMeasure n Ω := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [derivCoordCLM_testFunction_apply_ae (n := n) (Ω := Ω) i φ] with x hx
      rw [hx]
      simp [RCLike.inner_apply, mul_comm]
    change ⟪f, derivCoordCLM (n := n) (Ω := Ω) i (testFunctionToH10 φ)⟫_ℝ =
      -⟪g, baseCoordCLM (n := n) (Ω := Ω) (testFunctionToH10 φ)⟫_ℝ
    rw [hfint, inner_base_testFunction_eq_integral g φ]
    simpa [iteratedPartialDeriv] using hfg φ φ.2
  exact congrFun ((denseRange_testFunctionToH10Linear (n := n) (Ω := Ω)).equalizer
    F.continuous G.continuous htest) v

/-- Multiplying a `W^{1,∞}` coefficient by a smooth test function produces an
`H¹₀` test.  Both its base representative and every first derivative
are recorded explicitly. -/
theorem exists_H10_mul_testFunction_W1Top
    (hΩopen : IsOpen Ω) (A : W^{1,∞}(Ω))
    (φ : TestFunctionOn n Ω) :
    ∃ v : H¹₀(Ω),
      (((baseCoordCLM (n := n) (Ω := Ω) v :
          DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ φ.1.toFun x *
          (((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
            DerivLp n ∞ Ω) : ℝ^n → ℝ) x) ∧
      ∀ i : Fin n,
        ((derivCoordCLM (n := n) (Ω := Ω) i v :
            DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
          fun x ↦ φ.1.toFun x *
              (((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) :
                DerivLp n ∞ Ω) : ℝ^n → ℝ) x +
            iteratedPartialDeriv (n := n) [i] φ.1.toFun x *
              (((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                DerivLp n ∞ Ω) : ℝ^n → ℝ) x := by
  classical
  let a : ℝ^n → ℝ := ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) : DerivLp n ∞ Ω)
  let da : Fin n → ℝ^n → ℝ := fun i ↦
    ((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) : DerivLp n ∞ Ω)
  let b : ℝ^n → ℝ := fun x ↦ φ.1.toFun x * a x
  let d : Fin n → ℝ^n → ℝ := fun i x ↦
    φ.1.toFun x * da i x + iteratedPartialDeriv (n := n) [i] φ.1.toFun x * a x
  have hφLp : MemLp φ.1.toFun 2 (domainMeasure n Ω) :=
    φ.1.contDiff.continuous.memLp_of_hasCompactSupport φ.1.hasCompactSupport
  have hdφLp (i : Fin n) :
      MemLp (fun x ↦ iteratedPartialDeriv (n := n) [i] φ.1.toFun x) 2 (domainMeasure n Ω) :=
    (PDE.contDiff_top_iteratedPartialDeriv (n := n) φ.1.contDiff [i]).continuous
      |>.memLp_of_hasCompactSupport (iteratedPartialDeriv_hasCompactSupport (n := n) φ.1 [i])
  have hbLp : MemLp b 2 (domainMeasure n Ω) := hφLp.fun_mul (Lp.memLp _)
  have hdLp (i : Fin n) : MemLp (d i) 2 (domainMeasure n Ω) :=
    MemLp.add (hφLp.fun_mul (Lp.memLp _)) ((hdφLp i).fun_mul (Lp.memLp _))
  have hqLp (r : DerivIndex n 1) : MemLp (firstOrderRows b d r) 2 (domainMeasure n Ω) := by
    rcases r.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa using hbLp
    · simpa using hdLp i
  have hqweak (r : DerivIndex n 1) :
      HasWeakDerivativeOn (n := n) Ω r.toList b (firstOrderRows b d r) := by
    rcases r.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa [iteratedPartialDeriv] using hasWeakDerivativeOn_nil
        (memLp_locallyIntegrableOn_domain hbLp (by norm_num))
    · simpa [b, d, a, da] using hasWeakDerivativeOn_mul_testFunction_first
        (p := (∞ : ℝ≥0∞)) (i := i) (Lp.memLp _) (Lp.memLp _)
        (by simpa [a, da, firstDerivIndex_one] using
          A.property.hasWeakDerivativeOn_first (by norm_num) i) φ.1
  let V : H¹(Ω) := mkWkpSpaceOnOfWeakDerivatives b (firstOrderRows b d) (by simp) hqLp hqweak
  have hV (r : DerivIndex n 1) : ((((V : WkpAmbientOn n 1 2 Ω) r : DerivLp n 2 Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω] firstOrderRows b d r :=
    mkWkpSpaceOnOfWeakDerivatives_apply_ae b _ (by simp) hqLp hqweak r
  -- `V` is supported in `tsupport φ`, so a cutoff equal to one there fixes it and `V ∈ H¹₀`
  obtain ⟨χ, hχΩ, hχone, -⟩ :=
    TestFunction.exists_eq_one_on_compact hΩopen φ.1.hasCompactSupport (by exact φ.2)
  have hcutEq : cutoffCLM (n := n) (p := 2) (Ω := Ω) χ V = V := by
    apply WkpSpaceOn.ext_of_base_ae hΩopen
    filter_upwards [cutoffCLM_base_apply_ae (n := n) (p := 2) (Ω := Ω) χ V,
      hV (baseIndex n 1)] with x hx hxb
    rw [hx, hxb]
    by_cases hφx : (φ.1 : ℝ^n → ℝ) x = 0
    · simp [b, hφx]
    · simp [b, hχone x (subset_tsupport _ hφx)]
  let v : H¹₀(Ω) := ⟨V, by
    change V ∈ (wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω)).toSubmodule
    simpa only [h10SubmoduleOn, hcutEq] using cutoffCLM_mem_H10 hΩopen χ hχΩ V⟩
  exact ⟨v, (hV _).trans (.of_eq (firstOrderRows_baseIndex b d)),
    fun i ↦ (hV _).trans (.of_eq (firstOrderRows_singleDerivIndex b d i))⟩

/-- First-order weak Leibniz rule: for open `Ω`, `A ∈ W^{1,∞}(Ω)` with base coordinate `a`,
and `u ∈ L²(Ω)` with weak derivative `∂ᵢu = du` on `Ω`, the product `a u` has weak derivative
`a du + (∂ᵢa) u` on `Ω`. -/
theorem WkpSpaceOn.hasWeakDerivativeOn_mul_W1Top_first
    (hΩopen : IsOpen Ω) (A : W^{1,∞}(Ω))
    (i : Fin n) (u du : DerivLp n 2 Ω)
    (hu : HasWeakDerivativeOn (n := n) Ω [i]
      (u : ℝ^n → ℝ) (du : ℝ^n → ℝ)) :
    HasWeakDerivativeOn (n := n) Ω [i]
      (fun x ↦
        (((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
          DerivLp n ∞ Ω) : ℝ^n → ℝ) x * u x)
      (fun x ↦
        (((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
          DerivLp n ∞ Ω) : ℝ^n → ℝ) x * du x +
        (((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) :
          DerivLp n ∞ Ω) : ℝ^n → ℝ) x * u x) := by
  let a : ℝ^n → ℝ := ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) : DerivLp n ∞ Ω)
  let da : ℝ^n → ℝ := ((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) : DerivLp n ∞ Ω)
  have hauLp : MemLp (fun x ↦ a x * u x) 2 (domainMeasure n Ω) :=
    (Lp.memLp ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))).fun_mul (Lp.memLp u)
  have haduLp : MemLp (fun x ↦ a x * du x) 2 (domainMeasure n Ω) :=
    (Lp.memLp ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))).fun_mul (Lp.memLp du)
  have hdauLp : MemLp (fun x ↦ da x * u x) 2 (domainMeasure n Ω) :=
    (Lp.memLp ((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i))).fun_mul (Lp.memLp u)
  refine ⟨memLp_locallyIntegrableOn_domain hauLp (by norm_num),
    memLp_locallyIntegrableOn_domain (haduLp.add hdauLp) (by norm_num), fun φ hφΩ ↦ ?_⟩
  obtain ⟨v, hvbase, hvderiv⟩ := exists_H10_mul_testFunction_W1Top hΩopen A ⟨φ, hφΩ⟩
  have hφLp : MemLp φ.toFun 2 (domainMeasure n Ω) :=
    φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hdφLp : MemLp (fun x ↦ iteratedPartialDeriv (n := n) [i] φ.toFun x) 2 (domainMeasure n Ω) :=
    (PDE.contDiff_top_iteratedPartialDeriv (n := n) φ.contDiff [i]).continuous
      |>.memLp_of_hasCompactSupport (iteratedPartialDeriv_hasCompactSupport (n := n) φ [i])
  have hint {f g : ℝ^n → ℝ} (hf : MemLp f 2 (domainMeasure n Ω))
      (hg : MemLp g 2 (domainMeasure n Ω)) :
      Integrable (fun x ↦ f x * g x) (domainMeasure n Ω) :=
    memLp_one_iff_integrable.mp (hf.fun_mul hg)
  -- integrate by parts against the `H¹₀` test `φ a`
  have hleft : ⟪u, derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ =
      ∫ x, (da x * u x) * φ.toFun x + (a x * u x) * iteratedPartialDeriv (n := n) [i] φ.toFun x
        ∂domainMeasure n Ω := by
    rw [L2.inner_def]
    refine integral_congr_ae ((hvderiv i).mono fun x hx ↦ ?_)
    simp only [hx, a, da, RCLike.inner_apply, conj_trivial]
    ring
  have hright : ⟪du, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ =
      ∫ x, (a x * du x) * φ.toFun x ∂domainMeasure n Ω := by
    rw [L2.inner_def]
    refine integral_congr_ae (hvbase.mono fun x hx ↦ ?_)
    simp only [hx, a, RCLike.inner_apply, conj_trivial]
    ring
  have hparts := weakDerivative_integrationByParts_H10 i u du hu v
  rw [hleft, hright, integral_add (hint hdauLp hφLp) (hint hauLp hdφLp)] at hparts
  simp only [add_mul, List.length_singleton, pow_one]
  rw [integral_add (hint haduLp hφLp) (hint hdauLp hφLp)]
  linarith

/-- Quantitative form of the first-order
`W^{1,∞} × W^{1,2}` Leibniz rule.  The returned weak derivative obeys
the usual product estimate in terms of the `L∞` coefficient rows and the
`L²` field rows. -/
theorem WkpSpaceOn.exists_weakDerivative_mul_W1Top_first_with_norm
    (hΩopen : IsOpen Ω) (A : W^{1,∞}(Ω))
    (i : Fin n) (u du : DerivLp n 2 Ω)
    (hu : HasWeakDerivativeOn (n := n) Ω [i]
      (u : ℝ^n → ℝ) (du : ℝ^n → ℝ)) :
    ∃ g : DerivLp n 2 Ω,
      ‖g‖ ≤
          ‖((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
            DerivLp n ∞ Ω)‖ * ‖du‖ +
          ‖((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) :
            DerivLp n ∞ Ω)‖ * ‖u‖ ∧
        HasWeakDerivativeOn (n := n) Ω [i]
        (fun x ↦
          (((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
            DerivLp n ∞ Ω) : ℝ^n → ℝ) x * u x)
        (g : ℝ^n → ℝ) := by
  let a0 : DerivLp n ∞ Ω := (A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)
  let dai : DerivLp n ∞ Ω := (A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)
  have hg : ((a0 • du + dai • u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ (a0 : ℝ^n → ℝ) x * du x + (dai : ℝ^n → ℝ) x * u x := by
    filter_upwards [Lp.coeFn_add (a0 • du) (dai • u), Lp.coeFn_lpSMul (r := 2) a0 du,
      Lp.coeFn_lpSMul (r := 2) dai u] with x hadd h0 hi
    simp only [hadd, Pi.add_apply, h0, hi, Pi.smul_apply', smul_eq_mul]
  exact ⟨a0 • du + dai • u, (norm_add_le _ _).trans
      (add_le_add (Lp.norm_smul_le a0 du) (Lp.norm_smul_le dai u)),
    (hasWeakDerivativeOn_congr_ae .rfl hg.symm).1
      (A.hasWeakDerivativeOn_mul_W1Top_first hΩopen i u du hu)⟩

/-- Packaged `L²` conclusion of the first-order
`W^{1,∞} × W^{1,2}` Leibniz rule. -/
theorem WkpSpaceOn.exists_weakDerivative_mul_W1Top_first
    (hΩopen : IsOpen Ω) (A : W^{1,∞}(Ω))
    (i : Fin n) (u du : DerivLp n 2 Ω)
    (hu : HasWeakDerivativeOn (n := n) Ω [i]
      (u : ℝ^n → ℝ) (du : ℝ^n → ℝ)) :
    ∃ g : DerivLp n 2 Ω,
      HasWeakDerivativeOn (n := n) Ω [i]
        (fun x ↦
          (((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
            DerivLp n ∞ Ω) : ℝ^n → ℝ) x * u x)
        (g : ℝ^n → ℝ) := by
  obtain ⟨g, _hgNorm, hg⟩ :=
    A.exists_weakDerivative_mul_W1Top_first_with_norm hΩopen i u du hu
  exact ⟨g, hg⟩

end SobolevSpace.GraphSpace
