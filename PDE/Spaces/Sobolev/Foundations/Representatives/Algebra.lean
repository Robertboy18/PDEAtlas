/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.Representatives.Definitions

/-!
# Algebra of Representative-Level Sobolev Spaces

Weak derivatives are linear and satisfy the first-order Leibniz rule for smooth multipliers,
and representative-level Sobolev packages carry pointwise additive and real-linear structures.
These are the linearity and smooth-multiplier properties in Evans, §5.2.3, Theorem 1(ii), (iv).

Weak derivatives are linear in the function: if `g` and `g'` are weak `∂^α`-derivatives of `f`
and `f'` then `λg + μg'` is a weak `∂^α`-derivative of `λf + μf'`. Local integrability in
the weak-derivative relation and compact support of the test functions supply integrability
of the pairings. No global `L^p` hypotheses are needed for linearity. The first-order Leibniz rule
`∂ᵢ(ψf) = ψ ∂ᵢf + (∂ᵢψ) f` for a smooth multiplier `ψ` is proved by moving `ψ` onto the test
function; it is used throughout the localisation and extension arguments.

## Main results

* `hasWeakDerivativeOn_zero`, `hasWeakDerivativeOn_smul`, `hasWeakDerivativeOn_add`,
  `hasWeakDerivativeOn_sub`, `hasWeakDerivativeOn_finsetSum`: linearity of weak derivatives.
* `hasWeakDerivativeOn_mul_testFunction_first`, `hasWeakDerivativeOn_mul_contDiff_first`: the
  first-order product rule `∂ᵢ(ζf) = ζ ∂ᵢf + (∂ᵢζ) f` with a test function `ζ`, and with a
  smooth `ζ` such that `ζ` and `∂ᵢζ` are essentially bounded on `Ω`.
* `SobolevSpaceOn.mulTestFunction`: multiplication of a `W^{1,p}` package by a test function.
* `Zero`, `Add`, `Neg`, `Sub`, `SMul ℝ`, `AddCommGroup`, `Module ℝ` instances on
  `SobolevSpaceOn n k p Ω`, all defined pointwise on the stored representatives, together with
  the `*_toFun` evaluation lemmas.

## Implementation notes

The algebraic structure here is qualitative: `SobolevSpaceOn` stores concrete functions and is
not a quotient, so it carries no norm. The normed, complete `W^{k,p}(Ω)` is the graph space
`SobolevSpace.GraphSpace.WkpSpaceOn`. Every algebraic law is proved by extensionality
(`SobolevSpaceOn.ext`) from the corresponding law for functions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 1(ii) and (iv), pp. 261-262, and step 3 of
  its proof for the case `|α| = 1` of the Leibniz formula (7).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped NNReal

variable {n : ℕ} {p : ℝ≥0∞}

section BasicInstances

variable [Fact (1 ≤ p)]
variable {k : ℕ} {Ω : Set (ℝ^n)}

/-- The zero function has zero weak derivative of every order. -/
theorem hasWeakDerivativeOn_zero (Ω : Set (ℝ^n)) (α : List (Fin n)) :
    HasWeakDerivativeOn (n := n) Ω α (fun _ : ℝ^n ↦ (0 : ℝ)) (fun _ : ℝ^n ↦ (0 : ℝ)) := by
  refine ⟨MeasureTheory.locallyIntegrableOn_const 0,
    MeasureTheory.locallyIntegrableOn_const 0, ?_⟩
  intro φ _
  simp

/-- Weak derivatives commute with multiplication by a real scalar. -/
theorem hasWeakDerivativeOn_smul (c : ℝ) {α : List (Fin n)} {f g : ℝ^n → ℝ}
    (hfg : HasWeakDerivativeOn (n := n) Ω α f g) :
    HasWeakDerivativeOn (n := n) Ω α (c • f) (c • g) := by
  refine ⟨hfg.locallyIntegrable_f.smul c, hfg.locallyIntegrable_g.smul c, ?_⟩
  intro φ hφsupp
  have h := hfg φ hφsupp
  calc
    (∫ x, (c • f) x * iteratedPartialDeriv (n := n) α φ.toFun x ∂ domainMeasure n Ω) =
        c * ∫ x, f x * iteratedPartialDeriv (n := n) α φ.toFun x ∂ domainMeasure n Ω := by
      simp [smul_eq_mul, mul_assoc, MeasureTheory.integral_const_mul]
    _ = c * ((-1) ^ α.length * ∫ x, g x * φ.toFun x ∂ domainMeasure n Ω) :=
      congrArg (c * ·) h
    _ = (-1) ^ α.length * (c * ∫ x, g x * φ.toFun x ∂ domainMeasure n Ω) := by ring
    _ = (-1) ^ α.length * ∫ x, (c • g) x * φ.toFun x ∂ domainMeasure n Ω := by
      simp [smul_eq_mul, mul_assoc, MeasureTheory.integral_const_mul, mul_left_comm]

omit [Fact (1 ≤ p)] in private lemma hasWeakDerivativeInLpOn_zero
    (Ω : Set (ℝ^n)) (α : List (Fin n)) :
    HasWeakDerivativeInLpOn (n := n) Ω α p (fun _ : ℝ^n ↦ (0 : ℝ)) := by
  exact ⟨0, MeasureTheory.MemLp.zero, hasWeakDerivativeOn_zero Ω α⟩

/-- The zero package: the zero function, whose weak derivatives of every order are zero. -/
instance instZeroSobolevSpaceOn : Zero (SobolevSpaceOn n k p Ω) where
  zero :=
    { toFun := 0
      memLp := MeasureTheory.MemLp.zero
      weak_derivs_inLp := by
        intro α hα
        exact hasWeakDerivativeInLpOn_zero (n := n) (p := p) (Ω := Ω) α }

/-- Weak derivatives are additive. Local integrability suffices for both test pairings. -/
theorem hasWeakDerivativeOn_add {α : List (Fin n)} {f f' g g' : ℝ^n → ℝ}
    (hf : HasWeakDerivativeOn (n := n) Ω α f f')
    (hg : HasWeakDerivativeOn (n := n) Ω α g g') :
    HasWeakDerivativeOn (n := n) Ω α (f + g) (f' + g') := by
  refine ⟨hf.locallyIntegrable_f.add hg.locallyIntegrable_f,
    hf.locallyIntegrable_g.add hg.locallyIntegrable_g, ?_⟩
  intro φ hφsupp
  simp only [Pi.add_apply, add_mul]
  rw [integral_add (hf.integrable_mul_iteratedPartialDeriv φ hφsupp)
      (hg.integrable_mul_iteratedPartialDeriv φ hφsupp),
    integral_add (hf.integrable_mul_testFunction φ hφsupp)
      (hg.integrable_mul_testFunction φ hφsupp),
    hf φ hφsupp, hg φ hφsupp, mul_add]

/-- Finite sums preserve a fixed weak derivative. -/
theorem hasWeakDerivativeOn_finsetSum
    {ι : Type*}
    (s : Finset ι) (f g : ι → ℝ^n → ℝ) (alpha : List (Fin n))
    (hfg : ∀ i ∈ s,
      HasWeakDerivativeOn (n := n) Ω alpha (f i) (g i)) :
    HasWeakDerivativeOn (n := n) Ω alpha
      (fun x ↦ ∑ i ∈ s, f i x) (fun x ↦ ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hasWeakDerivativeOn_zero
        (n := n) (Ω := Ω) alpha
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      change HasWeakDerivativeOn (n := n) Ω alpha
        (f i + fun x ↦ ∑ j ∈ s, f j x)
        (g i + fun x ↦ ∑ j ∈ s, g j x)
      exact hasWeakDerivativeOn_add
        (hfg i (Finset.mem_insert_self i s))
        (ih (fun j hj ↦ hfg j (Finset.mem_insert_of_mem hj)))

/-- Weak derivatives commute with subtraction. -/
theorem hasWeakDerivativeOn_sub
    {f f' g g' : ℝ^n → ℝ} (alpha : List (Fin n))
    (hf : HasWeakDerivativeOn (n := n) Ω alpha f f')
    (hg : HasWeakDerivativeOn (n := n) Ω alpha g g') :
    HasWeakDerivativeOn (n := n) Ω alpha
      (fun x ↦ f x - g x) (fun x ↦ f' x - g' x) := by
  simpa only [neg_one_smul, Pi.add_def, Pi.neg_def, sub_eq_add_neg] using
    hasWeakDerivativeOn_add hf (hasWeakDerivativeOn_smul (-1 : ℝ) hg)

/-- First-order weak Leibniz rule for a smooth multiplier whose value and
coordinate derivative are essentially bounded on the domain.  Unlike
`hasWeakDerivativeOn_mul_testFunction_first`, the multiplier itself need not
have compact support: compactness comes from the test function used in the
weak formulation. -/
theorem hasWeakDerivativeOn_mul_contDiff_first
    {f g ζ : ℝ^n → ℝ} {i : Fin n}
    (hfLp : MeasureTheory.MemLp f p (domainMeasure n Ω))
    (hgLp : MeasureTheory.MemLp g p (domainMeasure n Ω))
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζLpTop : MeasureTheory.MemLp ζ (⊤ : ℝ≥0∞) (domainMeasure n Ω))
    (hdζLpTop : MeasureTheory.MemLp
      (fun x ↦ iteratedPartialDeriv (n := n) [i] ζ x)
      (⊤ : ℝ≥0∞) (domainMeasure n Ω))
    (hf : HasWeakDerivativeOn (n := n) Ω [i] f g) :
    HasWeakDerivativeOn (n := n) Ω [i] (fun x ↦ ζ x * f x)
      (fun x ↦ ζ x * g x +
        iteratedPartialDeriv (n := n) [i] ζ x * f x) := by
  refine ⟨memLp_locallyIntegrableOn_domain (p := p) (hζLpTop.fun_mul hfLp) Fact.out,
    memLp_locallyIntegrableOn_domain (p := p) ((hζLpTop.fun_mul hgLp).add
      (hdζLpTop.fun_mul hfLp)) Fact.out, fun φ hφsupp ↦ ?_⟩
  let ζφ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) := _root_.TestFunction.mk (fun x ↦ ζ x * φ.toFun x)
    (hζ.mul φ.contDiff) φ.hasCompactSupport.mul_left (subset_univ _)
  have hζφsupp : tsupport ζφ.toFun ⊆ Ω := tsupport_mul_subset_right.trans hφsupp
  set dζ : ℝ^n → ℝ := fun x ↦ iteratedPartialDeriv (n := n) [i] ζ x
  set dφ : ℝ^n → ℝ := fun x ↦ iteratedPartialDeriv (n := n) [i] φ.toFun x
  -- the classical product rule `∂ᵢ(ζ φ) = ζ ∂ᵢφ + φ ∂ᵢζ`
  have hderiv (x : ℝ^n) :
      iteratedPartialDeriv (n := n) [i] ζφ.toFun x = ζ x * dφ x + φ.toFun x * dζ x := by
    simpa [ζφ, dζ, dφ, iteratedPartialDeriv, mul_comm, add_comm] using
      PDE.partialDeriv_mul (n := n) (i := i) (x := x)
        (hζ.differentiable (by simp)).differentiableAt
        (φ.contDiff.differentiable (by simp)).differentiableAt
  have hdζ_cont : Continuous dζ :=
    (PDE.contDiff_top_iteratedPartialDeriv (n := n) hζ [i]).continuous
  have hI : Integrable (fun x ↦ f x * (φ.toFun x * dζ x)) (domainMeasure n Ω) :=
    (hfLp.locallyIntegrable Fact.out).integrable_smul_right_of_hasCompactSupport
      (φ.contDiff.continuous.mul hdζ_cont) φ.hasCompactSupport.mul_right
  -- `∫ ζ f ∂ᵢφ = ∫ f ∂ᵢ(ζ φ) - ∫ f φ ∂ᵢζ = -∫ g ζ φ - ∫ f φ ∂ᵢζ`
  have e₁ : (fun x ↦ ζ x * f x * dφ x) = fun x ↦
      f x * iteratedPartialDeriv (n := n) [i] ζφ.toFun x - f x * (φ.toFun x * dζ x) :=
    funext fun x ↦ by rw [hderiv]; ring
  have e₂ : (fun x ↦ (ζ x * g x + dζ x * f x) * φ.toFun x) = fun x ↦
      g x * ζφ.toFun x + f x * (φ.toFun x * dζ x) :=
    funext fun x ↦ show _ = g x * (ζ x * φ.toFun x) + _ by ring
  change ∫ x, ζ x * f x * dφ x ∂domainMeasure n Ω =
    (-1) ^ [i].length * ∫ x, (ζ x * g x + dζ x * f x) * φ.toFun x ∂domainMeasure n Ω
  rw [e₁, e₂, integral_sub (hf.integrable_mul_iteratedPartialDeriv ζφ hζφsupp) hI,
    integral_add (hf.integrable_mul_testFunction ζφ hζφsupp) hI, hf ζφ hζφsupp]
  simp only [List.length_singleton, pow_one]
  ring

/-- First-order weak Leibniz rule for multiplication by a test function: if `f, g ∈ L^p(Ω)`
and `∂ᵢf = g` weakly on `Ω`, then for every `ψ ∈ C_c^∞(ℝ^n)`, `∂ᵢ(ψf) = ψ g + (∂ᵢψ) f`
weakly on `Ω`.

This is the case `|α| = 1` of Evans, Section 5.2.3, Theorem 1(iv), except that the support
of `ψ` need not lie in `Ω`. Compact support supplies the required `L^∞` bounds for the
multiplier and its coordinate derivative. -/
theorem hasWeakDerivativeOn_mul_testFunction_first
    {f g : ℝ^n → ℝ} {i : Fin n}
    (hfLp : MeasureTheory.MemLp f p (domainMeasure n Ω))
    (hgLp : MeasureTheory.MemLp g p (domainMeasure n Ω))
    (hf : HasWeakDerivativeOn (n := n) Ω [i] f g)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    HasWeakDerivativeOn (n := n) Ω [i] (fun x ↦ ψ.toFun x * f x)
      (fun x ↦
        ψ.toFun x * g x + iteratedPartialDeriv (n := n) [i] ψ.toFun x * f x) := by
  have hψLpTop : MeasureTheory.MemLp ψ.toFun (⊤ : ℝ≥0∞) (domainMeasure n Ω) :=
    ψ.contDiff.continuous.memLp_top_of_hasCompactSupport
      ψ.hasCompactSupport (domainMeasure n Ω)
  have hdψLpTop : MeasureTheory.MemLp
      (fun x ↦ iteratedPartialDeriv (n := n) [i] ψ.toFun x) (⊤ : ℝ≥0∞) (domainMeasure n Ω) :=
    (PDE.contDiff_top_iteratedPartialDeriv (n := n) ψ.contDiff [i]).continuous
      |>.memLp_top_of_hasCompactSupport
      (iteratedPartialDeriv_hasCompactSupport (n := n) ψ [i]) (domainMeasure n Ω)
  exact hasWeakDerivativeOn_mul_contDiff_first hfLp hgLp ψ.contDiff hψLpTop hdψLpTop hf

/-- Multiply a representative-level `W^{1,p}` function by a test function.

The weak derivative is furnished by the first-order Leibniz rule. This
operation stays at the representative level; the graph-space quotient obtains
its corresponding bounded operator separately. -/
noncomputable def SobolevSpaceOn.mulTestFunction (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (u : SobolevSpaceOn n 1 p Ω) : SobolevSpaceOn n 1 p Ω :=
  have hψLpTop : MeasureTheory.MemLp ψ.toFun (⊤ : ℝ≥0∞) (domainMeasure n Ω) := by
    exact (ψ.contDiff.continuous).memLp_top_of_hasCompactSupport
      ψ.hasCompactSupport (domainMeasure n Ω)
  have hbaseLp : MeasureTheory.MemLp (fun x ↦ ψ.toFun x * u.toFun x) p (domainMeasure n Ω) := by
    exact hψLpTop.fun_mul u.memLp
  { toFun := fun x ↦ ψ.toFun x * u.toFun x
    memLp := hbaseLp
    weak_derivs_inLp := by
      intro α hα
      have hα' : α = [] ∨ ∃ i : Fin n, α = [i] := by
        -- lists of length ≤ 1 are either `[]` or `[i]`
        cases α with
        | nil => exact Or.inl rfl
        | cons a rest =>
            cases rest with
            | nil =>
                exact Or.inr ⟨a, rfl⟩
            | cons b rest' =>
                have : (a :: b :: rest').length ≤ 1 := hα
                simp at this
      rcases hα' with rfl | ⟨i, rfl⟩
      · -- `α = []`: weak derivative is the function itself.
        refine ⟨fun x ↦ ψ.toFun x * u.toFun x, hbaseLp, ?_⟩
        exact hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain hbaseLp Fact.out)
      · -- `α = [i]`: use the product rule lemma.
        rcases u.weak_derivs_inLp [i] (by simp) with ⟨g, hgLp, hgWeak⟩
        set dψ : ℝ^n → ℝ := fun x ↦ iteratedPartialDeriv (n := n) [i] ψ.toFun x
        have hdψLpTop : MeasureTheory.MemLp dψ (⊤ : ℝ≥0∞) (domainMeasure n Ω) := by
          have hdψ_cont : Continuous dψ :=
            (PDE.contDiff_top_iteratedPartialDeriv (n := n) ψ.contDiff [i]).continuous
          have hdψ_cs : HasCompactSupport dψ :=
            iteratedPartialDeriv_hasCompactSupport (n := n) ψ [i]
          exact hdψ_cont.memLp_top_of_hasCompactSupport hdψ_cs (domainMeasure n Ω)
        have hterm1 : MeasureTheory.MemLp (fun x ↦ ψ.toFun x * g x) p (domainMeasure n Ω) := by
          exact hψLpTop.fun_mul hgLp
        have hterm2 : MeasureTheory.MemLp (fun x ↦ dψ x * u.toFun x) p (domainMeasure n Ω) := by
          exact hdψLpTop.fun_mul u.memLp
        have hsum :
            MeasureTheory.MemLp (fun x ↦ ψ.toFun x * g x + dψ x * u.toFun x) p
              (domainMeasure n Ω) :=
          hterm1.add hterm2
        refine ⟨fun x ↦ ψ.toFun x * g x + dψ x * u.toFun x, hsum, ?_⟩
        have hWD :
            HasWeakDerivativeOn (n := n) Ω [i] (fun x ↦ ψ.toFun x * u.toFun x)
              (fun x ↦ ψ.toFun x * g x + dψ x * u.toFun x) := by
          -- `dψ = ∂ᵢψ` by definition of `iteratedPartialDeriv`
          simpa [dψ] using
            hasWeakDerivativeOn_mul_testFunction_first (n := n) (p := p) (Ω := Ω) (i := i)
              (f := u.toFun) (g := g) u.memLp hgLp hgWeak ψ
        exact hWD }

/-- Pointwise addition of packages, with the sum of their weak derivatives. -/
instance instAddSobolevSpaceOn : Add (SobolevSpaceOn n k p Ω) where
  add u v :=
    { toFun := u.toFun + v.toFun
      memLp := u.memLp.add v.memLp
      weak_derivs_inLp := by
        intro α hα
        rcases u.weak_derivs_inLp α hα with ⟨gu, hguLp, hgu⟩
        rcases v.weak_derivs_inLp α hα with ⟨gv, hgvLp, hgv⟩
        refine ⟨gu + gv, hguLp.add hgvLp, ?_⟩
        exact hasWeakDerivativeOn_add hgu hgv }

/-- Pointwise negation of packages; the weak derivatives are negated through
`hasWeakDerivativeOn_smul` with scalar `-1`. -/
instance instNegSobolevSpaceOn : Neg (SobolevSpaceOn n k p Ω) where
  neg u :=
    { toFun := -u.toFun
      memLp := u.memLp.neg
      weak_derivs_inLp := by
        intro α hα
        rcases u.weak_derivs_inLp α hα with ⟨g, hgLp, hg⟩
        refine ⟨-g, hgLp.neg, ?_⟩
        simpa only [neg_one_smul] using
          hasWeakDerivativeOn_smul (n := n) (Ω := Ω) (-1) hg }

/-- Subtraction of packages, defined as `u + (-v)`. -/
instance instSubSobolevSpaceOn : Sub (SobolevSpaceOn n k p Ω) where
  sub u v := u + (-v)

/-- Representative-level Sobolev packages form an additive commutative group under pointwise
operations.  Extensionality reduces every algebraic law to the corresponding law for functions. -/
instance : AddCommGroup (SobolevSpaceOn n k p Ω) where
  add := instAddSobolevSpaceOn.add
  zero := instZeroSobolevSpaceOn.zero
  neg := instNegSobolevSpaceOn.neg
  sub := instSubSobolevSpaceOn.sub
  add_assoc u v w := by
    apply SobolevSpaceOn.ext
    funext x
    change (u.toFun x + v.toFun x) + w.toFun x =
      u.toFun x + (v.toFun x + w.toFun x)
    exact add_assoc _ _ _
  zero_add u := by
    apply SobolevSpaceOn.ext
    funext x
    change 0 + u.toFun x = u.toFun x
    exact zero_add _
  add_zero u := by
    apply SobolevSpaceOn.ext
    funext x
    change u.toFun x + 0 = u.toFun x
    exact add_zero _
  neg_add_cancel u := by
    apply SobolevSpaceOn.ext
    funext x
    change -u.toFun x + u.toFun x = 0
    exact neg_add_cancel _
  add_comm u v := by
    apply SobolevSpaceOn.ext
    funext x
    change u.toFun x + v.toFun x = v.toFun x + u.toFun x
    exact add_comm _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

omit [Fact (1 ≤ p)] in
/-- The zero package evaluates to `0` at every point. -/
@[simp] theorem SobolevSpaceOn.zero_toFun (x : ℝ^n) :
    (0 : SobolevSpaceOn n k p Ω).toFun x = 0 :=
  rfl

omit [Fact (1 ≤ p)] in
/-- The sum of two packages evaluates pointwise to the sum of the representatives. -/
@[simp] theorem SobolevSpaceOn.add_toFun
    (u v : SobolevSpaceOn n k p Ω) (x : ℝ^n) :
    (u + v).toFun x = u.toFun x + v.toFun x :=
  rfl

omit [Fact (1 ≤ p)] in
/-- The negative of a package evaluates pointwise to the negative of the representative. -/
@[simp] theorem SobolevSpaceOn.neg_toFun
    (u : SobolevSpaceOn n k p Ω) (x : ℝ^n) :
    (-u).toFun x = -u.toFun x :=
  rfl

/-- Real scalar multiplication of packages, pointwise on the representative; weak derivatives
scale by `hasWeakDerivativeOn_smul`. -/
instance : SMul ℝ (SobolevSpaceOn n k p Ω) where
  smul c u :=
    { toFun := c • u.toFun
      memLp := u.memLp.const_smul c
      weak_derivs_inLp := by
        intro α hα
        rcases u.weak_derivs_inLp α hα with ⟨g, hgLp, hg⟩
        refine ⟨c • g, hgLp.const_smul c, ?_⟩
        exact hasWeakDerivativeOn_smul (n := n) (Ω := Ω) c hg }

omit [Fact (1 ≤ p)] in
/-- A scalar multiple of a package evaluates pointwise to the scaled representative. -/
@[simp] theorem SobolevSpaceOn.smul_toFun
    (c : ℝ) (u : SobolevSpaceOn n k p Ω) (x : ℝ^n) :
    (c • u).toFun x = c * u.toFun x :=
  rfl

/-- Representative-level Sobolev packages form a real vector space under pointwise
operations. This structure is qualitative: the normed, complete quotient-level space is
`SobolevSpace.GraphSpace.WkpSpaceOn`. -/
instance : Module ℝ (SobolevSpaceOn n k p Ω) where
  one_smul u := by
    apply SobolevSpaceOn.ext
    funext x
    simp
  mul_smul a b u := by
    apply SobolevSpaceOn.ext
    funext x
    simp [mul_assoc]
  smul_zero a := by
    apply SobolevSpaceOn.ext
    funext x
    simp
  smul_add a u v := by
    apply SobolevSpaceOn.ext
    funext x
    simp [mul_add]
  add_smul a b u := by
    apply SobolevSpaceOn.ext
    funext x
    simp [add_mul]
  zero_smul u := by
    apply SobolevSpaceOn.ext
    funext x
    simp

end BasicInstances

end SobolevSpace

end
