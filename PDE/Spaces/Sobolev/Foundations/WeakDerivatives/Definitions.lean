/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TestFunction
public import PDE.FDeriv.PartialDeriv.Support.Iterated
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Weak derivatives on Euclidean domains

For `Ω ⊆ ℝ^n`, a derivative word `α : List (Fin n)` and `f g : ℝ^n → ℝ`, the relation
`HasWeakDerivativeOn Ω α f g` says that `f` and `g` are locally integrable on `Ω` and

`∫_Ω f ∂^α φ = (-1)^|α| ∫_Ω g φ`

for every smooth compactly supported `φ` with `tsupport φ ⊆ Ω` (Evans §5.2.1, (3)).
The integrals are taken against `domainMeasure n Ω`, Lebesgue measure restricted to `Ω`.

## Main definitions

* `domainMeasure`: Lebesgue measure restricted to `Ω`.
* `HasWeakDerivativeOn`: the weak-derivative relation for a derivative word.

## Main results

* `HasWeakDerivativeOn.append_single`, `HasWeakDerivativeOn.cancel_prefix_append_single`,
  `hasWeakDerivativeOn_of_append_single_chain`: composing and splitting derivative words.
* `HasWeakDerivativeOn.perm`: the relation depends only on the multi-index of the word.
* `HasWeakDerivativeOn.congr_ae`, `hasWeakDerivativeOn_congr_ae`: only the almost-everywhere
  classes of `f` and `g` on `Ω` matter.
* `HasWeakDerivativeOn.mono`: restriction to a measurable subset (for open subsets, compare
  Evans §5.2.3, Theorem 1(iii)).

## How it works

We test against Mathlib's test functions `𝓓((⊤ : Opens (ℝ^n)), ℝ)` on all of `ℝⁿ` whose closed
support lies in `Ω`, and a word acts on a test function through `iteratedPartialDeriv`, which
applies its last letter first. To compose (`HasWeakDerivativeOn.append_single`) we apply the
identity for `α` to the line derivative `∂ᵢφ` (Mathlib's `TestFunction.lineDerivCLM`), whose closed
support stays in `Ω`, and then the first-order identity for `g`; the signs combine to
`(-1)^(|α| + 1)`. `HasWeakDerivativeOn.cancel_prefix_append_single` runs the same computation
backwards, using `((-1)^|α|)² = 1`. Permuting a word changes nothing because the iterated
derivatives of a smooth test function commute (`iteratedPartialDeriv_congr_perm_smooth`, by
induction on the permutation; each swap is the symmetry of second derivatives from Mathlib's
`ContDiffAt.isSymmSndFDerivAt`). Restriction to a measurable `Ω' ⊆ Ω` (`HasWeakDerivativeOn.mono`)
only uses that both integrands vanish off `tsupport φ ⊆ Ω'`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.1, the definition of weak derivatives, (3), p. 256; and
  §5.2.3, Theorem 1(iii), p. 261.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped NNReal

/-- The bundled directional derivative of a smooth test function evaluates to its
Fréchet derivative applied to the direction. This also applies to spacetime tests. -/
theorem testFunction_lineDerivCLM_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
    (φ : 𝓓(Ω, ℝ)) (v x : E) :
    (_root_.TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, ℝ)) x =
      fderiv ℝ φ.toFun x v := by
  rw [_root_.TestFunction.lineDerivCLM_eq_fderivCLM,
    _root_.TestFunction.fderivCLM_apply_of_le φ (by simp)]
  rfl

/-- The Lebesgue measure restricted to a domain `Ω`. -/
abbrev domainMeasure (n : ℕ) (Ω : Set (ℝ^n)) : Measure (ℝ^n) :=
  MeasureTheory.volume.restrict Ω

/-- On the whole space the domain measure is Lebesgue measure, an additive Haar measure. -/
instance isAddHaarMeasure_domainMeasure_univ (n : ℕ) :
    (domainMeasure n Set.univ).IsAddHaarMeasure := by
  simpa only [domainMeasure, MeasureTheory.Measure.restrict_univ] using
    (inferInstance : (MeasureTheory.volume : Measure (ℝ^n)).IsAddHaarMeasure)

/-- Restricting Lebesgue measure to a bounded Euclidean set gives a finite measure. -/
theorem isFiniteMeasure_domainMeasure_of_isBounded {n : ℕ} {Ω : Set (ℝ^n)}
    (hΩ : Bornology.IsBounded Ω) :
    IsFiniteMeasure (domainMeasure n Ω) :=
  MeasureTheory.isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne

variable {n : ℕ} {p : ℝ≥0∞}

/-!
## Support and restriction lemmas

Classical derivatives of a function vanish off its `tsupport`, and weak-derivative
identities on `Ω` restrict to measurable `Ω' ⊆ Ω`, since tests supported in `Ω'` are
supported in `Ω`.
-/

/-- Iterated coordinate differentiation does not enlarge topological support: outside
`tsupport f`, the function and all its iterated derivatives are locally zero. -/
theorem tsupport_iteratedPartialDeriv_subset_tsupport {n : ℕ} (α : List (Fin n)) (f : ℝ^n → ℝ) :
    tsupport (fun x ↦ iteratedPartialDeriv (n := n) α f x) ⊆ tsupport f :=
  PDE.tsupport_iteratedPartialDeriv_subset α f

/-- Every iterated coordinate derivative of a compactly supported function has compact
support. -/
theorem hasCompactSupport_iteratedPartialDeriv {f : ℝ^n → ℝ}
    (hf : HasCompactSupport f) (α : List (Fin n)) :
    HasCompactSupport (fun x ↦ iteratedPartialDeriv (n := n) α f x) :=
  hf.iteratedPartialDeriv α

/-- Every iterated coordinate derivative of a test function remains compactly supported. -/
theorem iteratedPartialDeriv_hasCompactSupport
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (α : List (Fin n)) :
    HasCompactSupport (iteratedPartialDeriv (n := n) α φ.toFun) :=
  hasCompactSupport_iteratedPartialDeriv φ.hasCompactSupport α

/-- Iterated partial derivatives of a smooth function depend only on the associated multi-index,
not on an ordering of the derivative word. -/
theorem iteratedPartialDeriv_congr_perm_smooth {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {α β : List (Fin n)} (hperm : α.Perm β) :
    (fun x ↦ iteratedPartialDeriv (n := n) α f x) =
      fun x ↦ iteratedPartialDeriv (n := n) β f x := by
  classical
  induction hperm generalizing f with
  | nil => rfl
  | cons a _ ih =>
      funext x
      simp [iteratedPartialDeriv, ih hf]
  | swap a b l =>
      funext x
      let g : ℝ^n → ℝ := fun y ↦ iteratedPartialDeriv (n := n) l f y
      have hg := PDE.contDiff_top_iteratedPartialDeriv (n := n) hf l
      simpa [g, iteratedPartialDeriv] using congrFun
        (PDE.partialDeriv_partialDeriv_comm_of_contDiff
          (n := n) a b (hg.of_le (WithTop.coe_le_coe.mpr le_top))).symm x
  | trans _ _ ih₁ ih₂ => exact (ih₁ hf).trans (ih₂ hf)

/-- Finite-order Clairaut theorem for derivative words. Permuting a word `α`
requires only `C^|α|` regularity. -/
theorem iteratedPartialDeriv_congr_perm_of_contDiff {f : ℝ^n → ℝ}
    {α β : List (Fin n)} (hf : ContDiff ℝ (α.length : ℕ∞) f)
    (hperm : α.Perm β) :
    (fun x ↦ iteratedPartialDeriv (n := n) α f x) =
      fun x ↦ iteratedPartialDeriv (n := n) β f x := by
  classical
  induction hperm generalizing f with
  | nil => rfl
  | @cons a l₁ l₂ hp ih =>
      have htail : ContDiff ℝ (l₁.length : ℕ∞) f := by
        apply hf.of_le
        simp
      funext x
      simp [iteratedPartialDeriv, ih htail]
  | @swap a b l =>
      let g : ℝ^n → ℝ := fun y ↦ iteratedPartialDeriv (n := n) l f y
      have hg : ContDiff ℝ 2 g := by
        have hf' : ContDiff ℝ (l.length + 2 : ℕ) f := by
          simpa [List.length_cons, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using hf
        have hlen : l.length ≤ l.length + 2 := by omega
        have h := PDE.contDiff_iteratedPartialDeriv_of_le
          (n := n) (k := l.length + 2) hf' l hlen
        simpa [g] using h
      funext x
      simpa [g, iteratedPartialDeriv] using
        (PDE.partialDeriv_partialDeriv_comm (n := n) a b hg x).symm
  | @trans l₁ l₂ l₃ hp₁ hp₂ ih₁ ih₂ =>
      have hlen : l₁.length = l₂.length := List.Perm.length_eq hp₁
      have hf₂ : ContDiff ℝ (l₂.length : ℕ∞) f := by simpa [hlen] using hf
      exact (ih₁ hf).trans (ih₂ hf₂)

/-- A weak-derivative relation on a set `Ω`, tested against globally smooth functions whose
closed support lies in `Ω`.

We use Mathlib's test-function type `𝓓((⊤ : Opens (ℝ^n)), ℝ)` and require its `tsupport`
(closed support) to lie in `Ω`. When `Ω` is open, this is the test class `C_c^∞(Ω)` of Evans §5.2.1.

Both `f` and its proposed weak derivative `g` are required to lie in `L¹_loc(Ω)`, and the sign is
`(-1)^|α|`, exactly as in Evans §5.2.1, (3).
For an arbitrary set the predicate is still a well-formed test-function relation, but it is not
automatically the standard Sobolev weak derivative: the test class can be too small (and can be
trivial when `Ω` has empty interior), so uniqueness may fail.  Results identifying this relation
with the usual weak derivative therefore require openness or another explicit test-function
density hypothesis. -/
structure HasWeakDerivativeOn (Ω : Set (ℝ^n)) (α : List (Fin n))
    (f g : ℝ^n → ℝ) : Prop where
  /-- The base function belongs to `L¹_loc(Ω)`. -/
  locallyIntegrable_f : MeasureTheory.LocallyIntegrableOn f Ω (MeasureTheory.volume)
  /-- The proposed weak derivative belongs to `L¹_loc(Ω)`. -/
  locallyIntegrable_g : MeasureTheory.LocallyIntegrableOn g Ω (MeasureTheory.volume)
  /-- The distributional integration-by-parts identity. -/
  integral_identity : ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      tsupport φ.toFun ⊆ Ω →
      (∫ x, f x * iteratedPartialDeriv (n := n) α φ.toFun x ∂ (domainMeasure n Ω))
        =
      (-1) ^ α.length *
        (∫ x, g x * φ.toFun x ∂ (domainMeasure n Ω))

/-- A weak-derivative witness can be applied directly to a test function. -/
instance {Ω : Set (ℝ^n)} {α : List (Fin n)} {f g : ℝ^n → ℝ} :
    CoeFun (HasWeakDerivativeOn (n := n) Ω α f g) (fun _ ↦
      ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
        tsupport φ.toFun ⊆ Ω →
        (∫ x, f x * iteratedPartialDeriv (n := n) α φ.toFun x ∂ (domainMeasure n Ω)) =
          (-1) ^ α.length *
            (∫ x, g x * φ.toFun x ∂ (domainMeasure n Ω))) where
  coe h := h.integral_identity

/-- A locally integrable function is its own weak derivative of order zero. -/
theorem hasWeakDerivativeOn_nil {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ}
    (hf : MeasureTheory.LocallyIntegrableOn f Ω MeasureTheory.volume) :
    HasWeakDerivativeOn (n := n) Ω [] f f := by
  refine ⟨hf, hf, ?_⟩
  intro φ _hφ
  simp [iteratedPartialDeriv]

private theorem integrable_mul_compactSupport_of_locallyIntegrableOn
    {Ω : Set (ℝ^n)} {f ψ : ℝ^n → ℝ}
    (hf : MeasureTheory.LocallyIntegrableOn f Ω MeasureTheory.volume)
    (hψcont : Continuous ψ) (hψcompact : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) :
    MeasureTheory.Integrable (fun x ↦ f x * ψ x) (domainMeasure n Ω) := by
  have hfcompact : MeasureTheory.IntegrableOn f (tsupport ψ) MeasureTheory.volume :=
    hf.integrableOn_compact_subset hψΩ hψcompact
  have hmulCompact :
      MeasureTheory.IntegrableOn (fun x ↦ ψ x * f x) (tsupport ψ)
        MeasureTheory.volume :=
    hfcompact.continuousOn_mul hψcont.continuousOn hψcompact
  have hmul : MeasureTheory.Integrable (fun x ↦ ψ x * f x) MeasureTheory.volume :=
    (MeasureTheory.integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_left (f := ψ) (g := f)).trans
        (subset_tsupport ψ))).mp hmulCompact
  simpa only [mul_comm] using hmul.mono_measure Measure.restrict_le_self

/-- The left-hand pairing in the weak-derivative identity is integrable.

This records the analytic content behind the use of the Bochner integral in
`HasWeakDerivativeOn`: local integrability and compact support of the test
function are enough; no global `L^p` hypothesis is needed. -/
theorem HasWeakDerivativeOn.integrable_mul_iteratedPartialDeriv
    {Ω : Set (ℝ^n)} {α : List (Fin n)} {f g : ℝ^n → ℝ}
    (h : HasWeakDerivativeOn (n := n) Ω α f g)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hφ : tsupport φ.toFun ⊆ Ω) :
    MeasureTheory.Integrable
      (fun x ↦ f x * iteratedPartialDeriv (n := n) α φ.toFun x)
      (domainMeasure n Ω) := by
  apply integrable_mul_compactSupport_of_locallyIntegrableOn h.locallyIntegrable_f
  · exact (PDE.contDiff_top_iteratedPartialDeriv (n := n) φ.contDiff α).continuous
  · exact iteratedPartialDeriv_hasCompactSupport (n := n) φ α
  · exact (tsupport_iteratedPartialDeriv_subset_tsupport (n := n) α φ.toFun).trans hφ

/-- The right-hand pairing in the weak-derivative identity is integrable. -/
theorem HasWeakDerivativeOn.integrable_mul_testFunction
    {Ω : Set (ℝ^n)} {α : List (Fin n)} {f g : ℝ^n → ℝ}
    (h : HasWeakDerivativeOn (n := n) Ω α f g)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hφ : tsupport φ.toFun ⊆ Ω) :
    MeasureTheory.Integrable (fun x ↦ g x * φ.toFun x) (domainMeasure n Ω) := by
  exact integrable_mul_compactSupport_of_locallyIntegrableOn h.locallyIntegrable_g
    φ.contDiff.continuous φ.hasCompactSupport hφ

/-- An `Lᵖ(Ω)` function with `p ≥ 1` is locally integrable on `Ω`. -/
theorem memLp_locallyIntegrableOn_domain {Ω : Set (ℝ^n)} {p : ℝ≥0∞} {f : ℝ^n → ℝ}
    (hf : MeasureTheory.MemLp f p (domainMeasure n Ω)) (hp : (1 : ℝ≥0∞) ≤ p) :
    MeasureTheory.LocallyIntegrableOn f Ω (MeasureTheory.volume) := by
  exact MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
    (hf.locallyIntegrable hp)

/--
If `g` is the weak `α`-derivative of `f` on `Ω` and `h` is the weak `i`-derivative of `g` on `Ω`,
then `h` is the weak `(α ++ [i])`-derivative of `f` on `Ω`. This is the composition rule used to
build higher Sobolev derivatives from compatible first-order representatives.
-/
theorem HasWeakDerivativeOn.append_single {Ω : Set (ℝ^n)} {α : List (Fin n)}
    {f g h : ℝ^n → ℝ} (i : Fin n)
    (hfg : HasWeakDerivativeOn (n := n) Ω α f g)
    (hgh : HasWeakDerivativeOn (n := n) Ω [i] g h) :
    HasWeakDerivativeOn (n := n) Ω (α ++ [i]) f h := by
  refine ⟨hfg.locallyIntegrable_f, hgh.locallyIntegrable_g, ?_⟩
  intro φ hφ
  let φi : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) φ
  have hφi_apply :
      φi.toFun = fun x ↦ fderiv ℝ φ.toFun x (EuclideanSpace.single i (1 : ℝ)) := by
    funext x
    change (_root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) φ :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) x = _
    exact testFunction_lineDerivCLM_apply φ _ x
  have hφi : tsupport φi.toFun ⊆ Ω := by
    rw [hφi_apply]
    exact (tsupport_fderiv_apply_subset ℝ (f := φ.toFun) (EuclideanSpace.single i (1 : ℝ))).trans hφ
  have hfirst := hfg φi hφi
  have hlast := hgh φ hφ
  calc
    (∫ x, f x * iteratedPartialDeriv (n := n) (α ++ [i]) φ.toFun x
        ∂ (domainMeasure n Ω)) =
        ∫ x, f x * iteratedPartialDeriv (n := n) α φi.toFun x
          ∂ (domainMeasure n Ω) := by
            apply integral_congr_ae
            filter_upwards with x
            rw [PDE.iteratedPartialDeriv_append_single, hφi_apply]
            change f x * iteratedPartialDeriv (n := n) α
              (fun y ↦ fderiv ℝ φ.toFun y (EuclideanSpace.single i (1 : ℝ))) x = _
            rfl
    _ = (-1) ^ α.length *
          (∫ x, g x * φi.toFun x ∂ (domainMeasure n Ω)) := hfirst
    _ = (-1) ^ (α ++ [i]).length *
          (∫ x, h x * φ.toFun x ∂ (domainMeasure n Ω)) := by
            have hlast' :
                (∫ x, g x * φi.toFun x ∂ (domainMeasure n Ω)) =
                  -(∫ x, h x * φ.toFun x ∂ (domainMeasure n Ω)) := by
              calc
                (∫ x, g x * φi.toFun x ∂ (domainMeasure n Ω)) =
                    ∫ x, g x * iteratedPartialDeriv (n := n) [i] φ.toFun x
                      ∂ (domainMeasure n Ω) := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards [] with x
                  rw [hφi_apply]
                  rfl
                _ = -(∫ x, h x * φ.toFun x ∂ (domainMeasure n Ω)) := by
                  simpa using hlast
            rw [hlast']
            simp [List.length_append, pow_succ]

/--
Cancel a common weak-derivative prefix.  If `g` represents `D^α f` and
`h` represents `D^(α ++ [i]) f`, then `h` is the weak `i`-derivative of
`g`.  This is the converse direction to `HasWeakDerivativeOn.append_single`
needed when extracting first-order Sobolev slices from a packaged `W^{m,p}`
function.
-/
theorem HasWeakDerivativeOn.cancel_prefix_append_single
    {Ω : Set (ℝ^n)} {α : List (Fin n)} {f g h : ℝ^n → ℝ} (i : Fin n)
    (hfg : HasWeakDerivativeOn (n := n) Ω α f g)
    (hfh : HasWeakDerivativeOn (n := n) Ω (α ++ [i]) f h) :
    HasWeakDerivativeOn (n := n) Ω [i] g h := by
  refine ⟨hfg.locallyIntegrable_g, hfh.locallyIntegrable_g, ?_⟩
  intro φ hφ
  let φi : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) φ
  have hφi_apply :
      φi.toFun = fun x ↦ fderiv ℝ φ.toFun x (EuclideanSpace.single i (1 : ℝ)) := by
    funext x
    change (_root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) φ :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) x = _
    exact testFunction_lineDerivCLM_apply φ _ x
  have hφi : tsupport φi.toFun ⊆ Ω := by
    rw [hφi_apply]
    exact (tsupport_fderiv_apply_subset ℝ (f := φ.toFun) (EuclideanSpace.single i (1 : ℝ))).trans hφ
  have hprefix := hfg φi hφi
  have hfull := hfh φ hφ
  have hlhs :
      (∫ x, f x * iteratedPartialDeriv (n := n) α φi.toFun x
          ∂ (domainMeasure n Ω)) =
        ∫ x, f x * iteratedPartialDeriv (n := n) (α ++ [i]) φ.toFun x
          ∂ (domainMeasure n Ω) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [PDE.iteratedPartialDeriv_append_single, hφi_apply]
    change f x * iteratedPartialDeriv (n := n) α
      (fun y ↦ fderiv ℝ φ.toFun y (EuclideanSpace.single i (1 : ℝ))) x = _
    rfl
  let s : ℝ := (-1 : ℝ) ^ α.length
  have hsquare : s * s = 1 := by
    simp [s, ← pow_add]
  have hcore :
      (∫ x, g x * φi.toFun x ∂ (domainMeasure n Ω)) =
        -(∫ x, h x * φ.toFun x ∂ (domainMeasure n Ω)) := by
    calc
      (∫ x, g x * φi.toFun x ∂ (domainMeasure n Ω)) =
          (s * s) * (∫ x, g x * φi.toFun x ∂ (domainMeasure n Ω)) := by
            rw [hsquare, one_mul]
      _ = s * (s * (∫ x, g x * φi.toFun x ∂ (domainMeasure n Ω))) := by
            ring
      _ = s * (∫ x, f x * iteratedPartialDeriv (n := n) α φi.toFun x
            ∂ (domainMeasure n Ω)) := by
            rw [hprefix]
      _ = s * (∫ x, f x * iteratedPartialDeriv (n := n) (α ++ [i]) φ.toFun x
            ∂ (domainMeasure n Ω)) := by rw [hlhs]
      _ = s * (((-1 : ℝ) ^ (α ++ [i]).length) *
            (∫ x, h x * φ.toFun x ∂ (domainMeasure n Ω))) := by rw [hfull]
      _ = -(∫ x, h x * φ.toFun x ∂ (domainMeasure n Ω)) := by
            rw [List.length_append]
            simp only [List.length_singleton, pow_succ]
            change s * (s * (-1) *
              (∫ x, h x * φ.toFun x ∂ (domainMeasure n Ω))) = _
            have hcoeff : s * (s * (-1)) = -1 := by
              calc
                s * (s * (-1)) = -(s * s) := by ring
                _ = -1 := by rw [hsquare]
            rw [← mul_assoc]
            rw [hcoeff]
            ring
  calc
    (∫ x, g x * iteratedPartialDeriv (n := n) [i] φ.toFun x
        ∂ (domainMeasure n Ω)) =
        ∫ x, g x * φi.toFun x ∂ (domainMeasure n Ω) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [hφi_apply]
      rfl
    _ = -(∫ x, h x * φ.toFun x ∂ (domainMeasure n Ω)) := hcore
    _ = (-1 : ℝ) ^ [i].length *
        (∫ x, h x * φ.toFun x ∂ (domainMeasure n Ω)) := by simp

/--
If `D []` is locally integrable on `Ω` and `D (α ++ [i])` is the weak `i`-derivative of `D α` on
`Ω` for every word `α` and every `i`, then `D α` is the weak `α`-derivative of `D []` on `Ω` for
every word `α`. Letters are appended on the right, matching `iteratedPartialDeriv_append_single`.
-/
theorem hasWeakDerivativeOn_of_append_single_chain {Ω : Set (ℝ^n)}
    (D : List (Fin n) → ℝ^n → ℝ)
    (hD0 : MeasureTheory.LocallyIntegrableOn (D []) Ω MeasureTheory.volume)
    (hstep : ∀ (α : List (Fin n)) (i : Fin n),
      HasWeakDerivativeOn (n := n) Ω [i] (D α) (D (α ++ [i]))) :
    ∀ α : List (Fin n), HasWeakDerivativeOn (n := n) Ω α (D []) (D α) := by
  intro α
  have hreverse : ∀ β : List (Fin n),
      HasWeakDerivativeOn (n := n) Ω β.reverse (D []) (D β.reverse) := by
    intro β
    induction β with
    | nil =>
        exact hasWeakDerivativeOn_nil hD0
    | cons i rest ih =>
        simpa only [List.reverse_cons] using
          ih.append_single i (hstep rest.reverse i)
  simpa using hreverse α.reverse

/--
The version of `hasWeakDerivativeOn_of_append_single_chain` through order `k`: if the first-order
steps are given for words of length less than `k`, then `D α` is the weak `α`-derivative of `D []`
on `Ω` for every word `α` of length at most `k`.
-/
theorem hasWeakDerivativeOn_of_append_single_chain_order {Ω : Set (ℝ^n)}
    (k : ℕ) (D : List (Fin n) → ℝ^n → ℝ)
    (hD0 : MeasureTheory.LocallyIntegrableOn (D []) Ω MeasureTheory.volume)
    (hstep : ∀ (α : List (Fin n)) (i : Fin n), α.length < k →
      HasWeakDerivativeOn (n := n) Ω [i] (D α) (D (α ++ [i])))
    (α : List (Fin n)) (hα : α.length ≤ k) :
    HasWeakDerivativeOn (n := n) Ω α (D []) (D α) := by
  have hreverse : ∀ (β : List (Fin n)) (hβ : β.length ≤ k),
      HasWeakDerivativeOn (n := n) Ω β.reverse
        (D []) (D β.reverse) := by
    intro β hβ
    induction β with
    | nil => simpa using hasWeakDerivativeOn_nil (n := n) hD0
    | cons i rest ih =>
        have hrestLt : rest.length < k := by
          simpa using hβ
        have hprefix := ih (Nat.le_of_lt hrestLt)
        have hlast := hstep rest.reverse i (by simpa using hrestLt)
        simpa only [List.reverse_cons] using hprefix.append_single i hlast
  simpa using hreverse α.reverse (by simpa using hα)

/-- Weak derivatives are indexed by commutative multi-indices: permuting the derivative word does
not change the weak-derivative relation. -/
theorem HasWeakDerivativeOn.perm {Ω : Set (ℝ^n)} {α β : List (Fin n)}
    {f g : ℝ^n → ℝ} (hfg : HasWeakDerivativeOn (n := n) Ω α f g)
    (hperm : α.Perm β) :
    HasWeakDerivativeOn (n := n) Ω β f g := by
  refine ⟨hfg.locallyIntegrable_f, hfg.locallyIntegrable_g, ?_⟩
  intro φ hφ
  have hderiv := iteratedPartialDeriv_congr_perm_smooth
    (n := n) φ.contDiff hperm
  have hlen : α.length = β.length := hperm.length_eq
  have hEq := hfg φ hφ
  simpa [hderiv, hlen] using hEq

/-- Replace a function and its weak derivative by almost-everywhere equal representatives. -/
theorem HasWeakDerivativeOn.congr_ae {Ω : Set (ℝ^n)} {α : List (Fin n)}
    {f g f' g' : ℝ^n → ℝ} (hf : HasWeakDerivativeOn (n := n) Ω α f f')
    (hfg : f =ᵐ[domainMeasure n Ω] g) (hf'g' : f' =ᵐ[domainMeasure n Ω] g') :
    HasWeakDerivativeOn (n := n) Ω α g g' := by
  refine ⟨hf.locallyIntegrable_f.congr hfg, hf.locallyIntegrable_g.congr hf'g', ?_⟩
  intro φ hφ
  calc
    (∫ x, g x * iteratedPartialDeriv (n := n) α φ.toFun x ∂ domainMeasure n Ω) =
        ∫ x, f x * iteratedPartialDeriv (n := n) α φ.toFun x ∂ domainMeasure n Ω :=
      MeasureTheory.integral_congr_ae (hfg.symm.mul (Filter.EventuallyEq.refl _ _))
    _ = (-1) ^ α.length * (∫ x, f' x * φ.toFun x ∂ domainMeasure n Ω) := hf φ hφ
    _ = (-1) ^ α.length * (∫ x, g' x * φ.toFun x ∂ domainMeasure n Ω) := by
      exact congrArg (fun I : ℝ ↦ (-1) ^ α.length * I)
        (MeasureTheory.integral_congr_ae
          (hf'g'.mul (Filter.EventuallyEq.refl _ φ.toFun)))

/-- The weak-derivative relation depends only on the almost-everywhere classes
of the base function and proposed derivative on the domain. -/
theorem hasWeakDerivativeOn_congr_ae {Ω : Set (ℝ^n)} {α : List (Fin n)}
    {f g f' g' : ℝ^n → ℝ}
    (hfg : f =ᵐ[domainMeasure n Ω] g) (hf'g' : f' =ᵐ[domainMeasure n Ω] g') :
    HasWeakDerivativeOn (n := n) Ω α f f' ↔ HasWeakDerivativeOn (n := n) Ω α g g' :=
  ⟨fun h ↦ h.congr_ae hfg hf'g', fun h ↦ h.congr_ae hfg.symm hf'g'.symm⟩

/-- Restrict a weak-derivative identity to a measurable subset of its domain. -/
theorem HasWeakDerivativeOn.mono {Ω Ω' : Set (ℝ^n)} {α : List (Fin n)}
    {f g : ℝ^n → ℝ}
    (hΩ' : MeasurableSet Ω') (hΩ'Ω : Ω' ⊆ Ω) (h : HasWeakDerivativeOn (n := n) Ω α f g) :
    HasWeakDerivativeOn (n := n) Ω' α f g := by
  refine ⟨h.locallyIntegrable_f.mono_set hΩ'Ω,
    h.locallyIntegrable_g.mono_set hΩ'Ω, ?_⟩
  intro φ hφΩ'
  have hφΩ : tsupport φ.toFun ⊆ Ω := hφΩ'.trans hΩ'Ω
  have hEq := h φ hφΩ
  -- Restrict both integrals from `Ω` down to `Ω'` using the support conditions.
  have hsuppDeriv :
      Function.support (fun x ↦ iteratedPartialDeriv (n := n) α φ.toFun x) ⊆ Ω' := by
    intro x hx
    have : x ∈ tsupport φ.toFun :=
      (tsupport_iteratedPartialDeriv_subset_tsupport (n := n) (α := α) (f := φ.toFun)) (by
        exact subset_tsupport _ hx)
    exact hφΩ' this
  have hsuppLeft :
      Function.support (fun x ↦ f x * iteratedPartialDeriv (n := n) α φ.toFun x) ⊆ Ω' :=
    (Function.support_mul_subset_right
      (f := f) (g := fun x ↦ iteratedPartialDeriv (n := n) α φ.toFun x)).trans hsuppDeriv
  have hsuppRight :
      Function.support (fun x ↦ g x * φ.toFun x) ⊆ Ω' := by
    -- `support (g*φ) ⊆ support φ ⊆ tsupport φ ⊆ Ω'`
    have hsuppφ : Function.support φ.toFun ⊆ Ω' := (subset_tsupport _).trans hφΩ'
    exact (Function.support_mul_subset_right (f := g) (g := φ.toFun)).trans hsuppφ
  have hμ : (domainMeasure n Ω).restrict Ω' = domainMeasure n Ω' := by
    rw [Measure.restrict_restrict hΩ']
    congr 1
    exact Set.inter_eq_left.2 hΩ'Ω
  have hL :
      (∫ x, f x * iteratedPartialDeriv (n := n) α φ.toFun x ∂ (domainMeasure n Ω)) =
        ∫ x, f x * iteratedPartialDeriv (n := n) α φ.toFun x ∂ (domainMeasure n Ω') := by
    -- Restrict `volume.restrict Ω` to `Ω'`, then simplify `Ω ∩ Ω' = Ω'`.
    have h' :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := domainMeasure n Ω) (s := Ω')
        (f := fun x ↦ f x * iteratedPartialDeriv (n := n) α φ.toFun x)
        (fun x hx ↦ by
          by_contra hfx
          exact hx (hsuppLeft hfx))).symm
    simpa [hμ] using h'
  have hR :
      (∫ x, g x * φ.toFun x ∂ (domainMeasure n Ω)) =
        ∫ x, g x * φ.toFun x ∂ (domainMeasure n Ω') := by
    have h' :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := domainMeasure n Ω) (s := Ω') (f := fun x ↦ g x * φ.toFun x)
        (fun x hx ↦ by
          by_contra hfx
          exact hx (hsuppRight hfx))).symm
    simpa [hμ] using h'
  calc
    (∫ x, f x * iteratedPartialDeriv (n := n) α φ.toFun x ∂ (domainMeasure n Ω')) =
        ∫ x, f x * iteratedPartialDeriv (n := n) α φ.toFun x ∂ (domainMeasure n Ω) := hL.symm
    _ = (-1) ^ α.length * (∫ x, g x * φ.toFun x ∂ (domainMeasure n Ω)) := hEq
    _ = (-1) ^ α.length * (∫ x, g x * φ.toFun x ∂ (domainMeasure n Ω')) := by rw [hR]


end SobolevSpace

end
