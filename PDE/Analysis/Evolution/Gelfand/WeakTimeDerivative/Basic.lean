/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.Triple
public import PDE.Analysis.Evolution.Time.WeakDerivative.Bochner
public import PDE.Analysis.Evolution.Bochner.Duality
public import PDE.Analysis.Evolution.Integrated.TimeTestFunction
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Analysis.Evolution.Integrated.Solution

/-!
# Weak time derivatives in a Gelfand triple

Let `V ↪ H` be a Gelfand triple with inclusion `i`, and let `u ∈ L²(a, b; V)` and
`g ∈ L²(a, b; V*)` be Bochner classes on `Ioc a b`. The relation
`HasGelfandWeakTimeDerivativeOn T u g` says that for every `v ∈ V` and every scalar
test `τ : TimeTest a b` with `τ a = 0` (tests already vanish at `b` by definition),

`∫ g(t)(v) τ(t) dt = -∫ ⟪i(u t), i v⟫_H τ'(t) dt`.

This is the weak derivative `u' = g` of the parabolic theory (Evans, §5.9.2 and §7.1.1),
in which `u` takes values in the energy space, `u'` in its dual, and the two are
compared through the pivot inner product. The tests vanish at both endpoints, so no trace
of `u` is involved. The continuous `H`-valued representative comes from the Lions–Magenes
theorem.

The test class `TimeTest a b` is larger than `C_c^∞((a, b))`: its members are scalar
functions with a derivative at every point of `[a, b]`, square integrable together with
that derivative. Weak limits of the integrated Galerkin equations satisfy the relation
directly. Conversely, the relation implies the classical distributional identity against
smooth compactly supported tests, so it is an instance of the Banach-valued
`HasWeakTimeDerivativeOn` on the open interval.

## Main results

* `HasGelfandWeakTimeDerivativeOn`: the defining identity above.
* `HasGelfandWeakTimeDerivativeOn.congr_ae`, `congr_ae_iff`: the relation transfers along
  almost-everywhere equality of `u` and of `g`.
* `HasGelfandWeakTimeDerivativeOn.zero`, `add`, `sub`, `neg`, `smul`, `sum`, `sum_smul`:
  linearity of the weak derivative under finite linear combinations.
* `HasGelfandWeakTimeDerivativeOn.test_contDiffSupported`: the identity holds against
  every `φ ∈ C_c^∞((a, b))` with `τ' = deriv φ`.
* `HasGelfandWeakTimeDerivativeOn.test_contDiffSupported_doubleDual` and
  `_volume`: the scalarised form against every functional `ℓ ∈ V**`, using that a real
  Hilbert space is reflexive in the concrete sense that every such `ℓ` is evaluation at
  some `v ∈ V` (`exists_eq_evaluation_of_doubleDual`).
* `HasGelfandWeakTimeDerivativeOn.hasWeakTimeDerivativeOn`: the pair
  `(t ↦ T.energyToDual (u t), g)` satisfies `HasWeakTimeDerivativeOn (Ioo a b)`.
* `HasGelfandWeakTimeDerivativeOn.identity_hasWeakTimeDerivativeOn`: for the identity
  triple `V = H`, the dual-encoded relation is the ordinary `V`-valued weak derivative.
* `HasGelfandWeakTimeDerivativeOn.eq`: the weak derivative of a fixed `u` is unique as
  an element of `L²(a, b; V*)`, by the fundamental lemma of the calculus of variations
  (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`).

## Implementation notes

The trajectory `u` enters the identity only through `T.energyToDual (u t) = ⟪i(u t), i ·⟫_H`,
which is why the link to `HasWeakTimeDerivativeOn` is stated for the `V*`-valued curve
`t ↦ T.energyToDual (u t)` rather than for `u` itself. Completeness of `V` is needed
exactly where reflexivity or the inverse Riesz map is used.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2 (the weak derivative of a Banach-valued
  function) and §7.1.1 (the definition of weak solution, with `u' ∈ L²(0, T; H⁻¹)`).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

section GelfandWeakTimeDerivative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `g ∈ L²(a, b; V*)` is the weak time derivative of `u ∈ L²(a, b; V)` in the Gelfand
triple `T`: for every `v ∈ V` and every time test `τ` with `τ(a) = 0` (time tests also vanish
at `b`),

`∫ g(t)(v) τ(t) dt = -∫ ⟪i(u(t)), i(v)⟫_H τ'(t) dt`.

This is the weak derivative of Evans, 2nd ed., §5.9.2, as used in §7.1.1. -/
def HasGelfandWeakTimeDerivativeOn
    {a b : ℝ} (T : GelfandTriple (V := V) (H := H))
    (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
    (g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))) : Prop :=
  ∀ (v : V) (τ : TimeTest a b), τ.toFun a = 0 →
    (∫ t, g t v * τ.toLp t ∂(volume.restrict (Set.Ioc a b))) =
      -(∫ t, inner ℝ (T.inclusion (u t)) (T.inclusion v) * τ.derivToLp t
        ∂(volume.restrict (Set.Ioc a b)))

/-- The weak time derivative relation transfers along almost-everywhere equality of `u` and
of `g`; as `Lp` classes, a.e.-equal functions are equal. -/
theorem HasGelfandWeakTimeDerivativeOn.congr_ae
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g₁ g₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (hu : (u₁ : ℝ → V) =ᵐ[volume.restrict (Set.Ioc a b)] u₂)
    (hg : (g₁ : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)] g₂)
    (h : HasGelfandWeakTimeDerivativeOn T u₁ g₁) :
    HasGelfandWeakTimeDerivativeOn T u₂ g₂ := by
  rwa [← Lp.ext hu, ← Lp.ext hg]

/-- The weak time derivative relation is invariant under almost-everywhere equality of `u` and
of `g`. -/
theorem HasGelfandWeakTimeDerivativeOn.congr_ae_iff
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g₁ g₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (hu : (u₁ : ℝ → V) =ᵐ[volume.restrict (Set.Ioc a b)] u₂)
    (hg : (g₁ : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)] g₂) :
    HasGelfandWeakTimeDerivativeOn T u₁ g₁ ↔
      HasGelfandWeakTimeDerivativeOn T u₂ g₂ := by
  rw [Lp.ext hu, Lp.ext hg]

/-- The zero trajectory has zero weak time derivative. -/
theorem HasGelfandWeakTimeDerivativeOn.zero
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)} :
    HasGelfandWeakTimeDerivativeOn T
      (0 : Lp V 2 (volume.restrict (Set.Ioc a b)))
      (0 : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))) := by
  intro v τ _hτa
  let μab := volume.restrict (Set.Ioc a b)
  have hgzero : ((0 : Lp (StrongDual ℝ V) 2 μab) :
      ℝ → StrongDual ℝ V) =ᵐ[μab] fun _ ↦ 0 :=
    Lp.coeFn_zero (StrongDual ℝ V) 2 μab
  have huzero : ((0 : Lp V 2 μab) : ℝ → V) =ᵐ[μab] fun _ ↦ 0 :=
    Lp.coeFn_zero V 2 μab
  have hleft :
      (∫ t, (0 : Lp (StrongDual ℝ V) 2 μab) t v * τ.toLp t ∂μab) = 0 := by
    calc
      (∫ t, (0 : Lp (StrongDual ℝ V) 2 μab) t v * τ.toLp t ∂μab) =
          ∫ _t : ℝ, (0 : ℝ) ∂μab := by
        apply integral_congr_ae
        filter_upwards [hgzero] with t ht
        rw [ht]
        simp
      _ = 0 := by simp
  have hright :
      (∫ t, inner ℝ (T.inclusion ((0 : Lp V 2 μab) t)) (T.inclusion v) *
        τ.derivToLp t ∂μab) = 0 := by
    calc
      (∫ t, inner ℝ (T.inclusion ((0 : Lp V 2 μab) t)) (T.inclusion v) *
          τ.derivToLp t ∂μab) =
          ∫ _t : ℝ, (0 : ℝ) ∂μab := by
        apply integral_congr_ae
        filter_upwards [huzero] with t ht
        rw [ht, map_zero]
        simp
      _ = 0 := by simp
  rw [hleft, hright]
  simp

/-- If `u₁' = g₁` and `u₂' = g₂` weakly, then `(u₁ - u₂)' = g₁ - g₂` weakly. -/
theorem HasGelfandWeakTimeDerivativeOn.sub
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g₁ g₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h₁ : HasGelfandWeakTimeDerivativeOn T u₁ g₁)
    (h₂ : HasGelfandWeakTimeDerivativeOn T u₂ g₂) :
    HasGelfandWeakTimeDerivativeOn T (u₁ - u₂) (g₁ - g₂) := by
  intro v τ hτa
  let μab := volume.restrict (Set.Ioc a b)
  have hgSub : ((g₁ - g₂ : Lp (StrongDual ℝ V) 2 μab) :
      ℝ → StrongDual ℝ V) =ᵐ[μab] fun t ↦ g₁ t - g₂ t :=
    Lp.coeFn_sub g₁ g₂
  have huSub : ((u₁ - u₂ : Lp V 2 μab) : ℝ → V) =ᵐ[μab]
      fun t ↦ u₁ t - u₂ t := Lp.coeFn_sub u₁ u₂
  have hg₁Int : Integrable (fun t ↦ g₁ t v * τ.toLp t) μab :=
    integrable_dualTimeTest v τ.toLp g₁
  have hg₂Int : Integrable (fun t ↦ g₂ t v * τ.toLp t) μab :=
    integrable_dualTimeTest v τ.toLp g₂
  have hgInt :
      (∫ t, (g₁ - g₂) t v * τ.toLp t ∂μab) =
        (∫ t, g₁ t v * τ.toLp t ∂μab) -
          ∫ t, g₂ t v * τ.toLp t ∂μab := by
    rw [← integral_sub hg₁Int hg₂Int]
    apply integral_congr_ae
    filter_upwards [hgSub] with t ht
    rw [ht, sub_apply]
    ring
  have hu₁Int : Integrable
      (fun t ↦ inner ℝ (T.inclusion (u₁ t)) (T.inclusion v) *
        τ.derivToLp t) μab :=
    integrable_gelfandPivotTimeTest T v τ.derivToLp u₁
  have hu₂Int : Integrable
      (fun t ↦ inner ℝ (T.inclusion (u₂ t)) (T.inclusion v) *
        τ.derivToLp t) μab :=
    integrable_gelfandPivotTimeTest T v τ.derivToLp u₂
  have huInt :
      (∫ t, inner ℝ (T.inclusion ((u₁ - u₂) t)) (T.inclusion v) *
        τ.derivToLp t ∂μab) =
        (∫ t, inner ℝ (T.inclusion (u₁ t)) (T.inclusion v) *
          τ.derivToLp t ∂μab) -
          ∫ t, inner ℝ (T.inclusion (u₂ t)) (T.inclusion v) *
            τ.derivToLp t ∂μab := by
    rw [← integral_sub hu₁Int hu₂Int]
    apply integral_congr_ae
    filter_upwards [huSub] with t ht
    rw [ht, map_sub, inner_sub_left]
    ring
  rw [hgInt, huInt]
  linarith [h₁ v τ hτa, h₂ v τ hτa]

/-- If `u' = g` weakly, then `(-u)' = -g` weakly. -/
theorem HasGelfandWeakTimeDerivativeOn.neg
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasGelfandWeakTimeDerivativeOn T u g) :
    HasGelfandWeakTimeDerivativeOn T (-u) (-g) := by
  have hzero : HasGelfandWeakTimeDerivativeOn T
      (0 : Lp V 2 (volume.restrict (Set.Ioc a b)))
      (0 : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))) :=
    HasGelfandWeakTimeDerivativeOn.zero
  simpa using hzero.sub h

/-- If `u₁' = g₁` and `u₂' = g₂` weakly, then `(u₁ + u₂)' = g₁ + g₂` weakly. -/
theorem HasGelfandWeakTimeDerivativeOn.add
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g₁ g₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h₁ : HasGelfandWeakTimeDerivativeOn T u₁ g₁)
    (h₂ : HasGelfandWeakTimeDerivativeOn T u₂ g₂) :
    HasGelfandWeakTimeDerivativeOn T (u₁ + u₂) (g₁ + g₂) := by
  simpa [sub_eq_add_neg] using h₁.sub h₂.neg

/-- If `u' = g` weakly, then `(c • u)' = c • g` weakly for every real constant `c`. -/
theorem HasGelfandWeakTimeDerivativeOn.smul
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (c : ℝ) (h : HasGelfandWeakTimeDerivativeOn T u g) :
    HasGelfandWeakTimeDerivativeOn T (c • u) (c • g) := by
  intro v τ hτa
  let μab := volume.restrict (Set.Ioc a b)
  have hgSmul : ((c • g : Lp (StrongDual ℝ V) 2 μab) :
      ℝ → StrongDual ℝ V) =ᵐ[μab] fun t ↦ c • g t :=
    Lp.coeFn_smul c g
  have huSmul : ((c • u : Lp V 2 μab) : ℝ → V) =ᵐ[μab] fun t ↦ c • u t :=
    Lp.coeFn_smul c u
  have hgInt : Integrable (fun t ↦ g t v * τ.toLp t) μab :=
    integrable_dualTimeTest v τ.toLp g
  have hleft :
      (∫ t, (c • g) t v * τ.toLp t ∂μab) =
        c * ∫ t, g t v * τ.toLp t ∂μab := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hgSmul] with t ht
    rw [ht]
    simp [mul_assoc]
  have huInt : Integrable
      (fun t ↦ inner ℝ (T.inclusion (u t)) (T.inclusion v) *
        τ.derivToLp t) μab :=
    integrable_gelfandPivotTimeTest T v τ.derivToLp u
  have hright :
      (∫ t, inner ℝ (T.inclusion ((c • u) t)) (T.inclusion v) *
        τ.derivToLp t ∂μab) =
        c * ∫ t, inner ℝ (T.inclusion (u t)) (T.inclusion v) *
          τ.derivToLp t ∂μab := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [huSmul] with t ht
    rw [ht, map_smul]
    rw [real_inner_smul_left]
    ring
  rw [hleft, hright, h v τ hτa]
  ring

/-- If `uᵢ' = gᵢ` weakly for every `i ∈ s`, then `(∑ᵢ uᵢ)' = ∑ᵢ gᵢ` weakly. Applied to
`uᵢ = dᵢ(t) wᵢ`, this differentiates a Galerkin approximant term by term. -/
theorem HasGelfandWeakTimeDerivativeOn.sum
    {ι : Type*} {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    (s : Finset ι)
    (u : ι → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (g : ι → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (h : ∀ i ∈ s, HasGelfandWeakTimeDerivativeOn T (u i) (g i)) :
    HasGelfandWeakTimeDerivativeOn T
      (∑ i ∈ s, u i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (HasGelfandWeakTimeDerivativeOn.zero
      (T := T) (a := a) (b := b) (V := V) (H := H))
  | insert i s his ih =>
      have hi : HasGelfandWeakTimeDerivativeOn T (u i) (g i) :=
        h i (by simp)
      have hs : HasGelfandWeakTimeDerivativeOn T
          (∑ j ∈ s, u j) (∑ j ∈ s, g j) := by
        apply ih
        intro j hj
        exact h j (by simp [hj])
      simpa [Finset.sum_insert his] using hi.add hs

/-- If `uᵢ' = gᵢ` weakly for every `i ∈ s`, then `(∑ᵢ cᵢ • uᵢ)' = ∑ᵢ cᵢ • gᵢ` weakly for
real constants `cᵢ`. -/
theorem HasGelfandWeakTimeDerivativeOn.sum_smul
    {ι : Type*} {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    (s : Finset ι) (c : ι → ℝ)
    (u : ι → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (g : ι → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (h : ∀ i ∈ s, HasGelfandWeakTimeDerivativeOn T (u i) (g i)) :
    HasGelfandWeakTimeDerivativeOn T
      (∑ i ∈ s, c i • u i) (∑ i ∈ s, c i • g i) := by
  apply HasGelfandWeakTimeDerivativeOn.sum
  intro i hi
  exact (h i hi).smul (c i)

/-- The weak derivative identity holds against every smooth scalar `φ` with
`closure (support φ) ⊆ (a, b)`, with `τ' = φ'`:
`∫ g(t)(v) φ(t) dt = -∫ ⟪i(u t), i v⟫_H φ'(t) dt`. -/
theorem HasGelfandWeakTimeDerivativeOn.test_contDiffSupported
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasGelfandWeakTimeDerivativeOn T u g)
    (v : V) (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : closure (Function.support φ) ⊆ Set.Ioo a b) :
    (∫ t, g t v * φ t ∂(volume.restrict (Set.Ioc a b))) =
      -(∫ t, inner ℝ (T.inclusion (u t)) (T.inclusion v) * deriv φ t
        ∂(volume.restrict (Set.Ioc a b))) := by
  let τ : TimeTest a b := TimeTest.ofContDiffSupported φ hφ hsupp
  have hτ := h v τ (TimeTest.ofContDiffSupported_initial_zero φ hφ hsupp)
  calc
    (∫ t, g t v * φ t ∂(volume.restrict (Set.Ioc a b))) =
        ∫ t, g t v * τ.toLp t ∂(volume.restrict (Set.Ioc a b)) := by
      apply integral_congr_ae
      filter_upwards [TimeTest.ofContDiffSupported_toLp_ae φ hφ hsupp]
        with t ht
      rw [ht]
    _ = -(∫ t, inner ℝ (T.inclusion (u t)) (T.inclusion v) * τ.derivToLp t
          ∂(volume.restrict (Set.Ioc a b))) := hτ
    _ = -(∫ t, inner ℝ (T.inclusion (u t)) (T.inclusion v) * deriv φ t
          ∂(volume.restrict (Set.Ioc a b))) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [TimeTest.ofContDiffSupported_derivToLp_ae φ hφ hsupp]
        with t ht
      rw [ht]

/-- Scalarised distributional identity in `V*`: for every `ℓ ∈ V**` and every smooth `φ`
with `closure (support φ) ⊆ (a, b)`,
`∫ ℓ(g t) φ(t) dt = -∫ ℓ(T.energyToDual (u t)) φ'(t) dt`. For a Hilbert space `V`, every
`ℓ ∈ V**` is evaluation at some `v ∈ V`, so this follows from the case of a fixed `v`. -/
theorem HasGelfandWeakTimeDerivativeOn.test_contDiffSupported_doubleDual
    [CompleteSpace V]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasGelfandWeakTimeDerivativeOn T u g)
    (ell : StrongDual ℝ (StrongDual ℝ V))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : closure (Function.support φ) ⊆ Set.Ioo a b) :
    (∫ t, ell (g t) * φ t ∂(volume.restrict (Set.Ioc a b))) =
      -(∫ t, ell (T.energyToDual (u t)) * deriv φ t
        ∂(volume.restrict (Set.Ioc a b))) := by
  obtain ⟨v, hv⟩ := exists_eq_evaluation_of_doubleDual ell
  simpa only [hv, GelfandTriple.energyToDual_apply] using
    h.test_contDiffSupported v φ hφ hsupp

/-- The scalarised distributional identity with integrals over all of `ℝ`. The supports of
`φ` and `φ'` lie in `(a, b)`, so these integrals equal the integrals over `(a, b]`. -/
theorem HasGelfandWeakTimeDerivativeOn.test_contDiffSupported_doubleDual_volume
    [CompleteSpace V]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasGelfandWeakTimeDerivativeOn T u g)
    (ell : StrongDual ℝ (StrongDual ℝ V))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : closure (Function.support φ) ⊆ Set.Ioo a b) :
    (∫ t, ell (g t) * φ t) =
      -(∫ t, ell (T.energyToDual (u t)) * deriv φ t) := by
  have hleftSupport :
      Function.support (fun t ↦ ell (g t) * φ t) ⊆ Set.Ioc a b := by
    intro t ht
    have hφt : t ∈ Function.support φ := by
      intro hzero
      exact ht (by simp [hzero])
    exact Set.Ioo_subset_Ioc_self (hsupp (subset_closure hφt))
  have hrightSupport :
      Function.support
          (fun t ↦ ell (T.energyToDual (u t)) * deriv φ t) ⊆ Set.Ioc a b := by
    intro t ht
    have hdt : t ∈ Function.support (deriv φ) := by
      intro hzero
      exact ht (by simp [hzero])
    exact Set.Ioo_subset_Ioc_self (hsupp (support_deriv_subset hdt))
  rw [(MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := Set.Ioc a b) (f := fun t ↦ ell (g t) * φ t)
      (fun t ht ↦ by
        by_contra hft
        exact ht (hleftSupport hft))).symm,
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := Set.Ioc a b)
      (f := fun t ↦ ell (T.energyToDual (u t)) * deriv φ t)
      (fun t ht ↦ by
        by_contra hft
        exact ht (hrightSupport hft))).symm]
  exact h.test_contDiffSupported_doubleDual ell φ hφ hsupp

/-- If `u' = g` in the Gelfand sense, then the `V*`-valued curve `t ↦ T.energyToDual (u t)`
has weak derivative `g` on `(a, b)` in the Banach-valued sense `HasWeakTimeDerivativeOn`. -/
theorem HasGelfandWeakTimeDerivativeOn.hasWeakTimeDerivativeOn
    [CompleteSpace V]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasGelfandWeakTimeDerivativeOn T u g) :
    PDE.Analysis.Evolution.HasWeakTimeDerivativeOn (Set.Ioo a b)
      (fun t ↦ T.energyToDual (u t)) (fun t ↦ g t) := by
  refine ⟨?_, ?_, ?_⟩
  · have huRestrict : LocallyIntegrable (fun t ↦ u t)
        (volume.restrict (Set.Ioc a b)) :=
      (MeasureTheory.Lp.memLp u).locallyIntegrable (by norm_num)
    have huOn : LocallyIntegrableOn (fun t ↦ u t) (Set.Ioo a b)
        (volume : Measure ℝ) :=
      (locallyIntegrableOn_of_locallyIntegrable_restrict huRestrict).mono_set
        Set.Ioo_subset_Ioc_self
    simpa [Function.comp_def] using T.energyToDual.locallyIntegrableOn_comp huOn
  · have hgRestrict : LocallyIntegrable (fun t ↦ g t)
        (volume.restrict (Set.Ioc a b)) :=
      (MeasureTheory.Lp.memLp g).locallyIntegrable (by norm_num)
    exact
      (locallyIntegrableOn_of_locallyIntegrable_restrict hgRestrict).mono_set
        Set.Ioo_subset_Ioc_self
  · intro ell φ hφ _hφcompact hsupp
    exact h.test_contDiffSupported_doubleDual_volume ell φ hφ hsupp

/--
For the identity triple on a Hilbert space `V`, if the Riesz image of `dx` is the Gelfand weak
derivative of `x`, then `dx` is the `V`-valued weak derivative of `x` on `(a, b)`.
-/
theorem HasGelfandWeakTimeDerivativeOn.identity_hasWeakTimeDerivativeOn
    [CompleteSpace V]
    {a b : ℝ}
    {x dx : Lp V 2 (volume.restrict (Set.Ioc a b))}
    (h : HasGelfandWeakTimeDerivativeOn
      (GelfandTriple.identity V) x
      (rieszToDualLp dx)) :
    PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
      (Set.Ioo a b) (fun t ↦ x t) (fun t ↦ dx t) := by
  let R : StrongDual ℝ V →L[ℝ] V :=
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hdual := h.hasWeakTimeDerivativeOn
  have hmapped := hdual.map R
  have hmeasure :
      volume.restrict (Set.Ioo a b) ≤
        volume.restrict (Set.Ioc a b) :=
    (volume : Measure ℝ).restrict_mono_set Set.Ioo_subset_Ioc_self
  have hx :
      (fun t ↦ R ((GelfandTriple.identity V).energyToDual (x t)))
        =ᵐ[volume.restrict (Set.Ioo a b)] fun t ↦ x t := by
    filter_upwards with t
    apply (InnerProductSpace.toDual ℝ V).injective
    ext v
    change
      inner ℝ
          ((InnerProductSpace.toDual ℝ V).symm
            ((GelfandTriple.identity V).energyToDual (x t))) v =
        inner ℝ (x t) v
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  have hdxDual :
      (rieszToDualLp dx : ℝ → StrongDual ℝ V) =ᵐ[
        volume.restrict (Set.Ioc a b)]
          fun t ↦ InnerProductSpace.toDual ℝ V (dx t) :=
    rieszToDualLp_apply_ae dx
  have hdx :
      (fun t ↦
        R (rieszToDualLp dx t))
        =ᵐ[volume.restrict (Set.Ioo a b)] fun t ↦ dx t := by
    filter_upwards
      [hdxDual.filter_mono (MeasureTheory.ae_mono hmeasure)] with t ht
    rw [ht]
    apply (InnerProductSpace.toDual ℝ V).injective
    ext v
    change
      inner ℝ
          ((InnerProductSpace.toDual ℝ V).symm
            (InnerProductSpace.toDual ℝ V (dx t))) v =
        inner ℝ (dx t) v
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  simpa only [Function.comp_def] using
    hmapped.congr_ae_restrict measurableSet_Ioo hx hdx

/-- The weak time derivative of `u` is unique in `L²(a, b; V*)`. -/
theorem HasGelfandWeakTimeDerivativeOn.eq
    [CompleteSpace V]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g₁ g₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h₁ : HasGelfandWeakTimeDerivativeOn T u g₁)
    (h₂ : HasGelfandWeakTimeDerivativeOn T u g₂) :
    g₁ = g₂ := by
  apply Lp.ext
  have hae := h₁.hasWeakTimeDerivativeOn.ae_eq isOpen_Ioo h₂.hasWeakTimeDerivativeOn
  rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hae

end GelfandWeakTimeDerivative

end PDE.Analysis.Evolution
