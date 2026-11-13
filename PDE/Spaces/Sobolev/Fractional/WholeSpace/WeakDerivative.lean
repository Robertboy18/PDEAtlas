/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Real
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.L2Representative
import PDE.Spaces.Sobolev.Fractional.WholeSpace.IntegrationByParts

/-!
# Fractional Sobolev functions have weak derivatives

We connect the fractional scale to the integer-order theory: for a
real element `u` of `H^s(ℝ^n)` with `s ≥ 1`, the real part of its `L²`
representative has a weak derivative in the sense of
`SobolevSpace.HasWeakDerivativeOn`, namely the real part of the `L²`
representative of `∂ᵢ u`.

The analysis is in `Fractional.WholeSpace.IntegrationByParts`; here we pass from complex to real
scalars and check the two local-integrability side conditions. Evans, PDE, §5.8.5, Theorem 8,
obtains the weak derivative of `u` as `((iy)^α û)^∨` and tests it by Plancherel's theorem; we
use the distributional derivative of Mathlib's `BesselPotentialSpace` instead.

## Realness hypothesis

Only `u` is assumed to have a real `L²` representative; realness of `∂ᵢ u` then
follows, by `isRealL2_lineDeriv_of_isRealL2`.  That derivation takes imaginary
parts in the integration-by-parts identity and applies du Bois-Reymond
(`ae_eq_zero_of_integral_contDiff_smul_eq_zero`); no conjugation on tempered
distributions is needed.

## Which notion of "real"

`IsRealL2 (toL2Fun hs u)` is realness of the function representative.  This
is not definitionally the condition defining
`SobolevSpace.Fractional.hsRealSubmodule` in `Fractional.WholeSpace.Real`, which asks
realness of the Bessel representative `toLp u`. For `s ≥ 0`,
`Fractional.WholeSpace.Conjugation` proves that the two conditions are equivalent, so
the results below apply to `HsSpaceReal` after that bridge.

## Main results

* `SobolevSpace.Fractional.isRealL2_lineDeriv_of_isRealL2`: realness of the
  representative passes to the derivative.
* `SobolevSpace.Fractional.hasWeakDerivativeOn_reOfL2`: for `s ≥ 1`, the real
  representative of `∂ᵢ u` is the `i`-th weak derivative of that of `u`.
* `SobolevSpace.Fractional.hasWeakDerivativeOn_reOfL2_two`,
  `SobolevSpace.Fractional.exists_hasWeakDerivativeOn_list`: the second-order
  case and arbitrary derivative words, by iteration.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.1, (1)-(3), p. 256, for weak derivatives, and §5.8.5,
  Theorem 8, pp. 297-298, whose step 2 (p. 298) identifies `((iy)^α û)^∨` with the weak derivative
  `D^α u`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open MeasureTheory SobolevSpace
open TopologicalSpace
open scoped BesselPotentialSpace Distributions ENNReal LineDeriv SchwartzMap

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

open BesselPotentialSpace

/-- The real part of an `L²` function, as a real-valued function. -/
noncomputable def reOfL2 (f : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℝ :=
  fun x ↦ (f x).re

/-- A real `L²` function agrees a.e. with the complexification of its real part. -/
theorem ofReal_reOfL2_ae {f : Lp ℂ 2 (volume : Measure (ℝ^n))} (hf : IsRealL2 f) :
    ∀ᵐ x ∂(volume : Measure (ℝ^n)),
      ((f : ℝ^n → ℂ) x) = ((reOfL2 f x : ℝ) : ℂ) := by
  filter_upwards [hf] with x hx
  refine Complex.ext ?_ ?_ <;> simp [reOfL2, hx]

/-- Real parts add, almost everywhere. -/
theorem reOfL2_add_ae (g h : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    reOfL2 (g + h) =ᵐ[(volume : Measure (ℝ^n))] reOfL2 g + reOfL2 h := by
  filter_upwards [Lp.coeFn_add g h] with x hx
  unfold reOfL2
  rw [hx]
  simp

/-- Real parts commute with real scalars, almost everywhere. -/
theorem reOfL2_smul_ae (c : ℝ) (g : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    reOfL2 ((c : ℂ) • g) =ᵐ[(volume : Measure (ℝ^n))] c • reOfL2 g := by
  filter_upwards [Lp.coeFn_smul (c : ℂ) g] with x hx
  unfold reOfL2
  rw [hx]
  simp

/-- The real part of an `L²` function is locally integrable on `ℝ^n`, since `L²_loc ⊆ L¹_loc`.
This is the side condition `HasWeakDerivativeOn` imposes on the function and its derivative. -/
theorem locallyIntegrableOn_reOfL2 (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    LocallyIntegrableOn (reOfL2 f) Set.univ (volume : Measure (ℝ^n)) := by
  have h : MemLp (reOfL2 f) 2 (volume : Measure (ℝ^n)) := (Lp.memLp f).re
  exact (h.locallyIntegrable (by norm_num)).locallyIntegrableOn _

/-- A complexified test function is continuous with compact support. -/
private theorem continuous_hasCompactSupport_ofTestFunction
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    Continuous (fun x ↦ ((φ x : ℝ) : ℂ))
      ∧ HasCompactSupport (fun x ↦ ((φ x : ℝ) : ℂ)) :=
  ⟨Complex.continuous_ofReal.comp φ.continuous,
    φ.hasCompactSupport.comp_left (g := fun r : ℝ ↦ (r : ℂ)) (by simp)⟩

/-- A complexified real test function times an `L²` function is integrable: the test function
is continuous with compact support and `L²` functions are locally integrable. -/
theorem integrable_testFunction_smul
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (h : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    Integrable (fun x ↦ ((φ x : ℝ) : ℂ) • (h : ℝ^n → ℂ) x)
      (volume : Measure (ℝ^n)) :=
  LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
    ((Lp.memLp h).locallyIntegrable (by norm_num))
    (continuous_hasCompactSupport_ofTestFunction φ).1
    (continuous_hasCompactSupport_ofTestFunction φ).2

/-- If the representative of `u` is real, so is that of `∂ᵢ u`.

Taking imaginary parts in the integration-by-parts identity shows the imaginary
part of the derivative's representative integrates to zero against every smooth
compactly supported function; du Bois-Reymond then forces it to vanish a.e. No
conjugation on tempered distributions is involved. -/
theorem isRealL2_lineDeriv_of_isRealL2 (hs : (1 : ℝ) ≤ s) (i : Fin n) (u : H^{s}(ℝ^n))
    (hu : IsRealL2 (toL2Fun (by linarith : (0 : ℝ) ≤ s) u)) :
    IsRealL2 (toL2Fun (by linarith : (0 : ℝ) ≤ s - 1)
      (lineDerivLinear n s (EuclideanSpace.single i (1 : ℝ)) u)) := by
  have h0 : (0 : ℝ) ≤ s := by linarith
  have h1 : (0 : ℝ) ≤ s - 1 := by linarith
  set f : Lp ℂ 2 (volume : Measure (ℝ^n)) := toL2Fun h0 u with hf
  set g := toL2Fun h1 (lineDerivLinear n s (EuclideanSpace.single i (1 : ℝ)) u) with hg
  change ∀ᵐ x ∂(volume : Measure (ℝ^n)), ((g : ℝ^n → ℂ) x).im = 0
  have hloc : LocallyIntegrable (fun x ↦ ((g : ℝ^n → ℂ) x).im)
      (volume : Measure (ℝ^n)) := ((Lp.memLp g).im).locallyIntegrable (by norm_num)
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  intro φ0 hφ0 hcs0
  have hφtop : ContDiff ℝ (⊤ : ℕ∞) φ0 := by exact_mod_cast hφ0
  let ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) := {
    toFun := φ0
    contDiff' := hφtop
    hasCompactSupport' := hcs0
    tsupport_subset' := Set.subset_univ _
  }
  have hcx := integral_partialDeriv_smul_toL2Fun hs i u ψ
  have hIL : Integrable
      (fun x ↦ (((∂[i] (ψ : ℝ^n → ℝ)) x : ℝ) : ℂ) • (f : ℝ^n → ℂ) x)
      (volume : Measure (ℝ^n)) := by
    let dψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
      _root_.TestFunction.lineDerivCLM ℝ
        (EuclideanSpace.single i (1 : ℝ)) ψ
    have hdψ (x : ℝ^n) :
        dψ x = (∂[i] (ψ : ℝ^n → ℝ)) x := by
      change
        (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) ψ :
            𝓓((⊤ : Opens (ℝ^n)), ℝ)) x = _
      rw [_root_.TestFunction.lineDerivCLM_eq_fderivCLM,
        _root_.TestFunction.fderivCLM_apply_of_le ψ (by simp)]
      rfl
    simpa only [hdψ] using integrable_testFunction_smul dψ f
  have hIR : Integrable (fun x ↦ ((ψ x : ℝ) : ℂ) • (g : ℝ^n → ℂ) x)
      (volume : Measure (ℝ^n)) := integrable_testFunction_smul ψ g
  have himL : (∫ x, (((∂[i] (ψ : ℝ^n → ℝ)) x : ℝ) : ℂ)
        • (f : ℝ^n → ℂ) x).im
      = ∫ x, (∂[i] (ψ : ℝ^n → ℝ)) x * ((f : ℝ^n → ℂ) x).im := by
    rw [show ((∫ x, (((∂[i] (ψ : ℝ^n → ℝ)) x : ℝ) : ℂ)
          • (f : ℝ^n → ℂ) x).im)
        = RCLike.im (∫ x, (((∂[i] (ψ : ℝ^n → ℝ)) x : ℝ) : ℂ)
            • (f : ℝ^n → ℂ) x) from rfl, ← integral_im hIL]
    refine integral_congr_ae ?_
    filter_upwards with x
    simp
  have himR : (∫ x, ((ψ x : ℝ) : ℂ) • (g : ℝ^n → ℂ) x).im
      = ∫ x, ψ x * ((g : ℝ^n → ℂ) x).im := by
    rw [show ((∫ x, ((ψ x : ℝ) : ℂ) • (g : ℝ^n → ℂ) x).im)
        = RCLike.im (∫ x, ((ψ x : ℝ) : ℂ) • (g : ℝ^n → ℂ) x) from rfl,
      ← integral_im hIR]
    refine integral_congr_ae ?_
    filter_upwards with x
    simp
  have hzeroL : (∫ x, (((∂[i] (ψ : ℝ^n → ℝ)) x : ℝ) : ℂ)
      • (f : ℝ^n → ℂ) x).im = 0 := by
    rw [himL]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hu] with x hx
    simp [hx]
  have hfinal : ∫ x, ψ x * ((g : ℝ^n → ℂ) x).im = 0 := by
    have hc := congrArg Complex.im hcx
    rw [hzeroL] at hc
    simp only [Complex.neg_im] at hc
    rw [himR] at hc
    linarith
  simp only [smul_eq_mul]
  exact hfinal

/-- Fractional Sobolev functions have weak derivatives.

For a real element of `H^s(ℝ^n)` with `s ≥ 1`, the real part of its `L²`
representative has, in the sense of `SobolevSpace.HasWeakDerivativeOn`, the real
part of the representative of `∂ᵢ u` as its `i`-th weak derivative. -/
theorem hasWeakDerivativeOn_reOfL2 (hs : (1 : ℝ) ≤ s) (i : Fin n) (u : H^{s}(ℝ^n))
    (hu : IsRealL2 (toL2Fun (by linarith : (0 : ℝ) ≤ s) u)) :
    HasWeakDerivativeOn (n := n) Set.univ [i]
      (reOfL2 (toL2Fun (by linarith : (0 : ℝ) ≤ s) u))
      (reOfL2 (toL2Fun (by linarith : (0 : ℝ) ≤ s - 1)
        (lineDerivLinear n s (EuclideanSpace.single i (1 : ℝ)) u))) where
  locallyIntegrable_f := locallyIntegrableOn_reOfL2 _
  locallyIntegrable_g := locallyIntegrableOn_reOfL2 _
  integral_identity := by
    intro φ _
    have hcx := integral_partialDeriv_smul_toL2Fun hs i u φ
    -- Rewrite each complex integral as the complexification of a real integral.
    have hL : ∫ x, (((∂[i] (φ : ℝ^n → ℝ)) x : ℝ) : ℂ)
          • (toL2Fun (by linarith : (0 : ℝ) ≤ s) u : ℝ^n → ℂ) x
        = ((∫ x, reOfL2 (toL2Fun (by linarith : (0 : ℝ) ≤ s) u) x
            * (∂[i] (φ : ℝ^n → ℝ)) x : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae ?_
      filter_upwards [ofReal_reOfL2_ae hu] with x hx
      rw [hx, smul_eq_mul, ← Complex.ofReal_mul]
      ring_nf
    have hR : ∫ x, ((φ x : ℝ) : ℂ)
          • (toL2Fun (by linarith : (0 : ℝ) ≤ s - 1)
              (lineDerivLinear n s (EuclideanSpace.single i (1 : ℝ)) u) : ℝ^n → ℂ) x
        = ((∫ x, reOfL2 (toL2Fun (by linarith : (0 : ℝ) ≤ s - 1)
            (lineDerivLinear n s (EuclideanSpace.single i (1 : ℝ)) u)) x
              * φ x : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae ?_
      filter_upwards [ofReal_reOfL2_ae (isRealL2_lineDeriv_of_isRealL2 hs i u hu)] with x hx
      rw [hx, smul_eq_mul, ← Complex.ofReal_mul]
      ring_nf
    rw [hL, hR, ← Complex.ofReal_neg] at hcx
    have hreal := Complex.ofReal_injective hcx
    simpa [domainMeasure, iteratedPartialDeriv] using hreal

/-- Every real-valued Schwartz function satisfies the realness hypothesis, in
every `H^s` with `s ≥ 0`.  This is the standard way to produce inputs for the
results above. -/
theorem isRealL2_ofSchwartz (hs : (0 : ℝ) ≤ s) (φ : 𝓢(ℝ^n, ℂ))
    (hφ : ∀ x, (φ x).im = 0) :
    IsRealL2 (toL2Fun hs ((SchwartzMap.memSobolev (s := s) φ).toBesselPotentialSpace)) := by
  rw [toL2Fun_ofSchwartz]
  filter_upwards [φ.coeFn_toLp 2 (volume : Measure (ℝ^n))] with x hx
  rw [hx]
  exact hφ x

/-! ## Iterating to higher order

The composition step is
`SobolevSpace.HasWeakDerivativeOn.append_single`, so higher-order weak
derivatives follow by chaining the first-order result.  The two-index case below
needs no dependent-type machinery: the order of each intermediate space is
determined by the nesting, `H^s → H^{s-1} → H^{s-1-1}`. -/

/-- Second-order weak derivative. For `u ∈ H^s` with `s ≥ 2` and a real
representative, the real representatives of `u` and `∂ⱼ∂ᵢu` are related by the
weak derivative along `[i, j]`. -/
theorem hasWeakDerivativeOn_reOfL2_two (hs : (2 : ℝ) ≤ s) (i j : Fin n)
    (u : H^{s}(ℝ^n)) (hu : IsRealL2 (toL2Fun (by linarith : (0 : ℝ) ≤ s) u)) :
    HasWeakDerivativeOn (n := n) Set.univ [i, j]
      (reOfL2 (toL2Fun (by linarith : (0 : ℝ) ≤ s) u))
      (reOfL2 (toL2Fun (by linarith : (0 : ℝ) ≤ s - 1 - 1)
        (lineDerivLinear n (s - 1) (EuclideanSpace.single j (1 : ℝ))
          (lineDerivLinear n s (EuclideanSpace.single i (1 : ℝ)) u)))) := by
  have hfirst := hasWeakDerivativeOn_reOfL2 (by linarith : (1 : ℝ) ≤ s) i u hu
  have hreal := isRealL2_lineDeriv_of_isRealL2 (by linarith : (1 : ℝ) ≤ s) i u hu
  have hsecond := hasWeakDerivativeOn_reOfL2 (by linarith : (1 : ℝ) ≤ s - 1) j
    (lineDerivLinear n s (EuclideanSpace.single i (1 : ℝ)) u) hreal
  simpa using HasWeakDerivativeOn.append_single (α := [i]) j hfirst hsecond

/-! ## Arbitrary derivative words

The general case is an induction along `HasWeakDerivativeOn.append_single`.  The
order of the resulting element is `s - |α|`, but stating it that way would force
a transport, since `s - ((0 : ℕ) : ℝ)` is not syntactically `s`.  Quantifying the
order existentially and recording `t = s - α.length` as a conjunct avoids every
cast while losing nothing. -/

/-- A function is its own weak derivative along the empty word. -/
theorem hasWeakDerivativeOn_nil (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    HasWeakDerivativeOn (n := n) Set.univ [] (reOfL2 f) (reOfL2 f) where
  locallyIntegrable_f := locallyIntegrableOn_reOfL2 f
  locallyIntegrable_g := locallyIntegrableOn_reOfL2 f
  integral_identity := by
    intro φ _
    simp [iteratedPartialDeriv]

/-- Weak derivatives along an arbitrary word. For `u ∈ H^s` with a real
representative and `|α| ≤ s`, there is an element of `H^{s-|α|}`, again with a
real representative, whose real representative is the `α`-th weak derivative of
that of `u`. -/
theorem exists_hasWeakDerivativeOn_list :
    ∀ (α : List (Fin n)) {s : ℝ} (h0 : (0 : ℝ) ≤ s), (α.length : ℝ) ≤ s →
      ∀ (u : H^{s}(ℝ^n)), IsRealL2 (toL2Fun h0 u) →
      ∃ (t : ℝ) (ht : (0 : ℝ) ≤ t) (v : H^{t}(ℝ^n)),
        t = s - α.length ∧ IsRealL2 (toL2Fun ht v) ∧
          HasWeakDerivativeOn (n := n) Set.univ α
            (reOfL2 (toL2Fun h0 u)) (reOfL2 (toL2Fun ht v)) := by
  intro α
  induction α using List.reverseRecOn with
  | nil =>
      intro s h0 _ u hu
      exact ⟨s, h0, u, by simp, hu, hasWeakDerivativeOn_nil _⟩
  | append_singleton β i ih =>
      intro s h0 hlen u hu
      have hlen' : (β.length : ℝ) + 1 ≤ s := by simpa using hlen
      have hβ : (β.length : ℝ) ≤ s := by linarith
      obtain ⟨t, ht, v, hteq, hvreal, hvweak⟩ := ih h0 hβ u hu
      have ht1 : (1 : ℝ) ≤ t := by rw [hteq]; linarith
      have hstep := hasWeakDerivativeOn_reOfL2 ht1 i v hvreal
      have hreal := isRealL2_lineDeriv_of_isRealL2 ht1 i v hvreal
      refine
        ⟨t - 1, by linarith, lineDerivLinear n t (EuclideanSpace.single i (1 : ℝ)) v,
          ?_, hreal, ?_⟩
      · have hlenβ : (((β ++ [i]).length : ℕ) : ℝ) = (β.length : ℝ) + 1 := by simp
        rw [hteq, hlenβ]; ring
      · exact HasWeakDerivativeOn.append_single i hvweak hstep

end SobolevSpace.Fractional
