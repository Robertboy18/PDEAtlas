/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.Representatives.Definitions
import PDE.DistributionTheory.TestFunction.SmoothMultiplier

/-!
# Compact-support localization for Sobolev functions

Suppose `f` and `g` are supported in a set `K` inside an open set `U`, and `g` is the weak
derivative `∂_i f` on `U`, meaning `∫_U f ∂_i φ = -∫_U g φ` for all test functions `φ`
supported in `U`. Then the same identity holds against every test function supported in any
larger set `Ωbig ⊇ U`, and in particular on all of `ℝ^n`. In practice `K` is compact, but
compactness is not needed: only a cutoff equal to `1` near `K` enters. The argument uses only
the definition of weak derivatives (Evans, PDE, §5.2.1, (3)): multiply a test function on
`Ωbig` by a smooth cutoff `ψ` supported in `U` and equal to `1` near `K`; the product is a test
function on `U`, and since `f` and `g` vanish off `K`, where `ψ ≡ 1`, neither side of the
identity changes. The same germ argument preserves every finite word of coordinate derivatives.
We prove the word-level transport, its first-order specializations, and the `L^p`
transfer it needs. No boundary-chart or `C¹`-domain structure enters.

## Main results

* `memLp_of_support_subset_of_subset`: `L^p` membership on a measurable set `U` transfers to
  any larger domain for functions supported in `U`.
* `hasWeakDerivativeOn_word_of_support_subset_of_cutoff_one_nhds`: transport of any
  finite derivative word from `U` to a larger domain.
* `hasWeakDerivativeOn_word_of_inter_of_cutoff_one_nhds`: the corresponding
  boundary-relative transport from `V ∩ Ω` to `Ω`.
* `hasWeakDerivativeOn_of_support_subset_of_cutoff_one_nhds`: extension of a first
  weak-derivative identity from `U` to a larger domain, given a cutoff equal to `1` near the
  common support `K`.
* `hasWeakDerivativeOn_univ_of_support_subset_of_cutoff_one_nhds`,
  `hasWeakDerivativeInLpOn_of_support_subset_of_cutoff_one_nhds`: the whole-space and `L^p`
  forms.
* `hasWeakDerivativeOn_of_inter_of_cutoff_one_nhds`: for open `V` and `Ωbig`, the identity on
  `V ∩ Ωbig` extends to `Ωbig` when the data are supported in a set near which a cutoff
  supported in `V` is `1`. A test function on `Ωbig` multiplied by that cutoff stays supported
  in `V ∩ Ωbig`, so no test function reaching across the boundary of `Ωbig` is ever needed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.1, (3), p. 256, for the definition of weak derivatives.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.CompactSupportLocalization

open MeasureTheory Set
open scoped ENNReal Topology

variable {n : ℕ}

variable {p : ℝ≥0∞}

/-- An `Lᵖ` function on `U` whose pointwise support lies in `U` remains in
`Lᵖ` on every larger measurable domain. -/
theorem memLp_of_support_subset_of_subset {U Ωbig : Set (ℝ^n)}
    (hUmeas : MeasurableSet U) (hUbig : U ⊆ Ωbig) {f : ℝ^n → ℝ}
    (hsupp : Function.support f ⊆ U)
    (hf : MemLp f p (domainMeasure n U)) :
    MemLp f p (domainMeasure n Ωbig) := by
  have h := (memLp_indicator_iff_restrict (μ := volume.restrict Ωbig) (p := p)
    hUmeas.nullMeasurableSet).2 (by rwa [Measure.restrict_restrict_of_subset hUbig])
  rwa [Set.indicator_eq_self.2 hsupp] at h

/-- The cutoff argument behind both transports below. Let `f` and `g` vanish off `K`, let `χ = 1`
near `K`, and let the test function `χ φ` be supported in a measurable `D ⊆ E`, with
`K ∩ tsupport (χ φ) ⊆ D`. Then the weak-derivative identity on `D` tested against `χ φ` is the
identity on `E` tested against `φ`. -/
private theorem integral_identity_of_cutoff_one_nhds {D E K : Set (ℝ^n)} (hD : MeasurableSet D)
    (hDE : D ⊆ E) (alpha : List (Fin n)) {f g : ℝ^n → ℝ} (hsupp_f : Function.support f ⊆ K)
    (hsupp_g : Function.support g ⊆ K) (chi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hchi1nhds : ∀ x ∈ K, chi.toFun =ᶠ[𝓝 x] 1) (phi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hchiphi : tsupport (TestFunction.mul chi phi).toFun ⊆ D)
    (hKD : ∀ x ∈ K, x ∈ tsupport (TestFunction.mul chi phi).toFun → x ∈ D)
    (hweak : HasWeakDerivativeOn (n := n) D alpha f g) :
    (∫ x, f x * iteratedPartialDeriv (n := n) alpha phi.toFun x ∂domainMeasure n E) =
      (-1) ^ alpha.length * ∫ x, g x * phi.toFun x ∂domainMeasure n E := by
  set chiphi := TestFunction.mul chi phi
  -- `χ φ = φ` near `K`, and the integrands vanish off `K`
  have hnhds (x : ℝ^n) (hx : x ∈ K) : chiphi.toFun =ᶠ[𝓝 x] phi.toFun :=
    (hchi1nhds x hx).mono fun y hy ↦ show chi.toFun y * phi.toFun y = phi.toFun y by
      rw [hy, Pi.one_apply, one_mul]
  have hK {F h₁ h₂ : ℝ^n → ℝ} (hF : Function.support F ⊆ K) (h : ∀ x ∈ K, h₁ x = h₂ x) :
      (fun x ↦ F x * h₁ x) = fun x ↦ F x * h₂ x := funext fun x ↦ by
    by_cases hx : x ∈ K
    · rw [h x hx]
    · rw [Function.notMem_support.1 fun h ↦ hx (hF h), zero_mul, zero_mul]
  -- integrands supported in `D` have the same integral over `D` and over `E`
  have hrestrict {F : ℝ^n → ℝ} (hF : Function.support F ⊆ D) :
      ∫ x, F x ∂domainMeasure n E = ∫ x, F x ∂domainMeasure n D := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      fun x hx ↦ Function.notMem_support.1 fun h ↦ hx (hF h),
      Measure.restrict_restrict hD, inter_eq_left.2 hDE]
  rw [hK hsupp_f fun x hx ↦ (((hnhds x hx).iteratedPartialDeriv alpha).self_of_nhds).symm,
    hrestrict fun x hx ↦ hKD x (hsupp_f (left_ne_zero_of_mul hx))
      (tsupport_iteratedPartialDeriv_subset_tsupport alpha _
        (subset_tsupport _ (right_ne_zero_of_mul hx))),
    hweak chiphi hchiphi, ← hrestrict fun x hx ↦ hKD x (hsupp_g (left_ne_zero_of_mul hx))
      (subset_tsupport _ (right_ne_zero_of_mul hx)),
    hK hsupp_g fun x hx ↦ (hnhds x hx).self_of_nhds]

/-- Arbitrary-order compact-support localization of a weak derivative.

Both representatives are supported in `K ⊆ U`; the auxiliary cutoff is
one on a neighborhood of `K`.  Consequently the identity on `U` may be tested
against the localized test function and then read as the same identity on any
larger domain `OmegaBig`.
-/
theorem hasWeakDerivativeOn_word_of_support_subset_of_cutoff_one_nhds
    {U OmegaBig K : Set (ℝ^n)} (hU : IsOpen U) (hUbig : U ⊆ OmegaBig)
    (hKU : K ⊆ U) (alpha : List (Fin n)) {f g : ℝ^n → ℝ}
    (hsupp_f : Function.support f ⊆ K) (hsupp_g : Function.support g ⊆ K)
    (chi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hchiU : tsupport chi.toFun ⊆ U)
    (hchi1nhds : ∀ x ∈ K, chi.toFun =ᶠ[𝓝 x] 1)
    (hweak : HasWeakDerivativeOn (n := n) U alpha f g) :
    HasWeakDerivativeOn (n := n) OmegaBig alpha f g := by
  -- `f` and `g` are integrable: they are supported in the compact `tsupport χ`
  have hKchi : K ⊆ tsupport chi.toFun := fun x hx ↦
    subset_tsupport _ ((hchi1nhds x hx).eq_of_nhds.trans_ne one_ne_zero)
  have hint {F : ℝ^n → ℝ} (hF : Function.support F ⊆ K) (hloc : LocallyIntegrableOn F U) :
      LocallyIntegrableOn F OmegaBig :=
    ((integrableOn_iff_integrable_of_support_subset (hF.trans hKchi)).mp
      (hloc.integrableOn_compact_subset hchiU chi.hasCompactSupport)).locallyIntegrable
        |>.locallyIntegrableOn OmegaBig
  exact ⟨hint hsupp_f hweak.locallyIntegrable_f, hint hsupp_g hweak.locallyIntegrable_g,
    fun phi _ ↦ integral_identity_of_cutoff_one_nhds hU.measurableSet hUbig alpha hsupp_f hsupp_g
      chi hchi1nhds phi ((tsupport_mul_subset_left (f := chi.toFun) (g := phi.toFun)).trans hchiU)
      (fun x hx _ ↦ hKU hx) hweak⟩

section WordIntersection

variable [Fact (1 ≤ p)]

/-- Localize an arbitrary-order weak derivative from `V ∩ Ω` to
`Ω`. The multiplier is compactly supported in the chart neighborhood
`V`, while the test function supplies compact support inside `Ω`; hence
the argument does not extend through the physical boundary of `Ω`. -/
theorem hasWeakDerivativeOn_word_of_inter_of_cutoff_one_nhds
    {V Ω K : Set (ℝ^n)} (hV : IsOpen V) (hOmega : IsOpen Ω)
    (alpha : List (Fin n)) {f g : ℝ^n → ℝ}
    (hsupp_f : Function.support f ⊆ K)
    (hsupp_g : Function.support g ⊆ K)
    (chi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hchiV : tsupport chi.toFun ⊆ V)
    (hchi1nhds : ∀ x ∈ K, chi.toFun =ᶠ[𝓝 x] 1)
    (hfLp : MemLp f p (domainMeasure n Ω))
    (hgLp : MemLp g p (domainMeasure n Ω))
    (hweak : HasWeakDerivativeOn (n := n) (V ∩ Ω) alpha f g) :
    HasWeakDerivativeOn (n := n) Ω alpha f g :=
  ⟨memLp_locallyIntegrableOn_domain hfLp Fact.out,
    memLp_locallyIntegrableOn_domain hgLp Fact.out, fun phi hphiOmega ↦ by
      have hchiphi : tsupport (TestFunction.mul chi phi).toFun ⊆ V ∩ Ω := fun _ hx ↦
        ⟨hchiV (tsupport_mul_subset_left (f := chi.toFun) (g := phi.toFun) hx),
          hphiOmega (tsupport_mul_subset_right (f := chi.toFun) (g := phi.toFun) hx)⟩
      exact integral_identity_of_cutoff_one_nhds (hV.measurableSet.inter hOmega.measurableSet)
        inter_subset_right alpha hsupp_f hsupp_g chi hchi1nhds phi hchiphi
        (fun _ _ hx ↦ hchiphi hx) hweak⟩

end WordIntersection

/-- A first weak-derivative identity supported in `K ⊆ U` extends from the open set `U` to a
larger domain when a test-function cutoff is identically one near `K`. -/
theorem hasWeakDerivativeOn_of_support_subset_of_cutoff_one_nhds
    {U Ωbig K : Set (ℝ^n)} (hU : IsOpen U) (hUbig : U ⊆ Ωbig)
    (hKU : K ⊆ U) {i : Fin n} {f g : ℝ^n → ℝ}
    (hsupp_f : Function.support f ⊆ K)
    (hsupp_g : Function.support g ⊆ K)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψU : tsupport ψ.toFun ⊆ U)
    (hψ1nhds : ∀ x ∈ K, ψ.toFun =ᶠ[𝓝 x] 1)
    (hweak : HasWeakDerivativeOn (n := n) U [i] f g) :
    HasWeakDerivativeOn (n := n) Ωbig [i] f g := by
  exact hasWeakDerivativeOn_word_of_support_subset_of_cutoff_one_nhds
    hU hUbig hKU [i] hsupp_f hsupp_g ψ hψU hψ1nhds hweak

/-- A compactly supported first weak-derivative identity on an open set extends to all of
`ℝ^n`. -/
theorem hasWeakDerivativeOn_univ_of_support_subset_of_cutoff_one_nhds
    {U K : Set (ℝ^n)} (hU : IsOpen U) (hKU : K ⊆ U) {i : Fin n}
    {f g : ℝ^n → ℝ} (hsupp_f : Function.support f ⊆ K)
    (hsupp_g : Function.support g ⊆ K)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψU : tsupport ψ.toFun ⊆ U)
    (hψ1nhds : ∀ x ∈ K, ψ.toFun =ᶠ[𝓝 x] 1)
    (hweak : HasWeakDerivativeOn (n := n) U [i] f g) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) [i] f g :=
  hasWeakDerivativeOn_of_support_subset_of_cutoff_one_nhds
    (n := n) (U := U) (Ωbig := Set.univ) (K := K)
    hU (subset_univ _) hKU hsupp_f hsupp_g ψ hψU hψ1nhds hweak

/-- The support-extension construction preserves an `L^p` first weak derivative on the larger
domain. -/
theorem hasWeakDerivativeInLpOn_of_support_subset_of_cutoff_one_nhds
    {U Ωbig K : Set (ℝ^n)} (hU : IsOpen U) (hUbig : U ⊆ Ωbig)
    (hKU : K ⊆ U) {i : Fin n} {f g : ℝ^n → ℝ}
    (hsupp_f : Function.support f ⊆ K)
    (hsupp_g : Function.support g ⊆ K)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψU : tsupport ψ.toFun ⊆ U)
    (hψ1nhds : ∀ x ∈ K, ψ.toFun =ᶠ[𝓝 x] 1)
    (hgLp : MemLp g p (domainMeasure n U))
    (hweak : HasWeakDerivativeOn (n := n) U [i] f g) :
    HasWeakDerivativeInLpOn (n := n) Ωbig [i] p f := by
  refine ⟨g, ?_, ?_⟩
  · exact memLp_of_support_subset_of_subset
      hU.measurableSet hUbig (hsupp_g.trans hKU) hgLp
  · exact hasWeakDerivativeOn_of_support_subset_of_cutoff_one_nhds
      hU hUbig hKU hsupp_f hsupp_g ψ hψU hψ1nhds hweak

/-- Localize a weak-derivative identity from `V ∩ Ωbig` to `Ωbig` without
cutting across the boundary of `Ωbig`. -/
theorem hasWeakDerivativeOn_of_inter_of_cutoff_one_nhds
    [Fact (1 ≤ p)]
    {V Ωbig K : Set (ℝ^n)} (hV : IsOpen V) (hΩbig : IsOpen Ωbig)
    {i : Fin n} {f g : ℝ^n → ℝ}
    (hsupp_f : Function.support f ⊆ K)
    (hsupp_g : Function.support g ⊆ K)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (hψ1nhds : ∀ x ∈ K, ψ.toFun =ᶠ[nhds x] 1)
    (hfLp : MemLp f p (domainMeasure n Ωbig))
    (hgLp : MemLp g p (domainMeasure n Ωbig))
    (hweak : HasWeakDerivativeOn (n := n) (V ∩ Ωbig) [i] f g) :
    HasWeakDerivativeOn (n := n) Ωbig [i] f g := by
  exact hasWeakDerivativeOn_word_of_inter_of_cutoff_one_nhds
    hV hΩbig [i] hsupp_f hsupp_g ψ hψV hψ1nhds hfLp hgLp hweak

end SobolevSpace.CompactSupportLocalization
