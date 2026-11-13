/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Weak derivatives in time

For a real normed space `X`, a time set `U ⊆ ℝ`, and locally Bochner integrable
`f, g : ℝ → X` on `U`, we say that `g` is the weak time derivative of `f` on `U`,
`HasWeakTimeDerivativeOn U f g`, when

`∫ ℓ(g t) φ(t) dt = -∫ ℓ(f t) φ'(t) dt`

for every `φ ∈ C_c^∞` with `closure (support φ) ⊆ U` and every `ℓ ∈ X*`.
Testing through continuous linear functionals gives a scalar integral identity;
the definition and the results here do not require completeness of `X`.
On an open time domain this is the weak time derivative of Evans §5.9.2, tested through
functionals in `X*` rather than stated as an identity in `X`; for a Banach space `X` the
two agree by the Hahn–Banach theorem. The definition also accepts
arbitrary `U`, with the same support restriction on tests. Taking `U = Set.univ`
gives the global predicate.

We prove the elementary calculus of the relation: restriction to smaller sets,
naturality under bounded linear maps, linearity, and invariance under a.e. changes of `f`
and `g`. Localisation lemmas (Leibniz rule with a cutoff, gluing) are in
`PDE.Analysis.Evolution.Time.WeakDerivative.Localization`, and the transport to Euclidean
coordinates, which connects with the Sobolev-space machinery, is in
`PDE.Analysis.Evolution.Time.WeakDerivative.Euclidean`.

## Main results

* `HasWeakTimeDerivativeOn`: the definition, with local integrability of both `f` and `g`
  built in.
* `HasWeakTimeDerivativeOn.integrable_mul_test`, `integrable_smul_test`: a locally
  integrable function times a continuous compactly supported test with support in `U` is
  globally integrable. Applying this to `φ` and `φ'` gives integrability of
  both tested terms in the defining identity.
* `HasWeakTimeDerivativeOn.mono`, `map`, `neg`, `add`, `sub`: restriction to `W ⊆ U`,
  commutation with `L : X →L[ℝ] Y`, and linearity.
* `HasWeakTimeDerivativeOn.congr_ae`, `congr_ae_restrict`: the relation depends only on
  the a.e. classes of `f` and `g` (on `ℝ`, or only on `U` when `U` is measurable).

## Implementation notes

Local integrability and compact test support ensure that the tested integrands
are integrable; the defining equality alone would not express this condition,
since Mathlib assigns value `0` to the integral of a nonintegrable function.
On an open interval, the tests vanish near its endpoints. The relation therefore
imposes no endpoint trace condition. If a trajectory has nonzero endpoint traces,
its zero extension can instead have Dirac masses in its distributional derivative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2 (the weak derivative of a function of time with values
  in a Banach space). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Local weak differentiation in time for functions valued in a real normed space.
The definition records local Bochner integrability as well as the standard
distributional identity against smooth scalar tests whose topological
support lies in `U`.  Including integrability is essential: Lean's Bochner
integral is defined to be zero for a nonintegrable function, so the identity
alone would not characterize a distributional derivative.

On `Set.univ`, this is the global weak-time-derivative predicate. On a proper
open interval, compactly supported tests vanish near both endpoints, so the
relation places no condition on endpoint traces or values outside the interval.

Nothing in the definition is specific to time: it is the weak derivative of any function of
one real variable, and the De Gregorio profile files apply it to the spatial variable of a
stationary profile. -/
structure HasWeakTimeDerivativeOn (U : Set ℝ) (f g : ℝ → X) : Prop where
  /-- The trajectory is locally Bochner integrable in the time domain. -/
  locallyIntegrable_f : LocallyIntegrableOn f U (volume : Measure ℝ)
  /-- The proposed derivative is locally Bochner integrable there. -/
  locallyIntegrable_g : LocallyIntegrableOn g U (volume : Measure ℝ)
  /-- Distributional integration by parts against `C_c^∞(U)`. -/
  integral_eq : ∀ (ell : StrongDual ℝ X) (φ : ℝ → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    closure (Function.support φ) ⊆ U →
    (∫ t, ell (g t) * φ t) = -(∫ t, ell (f t) * deriv φ t)

namespace HasWeakTimeDerivativeOn

/-- A locally integrable scalar function can be paired globally with a
continuous compactly supported test whose topological support lies in the
local domain. -/
theorem integrable_mul_test
    {U : Set ℝ} {q φ : ℝ → ℝ}
    (hq : LocallyIntegrableOn q U (volume : Measure ℝ))
    (hφ : Continuous φ) (hφcompact : HasCompactSupport φ)
    (hsupp : closure (Function.support φ) ⊆ U) :
    Integrable (fun t ↦ q t * φ t) (volume : Measure ℝ) := by
  let K := closure (Function.support φ)
  have hqK : IntegrableOn q K (volume : Measure ℝ) :=
    hq.integrableOn_compact_subset hsupp hφcompact
  have hprodK : IntegrableOn (fun t ↦ q t * φ t) K
      (volume : Measure ℝ) :=
    hqK.mul_continuousOn hφ.continuousOn hφcompact
  have hsupport : Function.support (fun t ↦ q t * φ t) ⊆ K := by
    intro t ht
    apply subset_closure
    intro hzero
    exact ht (by simp [hzero])
  have hself : K.indicator (fun t ↦ q t * φ t) = fun t ↦ q t * φ t :=
    Set.indicator_eq_self.2 hsupport
  rw [← hself]
  exact (integrable_indicator_iff
    (show MeasurableSet K from hφcompact.measurableSet)).2 hprodK

/-- Banach-valued version of `integrable_mul_test`. -/
theorem integrable_smul_test
    {U : Set ℝ} {f : ℝ → X} {φ : ℝ → ℝ}
    (hf : LocallyIntegrableOn f U (volume : Measure ℝ))
    (hφ : Continuous φ) (hφcompact : HasCompactSupport φ)
    (hsupp : closure (Function.support φ) ⊆ U) :
    Integrable (fun t ↦ φ t • f t) (volume : Measure ℝ) := by
  let K := closure (Function.support φ)
  have hfK : IntegrableOn f K (volume : Measure ℝ) :=
    hf.integrableOn_compact_subset hsupp hφcompact
  have hprodK : IntegrableOn (fun t ↦ φ t • f t) K
      (volume : Measure ℝ) :=
    hfK.continuousOn_smul hφ.continuousOn hφcompact
  have hsupport : Function.support (fun t ↦ φ t • f t) ⊆ K := by
    intro t ht
    apply subset_closure
    intro hzero
    exact ht (by simp [hzero])
  have hself : K.indicator (fun t ↦ φ t • f t) = fun t ↦ φ t • f t :=
    Set.indicator_eq_self.2 hsupport
  rw [← hself]
  exact (integrable_indicator_iff
    (show MeasurableSet K from hφcompact.measurableSet)).2 hprodK

/-- A local weak derivative restricts to every smaller time domain. -/
theorem mono {U W : Set ℝ} {f g : ℝ → X}
    (h : HasWeakTimeDerivativeOn U f g) (hWU : W ⊆ U) :
    HasWeakTimeDerivativeOn W f g where
  locallyIntegrable_f := h.locallyIntegrable_f.mono_set hWU
  locallyIntegrable_g := h.locallyIntegrable_g.mono_set hWU
  integral_eq := by
    intro ell φ hφ hφcompact hsupp
    exact h.integral_eq ell φ hφ hφcompact (hsupp.trans hWU)

/-- Continuous linear maps commute with local weak differentiation. -/
theorem map
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) {U : Set ℝ} {f g : ℝ → X}
    (h : HasWeakTimeDerivativeOn U f g) :
    HasWeakTimeDerivativeOn U (L ∘ f) (L ∘ g) where
  locallyIntegrable_f := L.locallyIntegrableOn_comp h.locallyIntegrable_f
  locallyIntegrable_g := L.locallyIntegrableOn_comp h.locallyIntegrable_g
  integral_eq := by
    intro ell φ hφ hφcompact hsupp
    simpa [Function.comp_def] using
      h.integral_eq (ell.comp L) φ hφ hφcompact hsupp

/-- Negation commutes with local weak differentiation. -/
theorem neg
    {U : Set ℝ} {f g : ℝ → X}
    (h : HasWeakTimeDerivativeOn U f g) :
    HasWeakTimeDerivativeOn U (fun t ↦ -f t) (fun t ↦ -g t) := by
  simpa only [Function.comp_def, neg_apply,
    ContinuousLinearMap.id_apply] using
    h.map (-(ContinuousLinearMap.id ℝ X))

/-- Local Banach-valued weak derivatives add. -/
theorem add
    {U : Set ℝ} {f₁ g₁ f₂ g₂ : ℝ → X}
    (h₁ : HasWeakTimeDerivativeOn U f₁ g₁)
    (h₂ : HasWeakTimeDerivativeOn U f₂ g₂) :
    HasWeakTimeDerivativeOn U
      (fun t ↦ f₁ t + f₂ t) (fun t ↦ g₁ t + g₂ t) where
  locallyIntegrable_f :=
    h₁.locallyIntegrable_f.add h₂.locallyIntegrable_f
  locallyIntegrable_g :=
    h₁.locallyIntegrable_g.add h₂.locallyIntegrable_g
  integral_eq := by
    intro ell φ hφ hφcompact hsupp
    have hφContinuous : Continuous φ := hφ.continuous
    have hdφ : ContDiff ℝ (⊤ : ℕ∞) (deriv φ) :=
      (contDiff_infty_iff_deriv.mp hφ).2
    have hdφCompact : HasCompactSupport (deriv φ) := hφcompact.deriv
    have hdφSupp :
        closure (Function.support (deriv φ)) ⊆ U :=
      tsupport_deriv_subset.trans hsupp
    have hg₁ :
        Integrable (fun t ↦ ell (g₁ t) * φ t) :=
      integrable_mul_test
        (ell.locallyIntegrableOn_comp h₁.locallyIntegrable_g)
        hφContinuous hφcompact hsupp
    have hg₂ :
        Integrable (fun t ↦ ell (g₂ t) * φ t) :=
      integrable_mul_test
        (ell.locallyIntegrableOn_comp h₂.locallyIntegrable_g)
        hφContinuous hφcompact hsupp
    have hf₁ :
        Integrable (fun t ↦ ell (f₁ t) * deriv φ t) :=
      integrable_mul_test
        (ell.locallyIntegrableOn_comp h₁.locallyIntegrable_f)
        hdφ.continuous hdφCompact hdφSupp
    have hf₂ :
        Integrable (fun t ↦ ell (f₂ t) * deriv φ t) :=
      integrable_mul_test
        (ell.locallyIntegrableOn_comp h₂.locallyIntegrable_f)
        hdφ.continuous hdφCompact hdφSupp
    calc
      (∫ t, ell (g₁ t + g₂ t) * φ t) =
          ∫ t, (ell (g₁ t) * φ t + ell (g₂ t) * φ t) := by
            apply integral_congr_ae
            filter_upwards with t
            simp only [map_add]
            ring
      _ = (∫ t, ell (g₁ t) * φ t) +
          ∫ t, ell (g₂ t) * φ t :=
        integral_add hg₁ hg₂
      _ = -(∫ t, ell (f₁ t) * deriv φ t) -
          (∫ t, ell (f₂ t) * deriv φ t) := by
        rw [h₁.integral_eq ell φ hφ hφcompact hsupp,
          h₂.integral_eq ell φ hφ hφcompact hsupp]
        ring
      _ = -((∫ t, ell (f₁ t) * deriv φ t) +
          ∫ t, ell (f₂ t) * deriv φ t) := by ring
      _ = -(∫ t, ell (f₁ t + f₂ t) * deriv φ t) := by
        congr 1
        rw [← integral_add hf₁ hf₂]
        apply integral_congr_ae
        filter_upwards with t
        simp only [map_add]
        ring

/-- Local Banach-valued weak derivatives subtract. -/
theorem sub
    {U : Set ℝ} {f₁ g₁ f₂ g₂ : ℝ → X}
    (h₁ : HasWeakTimeDerivativeOn U f₁ g₁)
    (h₂ : HasWeakTimeDerivativeOn U f₂ g₂) :
    HasWeakTimeDerivativeOn U
      (fun t ↦ f₁ t - f₂ t) (fun t ↦ g₁ t - g₂ t) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- Local weak differentiation is invariant under almost-everywhere changes
of both the trajectory and its derivative.  This is essential when an
endpoint extension is first constructed canonically in `V*` and then
identified with a reflected `V`-valued representative away from finitely
many junction points. -/
theorem congr_ae
    {U : Set ℝ} {f f' g g' : ℝ → X}
    (h : HasWeakTimeDerivativeOn U f g)
    (hff' : f =ᵐ[volume] f') (hgg' : g =ᵐ[volume] g') :
    HasWeakTimeDerivativeOn U f' g' where
  locallyIntegrable_f :=
    LocallyIntegrableOn.congr
      (hff'.filter_mono MeasureTheory.ae_restrict_le) h.locallyIntegrable_f
  locallyIntegrable_g :=
    LocallyIntegrableOn.congr
      (hgg'.filter_mono MeasureTheory.ae_restrict_le) h.locallyIntegrable_g
  integral_eq := by
    intro ell φ hφ hφcompact hsupp
    calc
      (∫ t, ell (g' t) * φ t) = ∫ t, ell (g t) * φ t := by
        apply integral_congr_ae
        filter_upwards [hgg'] with t ht
        rw [ht]
      _ = -(∫ t, ell (f t) * deriv φ t) :=
        h.integral_eq ell φ hφ hφcompact hsupp
      _ = -(∫ t, ell (f' t) * deriv φ t) := by
        apply congrArg Neg.neg
        apply integral_congr_ae
        filter_upwards [hff'] with t ht
        rw [ht]

/--
Replacing `f` and `g` by functions equal to them almost everywhere on a
measurable time domain `U` preserves their weak-derivative relation.
Both `φ` and `φ'` vanish outside `U`, so equality outside `U` is not
needed. In particular, the result applies when two extensions agree on
the original interval but differ beyond its endpoints.
-/
theorem congr_ae_restrict
    {U : Set ℝ} (hU : MeasurableSet U)
    {f f' g g' : ℝ → X}
    (h : HasWeakTimeDerivativeOn U f g)
    (hff' : f =ᵐ[volume.restrict U] f')
    (hgg' : g =ᵐ[volume.restrict U] g') :
    HasWeakTimeDerivativeOn U f' g' where
  locallyIntegrable_f :=
    LocallyIntegrableOn.congr hff' h.locallyIntegrable_f
  locallyIntegrable_g :=
    LocallyIntegrableOn.congr hgg' h.locallyIntegrable_g
  integral_eq := by
    intro ell φ hφ hφcompact hsupp
    have hffOn :
        ∀ᵐ t ∂volume, t ∈ U → f t = f' t :=
      (MeasureTheory.ae_restrict_iff' hU).1 hff'
    have hggOn :
        ∀ᵐ t ∂volume, t ∈ U → g t = g' t :=
      (MeasureTheory.ae_restrict_iff' hU).1 hgg'
    have hderivSupp :
        closure (Function.support (deriv φ)) ⊆ U :=
      tsupport_deriv_subset.trans hsupp
    calc
      (∫ t, ell (g' t) * φ t) =
          ∫ t, ell (g t) * φ t := by
        apply integral_congr_ae
        filter_upwards [hggOn] with t ht
        by_cases htU : t ∈ U
        · rw [ht htU]
        · have hφzero : φ t = 0 := by
            by_contra hne
            exact htU (hsupp (subset_closure
              (Function.mem_support.mpr hne)))
          simp [hφzero]
      _ = -(∫ t, ell (f t) * deriv φ t) :=
        h.integral_eq ell φ hφ hφcompact hsupp
      _ = -(∫ t, ell (f' t) * deriv φ t) := by
        apply congrArg Neg.neg
        apply integral_congr_ae
        filter_upwards [hffOn] with t ht
        by_cases htU : t ∈ U
        · rw [ht htU]
        · have hderivZero : deriv φ t = 0 := by
            by_contra hne
            exact htU (hderivSupp (subset_closure
              (Function.mem_support.mpr hne)))
          simp [hderivZero]

end HasWeakTimeDerivativeOn

end PDE.Analysis.Evolution
