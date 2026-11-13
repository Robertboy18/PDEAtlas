/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.Coordinate
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import PDE.Analysis.Evolution.Time.WeakDerivative.AbsolutelyContinuous
import PDE.DistributionTheory.TestFunction

/-!
# Reconstruction of weak derivatives from coordinate-line ACL data

We prove the converse direction of the ACL characterization. If
locally integrable fields have, on almost every line parallel to a selected
coordinate, an absolutely continuous representative whose classical
derivative is the corresponding slice of the second field, then the second
field is the selected weak derivative of the first.

Together with `Slicing.ACL` this gives both directions of the ACL
characterization of `W^{1,1}(ℝ^(n+1))` along a coordinate direction. The
proof is integration by parts on each line, where absolute continuity makes
the classical formula valid (through the one-dimensional weak derivative
theory of `PDE.Analysis.Evolution`), followed by Fubini's theorem over the
volume-preserving coordinate split of `Slicing.Coordinate`.

## Main results

* `hasWeakDerivativeOn_of_locallyIntegrable_ae_coordinate_acl`: if `f, g` are locally
  integrable and for
  almost every `y` the slice `t ↦ f (y, t)` has a representative `r y` that is
  absolutely continuous on compact intervals with `(r y)' = g (y, ·)` almost
  everywhere, then `g` is the weak derivative `∂ᵢ f` on `ℝ^(n+1)`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 8, for the absolutely continuous representative of a `W^{1,p}` function on
  an interval.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.2, p. 259, which states this one-dimensional
  characterization, leaves it to the exercises, and remarks that so simple a characterization is
  only available for `n = 1`.
  <https://doi.org/10.1090/gsm/019>
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  Chapman and Hall/CRC, 2015, Chapter 4, Sobolev Functions, pp. 158-207, for absolute continuity of
  Sobolev functions on lines.
  <https://doi.org/10.1201/b18333>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.Slices

open Function MeasureTheory Set

private abbrev AmbientTestFunction (m : ℕ) :=
  TestFunction
    (⊤ : TopologicalSpace.Opens (ℝ^m))
    ℝ (⊤ : ℕ∞)

private theorem integrable_mul_continuous_compact
    {m : ℕ} {q ψ : ℝ^m → ℝ}
    (hq : LocallyIntegrableOn q univ volume) (hψ : Continuous ψ)
    (hψcompact : HasCompactSupport ψ) :
    Integrable (fun x ↦ q x * ψ x) volume := by
  let K := closure (support ψ)
  have hqK : IntegrableOn q K volume := hq.integrableOn_compact_subset (subset_univ K) hψcompact
  have hprodK : IntegrableOn (fun x ↦ q x * ψ x) K volume :=
    hqK.mul_continuousOn hψ.continuousOn hψcompact
  have hsupport : support (fun x ↦ q x * ψ x) ⊆ K := by
    intro x hx
    apply subset_closure
    intro hzero
    exact hx (by simp [hzero])
  have hself : K.indicator (fun x ↦ q x * ψ x) =
      fun x ↦ q x * ψ x :=
    indicator_eq_self.2 hsupport
  rw [← hself]
  exact (integrable_indicator_iff hψcompact.measurableSet).2 hprodK

private theorem measurePreserving_joinCoordinate
    {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving
      (coordinateMeasurableEquiv i).symm
      ((volume : Measure (ℝ^n)).prod volume)
      (volume : Measure (ℝ^(n + 1))) := by
  simpa only [Measure.volume_eq_prod] using
    MeasurePreserving.symm
      (coordinateMeasurableEquiv i)
      (measurePreserving_coordinateMeasurableEquiv i)

private theorem integral_eq_iterated_coordinate
    {n : ℕ} (i : Fin (n + 1)) {q : ℝ^(n + 1) → ℝ}
    (hq : Integrable q volume) :
    (∫ x, q x) =
      ∫ y : ℝ^n, ∫ t : ℝ, q (joinCoordinate i (y, t)) := by
  have hqProd :
      Integrable (fun p : ℝ^n × ℝ ↦ q (joinCoordinate i p))
        ((volume : Measure (ℝ^n)).prod volume) := by
    simpa only [Function.comp_def, coordinateMeasurableEquiv_symm_apply] using
      (measurePreserving_joinCoordinate i).integrable_comp_of_integrable hq
  calc
    (∫ x, q x) =
        ∫ p : ℝ^n × ℝ, q (joinCoordinate i p)
          ∂((volume : Measure (ℝ^n)).prod volume) := by
      simpa only [coordinateMeasurableEquiv_symm_apply] using
        ((measurePreserving_joinCoordinate i).integral_comp' q).symm
    _ = ∫ y : ℝ^n, ∫ t : ℝ, q (joinCoordinate i (y, t)) :=
      integral_prod _ hqProd

private theorem integral_eq_neg_of_ae_iterated
    {n : ℕ} (i : Fin (n + 1))
    {qLeft qRight : ℝ^(n + 1) → ℝ}
    (hqLeft : Integrable qLeft volume)
    (hqRight : Integrable qRight volume)
    (hline :
      ∀ᵐ y : ℝ^n,
        (∫ t : ℝ, qLeft (joinCoordinate i (y, t))) =
          -(∫ t : ℝ, qRight (joinCoordinate i (y, t)))) :
    (∫ x, qLeft x) = -(∫ x, qRight x) := by
  calc
    (∫ x, qLeft x) =
        ∫ y : ℝ^n, ∫ t : ℝ, qLeft (joinCoordinate i (y, t)) :=
      integral_eq_iterated_coordinate i hqLeft
    _ = ∫ y : ℝ^n, -(∫ t : ℝ, qRight (joinCoordinate i (y, t))) :=
      integral_congr_ae hline
    _ = -(∫ y : ℝ^n, ∫ t : ℝ, qRight (joinCoordinate i (y, t))) := by
      rw [integral_neg]
    _ = -(∫ x, qRight x) := by
      rw [integral_eq_iterated_coordinate i hqRight]

private theorem coordinateLine_integral_identity
    {n : ℕ} (i : Fin (n + 1))
    {f g : ℝ^(n + 1) → ℝ} {r : ℝ → ℝ}
    (φ : TestFunction
      (⊤ : TopologicalSpace.Opens (ℝ^(n + 1)))
      ℝ (⊤ : ℕ∞))
    (y : ℝ^n)
    (hrep : r =ᵐ[volume] coordinateSlice i f y)
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval r a b)
    (hderiv : ∀ᵐ t, HasDerivAt r (coordinateSlice i g y t) t) :
    (∫ t,
        coordinateSlice i f y t *
          coordinateDerivativeInSplit i φ.toFun (y, t)) =
      -(∫ t, coordinateSlice i g y t * coordinateSlice i φ.toFun y t) := by
  have hrLocal : LocallyIntegrable r (volume : Measure ℝ) := by
    intro x
    have hleft : x - 1 < x := by linarith
    have hright : x < x + 1 := by linarith
    have hle : x - 1 ≤ x + 1 := by linarith
    exact ⟨Icc (x - 1) (x + 1), Icc_mem_nhds hleft hright,
      by
        simpa [uIcc_of_le hle] using
          (hAC (x - 1) (x + 1)).continuousOn.integrableOn_uIcc
            (μ := (volume : Measure ℝ))⟩
  have hgLineLocal :
      LocallyIntegrable (coordinateSlice i g y) (volume : Measure ℝ) := by
    have hderivEq : deriv r =ᵐ[volume] coordinateSlice i g y :=
      hderiv.mono fun _ ht ↦ ht.deriv
    intro x
    have hleft : x - 1 < x := by linarith
    have hright : x < x + 1 := by linarith
    have hle : x - 1 ≤ x + 1 := by linarith
    have hInterval : IntervalIntegrable (coordinateSlice i g y) volume
        (x - 1) (x + 1) :=
      (hAC (x - 1) (x + 1)).intervalIntegrable_deriv.congr_ae
        (ae_restrict_of_ae hderivEq)
    exact ⟨Icc (x - 1) (x + 1), Icc_mem_nhds hleft hright,
      (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mp hInterval⟩
  have hweak :
      PDE.Analysis.Evolution.HasWeakTimeDerivativeOn Set.univ
        r (coordinateSlice i g y) :=
    PDE.Analysis.Evolution.HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval
      hrLocal hgLineLocal hAC hderiv
  have htestSmooth :
      ContDiff ℝ (⊤ : ℕ∞) (coordinateSlice i φ.toFun y) :=
    coordinateSlice_contDiff i φ.contDiff y
  have htestCompact :
      HasCompactSupport (coordinateSlice i φ.toFun y) :=
    coordinateSlice_hasCompactSupport i φ.hasCompactSupport y
  have hidentity :=
    hweak.integral_eq (ContinuousLinearMap.id ℝ ℝ)
      (coordinateSlice i φ.toFun y) htestSmooth htestCompact
      (Set.subset_univ _)
  have hrepIntegral :
      (∫ t, r t * deriv (coordinateSlice i φ.toFun y) t) =
        ∫ t,
          coordinateSlice i f y t *
            deriv (coordinateSlice i φ.toFun y) t := by
    apply integral_congr_ae
    filter_upwards [hrep] with t ht
    rw [ht]
  calc
    (∫ t,
        coordinateSlice i f y t *
          coordinateDerivativeInSplit i φ.toFun (y, t)) =
        ∫ t,
          coordinateSlice i f y t *
            deriv (coordinateSlice i φ.toFun y) t := by
      apply integral_congr_ae
      filter_upwards with t
      exact congrArg (fun z ↦ coordinateSlice i f y t * z)
        (deriv_coordinateSlice i (f := φ.toFun)
          (φ.contDiff.of_le (by simp)) y t).symm
    _ = ∫ t, r t * deriv (coordinateSlice i φ.toFun y) t :=
      hrepIntegral.symm
    _ = -(∫ t, coordinateSlice i g y t *
        coordinateSlice i φ.toFun y t) := by
      have hneg := congrArg Neg.neg hidentity
      simpa using hneg.symm

private theorem ae_coordinateLine_integral_identity
    {n : ℕ} (i : Fin (n + 1))
    {f g : ℝ^(n + 1) → ℝ} {r : ℝ^n → ℝ → ℝ}
    (φ : TestFunction
      (⊤ : TopologicalSpace.Opens (ℝ^(n + 1)))
      ℝ (⊤ : ℕ∞))
    (hrep : ∀ᵐ y, r y =ᵐ[volume] coordinateSlice i f y)
    (hAC : ∀ᵐ y, ∀ a b : ℝ, AbsolutelyContinuousOnInterval (r y) a b)
    (hderiv :
      ∀ᵐ y, ∀ᵐ t, HasDerivAt (r y) (coordinateSlice i g y t) t) :
    ∀ᵐ y : ℝ^n,
      (∫ t,
          coordinateSlice i f y t *
            coordinateDerivativeInSplit i φ.toFun (y, t)) =
        -(∫ t,
          coordinateSlice i g y t * coordinateSlice i φ.toFun y t) := by
  filter_upwards [hrep, hAC, hderiv] with y hyrep hyAC hyderiv
  exact coordinateLine_integral_identity i φ y hyrep hyAC hyderiv

private noncomputable def weakTestLeft
    {n : ℕ} (i : Fin (n + 1)) (f : ℝ^(n + 1) → ℝ)
    (φ : AmbientTestFunction (n + 1)) : ℝ^(n + 1) → ℝ :=
  fun x ↦ f x * (∂[i] φ.toFun) x

private noncomputable def weakTestRight
    {n : ℕ} (g : ℝ^(n + 1) → ℝ)
    (φ : AmbientTestFunction (n + 1)) : ℝ^(n + 1) → ℝ :=
  fun x ↦ g x * φ.toFun x

private theorem weakTestLeft_integrable
    {n : ℕ} (i : Fin (n + 1)) {f : ℝ^(n + 1) → ℝ}
    (hf : LocallyIntegrableOn f univ volume) (φ : AmbientTestFunction (n + 1)) :
    Integrable (weakTestLeft i f φ) volume := by
  let φ1 :
      TestFunction
        (⊤ : TopologicalSpace.Opens (ℝ^(n + 1)))
        ℝ 1 :=
    TestFunction.monoCLM ℝ φ
  change Integrable
    (fun x ↦ f x * (∂[i] φ.toFun) x) volume
  simpa [φ1] using φ1.integrable_mul_partialDeriv
    hf i

private theorem weakTestRight_integrable
    {n : ℕ} {g : ℝ^(n + 1) → ℝ}
    (hg : LocallyIntegrableOn g univ volume) (φ : AmbientTestFunction (n + 1)) :
    Integrable (weakTestRight g φ) volume := by
  change Integrable (fun x ↦ g x * φ.toFun x) volume
  exact integrable_mul_continuous_compact
    (q := g) (ψ := φ.toFun) hg φ.contDiff.continuous φ.hasCompactSupport

private theorem ae_weakTestLine
    {n : ℕ} (i : Fin (n + 1))
    {f g : ℝ^(n + 1) → ℝ} (φ : AmbientTestFunction (n + 1))
    (hline :
      ∀ᵐ y : ℝ^n,
        (∫ t,
            coordinateSlice i f y t *
              coordinateDerivativeInSplit i φ.toFun (y, t)) =
          -(∫ t,
            coordinateSlice i g y t * coordinateSlice i φ.toFun y t)) :
    ∀ᵐ y : ℝ^n,
      (∫ t : ℝ, weakTestLeft i f φ (joinCoordinate i (y, t))) =
        -(∫ t : ℝ, weakTestRight g φ (joinCoordinate i (y, t))) := by
  filter_upwards [hline] with y hy
  simpa [weakTestLeft, weakTestRight, coordinateSlice,
    coordinateDerivativeInSplit] using hy

private theorem weakTest_integral_identity
    {n : ℕ} (i : Fin (n + 1))
    {f g : ℝ^(n + 1) → ℝ} (hf : LocallyIntegrableOn f univ volume)
    (hg : LocallyIntegrableOn g univ volume) (φ : AmbientTestFunction (n + 1))
    (hline :
      ∀ᵐ y : ℝ^n,
        (∫ t,
            coordinateSlice i f y t *
              coordinateDerivativeInSplit i φ.toFun (y, t)) =
          -(∫ t,
            coordinateSlice i g y t * coordinateSlice i φ.toFun y t)) :
    (∫ x, weakTestLeft i f φ x) =
      -(∫ x, weakTestRight g φ x) :=
  integral_eq_neg_of_ae_iterated i
    (weakTestLeft_integrable i hf φ)
    (weakTestRight_integrable hg φ)
    (ae_weakTestLine i φ hline)

/-- Local integrability and almost-everywhere absolute continuity on coordinate
lines reconstruct the global weak derivative; no integrability at infinity is needed. -/
theorem hasWeakDerivativeOn_of_locallyIntegrable_ae_coordinate_acl
    {n : ℕ} (i : Fin (n + 1))
    {f g : ℝ^(n + 1) → ℝ} (hf : LocallyIntegrableOn f Set.univ volume)
    (hg : LocallyIntegrableOn g Set.univ volume) {r : ℝ^n → ℝ → ℝ}
    (hrep :
      ∀ᵐ y, r y =ᵐ[volume] coordinateSlice i f y)
    (hAC :
      ∀ᵐ y, ∀ a b : ℝ, AbsolutelyContinuousOnInterval (r y) a b)
    (hderiv :
      ∀ᵐ y, ∀ᵐ t, HasDerivAt (r y) (coordinateSlice i g y t) t) :
    HasWeakDerivativeOn (n := n + 1) Set.univ [i] f g := by
  refine ⟨hf, hg, ?_⟩
  intro φ _hφ
  have hline :=
    ae_coordinateLine_integral_identity i φ hrep hAC hderiv
  rw [domainMeasure, Measure.restrict_univ]
  simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
    zero_add, pow_one, neg_one_mul, weakTestLeft, weakTestRight] using
    weakTest_integral_identity i hf hg φ hline


/-- Almost-everywhere absolute continuity on coordinate lines reconstructs
the selected global weak derivative. -/
theorem hasWeakDerivativeOn_of_ae_coordinate_acl
    {n : ℕ} (i : Fin (n + 1))
    {f g : ℝ^(n + 1) → ℝ} (hf : Integrable f volume)
    (hg : Integrable g volume) {r : ℝ^n → ℝ → ℝ}
    (hrep :
      ∀ᵐ y, r y =ᵐ[volume] coordinateSlice i f y)
    (hAC :
      ∀ᵐ y, ∀ a b : ℝ, AbsolutelyContinuousOnInterval (r y) a b)
    (hderiv :
      ∀ᵐ y, ∀ᵐ t, HasDerivAt (r y) (coordinateSlice i g y t) t) :
    HasWeakDerivativeOn (n := n + 1) Set.univ [i] f g := by
  exact hasWeakDerivativeOn_of_locallyIntegrable_ae_coordinate_acl i
    (hf.locallyIntegrable.locallyIntegrableOn Set.univ)
    (hg.locallyIntegrable.locallyIntegrableOn Set.univ) hrep hAC hderiv

end SobolevSpace.Slices
