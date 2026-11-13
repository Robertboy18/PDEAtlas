/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.LocalForward
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Vector

/-!
# Interior estimates for vector difference quotients

The coordinate estimates assemble in Euclidean-valued Lp. Translation preserves
null sets, so the estimates apply to every representative of the Sobolev function.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open MeasureTheory Set Rellich
open SobolevSpace.Extension.Lp
open scoped ENNReal Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Inside the original domain, a quotient of its zero extension represents the raw
quotient whenever both evaluation points stay in that domain. -/
theorem restrict_differenceQuotient_zeroExtend_ae {Ω V : Set (ℝ^n)}
    (hΩ : MeasurableSet Ω) (hVΩ : V ⊆ Ω)
    (f : DerivLp n p Ω) {u : ℝ^n → ℝ}
    (hu : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] u) (i : Fin n) (h : ℝ)
    (hshift : MapsTo (fun x ↦ x + coordinateStep i h) V Ω) :
    ((restrictDerivLp (subset_univ V) (differenceQuotientLp p i h
      (zeroExtendLp hΩ f)) : DerivLp n p V) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n V] forwardDifference i h u := by
  let f₀ := zeroExtendLp hΩ f
  have hf : ∀ᵐ x ∂volume, x ∈ Ω → f₀ x = u x :=
    (ae_restrict_iff' hΩ).mp ((zeroExtendLp_agree_ae hΩ f).trans hu)
  have hft := (measurePreserving_add_right (volume : Measure (ℝ^n))
    (coordinateStep i h)).quasiMeasurePreserving.ae hf
  filter_upwards [restrictDerivLp_apply_ae (subset_univ V) (differenceQuotientLp p i h f₀),
    (differenceQuotientLp_apply_ae p i h f₀).filter_mono (ae_mono Measure.restrict_le_self),
    hf.filter_mono (ae_mono Measure.restrict_le_self),
    hft.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_of_ae_restrict_of_subset hVΩ (ae_restrict_mem hΩ),
    ae_restrict_of_ae_restrict_of_subset (fun _ hy ↦ hshift hy)
      (ae_restrict_mem (hΩ.preimage (measurable_add_const (coordinateStep i h))))]
    with x hr hd hx htx hxΩ hxsΩ
  rw [hr, hd]
  simp only [forwardDifference, hx hxΩ, htx hxsΩ]

/-- Bounds for the restricted coordinate quotients assemble into a bound
for the vector quotient of any representative. No weak
derivatives of the original `Lp` field are assumed. -/
theorem eLpNorm_vectorDifference_le_of_restricted_bounds
    {Ω V : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    (hVΩ : V ⊆ Ω) (f : DerivLp n p Ω) {u : ℝ^n → ℝ}
    (hu : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] u) (h : ℝ)
    (hshift : ∀ i, MapsTo (fun x ↦ x + coordinateStep i h) V Ω)
    {C : ℝ} (hbound : ∀ i,
      ‖restrictDerivLp (subset_univ V)
        (differenceQuotientLp p i h (zeroExtendLp hΩ f))‖ ≤ C) :
    eLpNorm (vectorDifference h u) p (domainMeasure n V) ≤
      ENNReal.ofReal ((n : ℝ) * C) := by
  let d (i : Fin n) : DerivLp n p V :=
    restrictDerivLp (subset_univ V)
      (differenceQuotientLp p i h (zeroExtendLp hΩ f))
  have hd (i : Fin n) :
      (d i : ℝ^n → ℝ) =ᵐ[domainMeasure n V] forwardDifference i h u :=
    restrict_differenceQuotient_zeroExtend_ae hΩ hVΩ f hu i h (hshift i)
  let D : Lp (ℝ^n) p (domainMeasure n V) := Lp.euclideanTuple d
  have hD : (D : ℝ^n → ℝ^n) =ᵐ[domainMeasure n V] vectorDifference h u := by
    filter_upwards [Lp.euclideanTuple_apply_ae d, ae_all_iff.mpr hd] with x hx hy
    exact PiLp.ext fun i ↦ (hx i).trans (hy i)
  have hnorm : ‖D‖ ≤ (n : ℝ) * C := by
    apply (Lp.norm_euclideanTuple_le d).trans
    calc
      ∑ i : Fin n, ‖d i‖ ≤ ∑ _ : Fin n, C := Finset.sum_le_sum fun i _ ↦ hbound i
      _ = _ := by simp
  rw [← eLpNorm_congr_ae hD, ← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hnorm

/-- For a compactly contained set and any collar inside the domain, vector quotients
of a Sobolev representative have Lp norm at most `n` times the gradient norm. -/
theorem eLpNorm_vectorDifference_le_of_thickening
    (hp : p ≠ ∞) {Ω V : Set (ℝ^n)} (hΩ : IsOpen Ω) (hV : MeasurableSet V)
    (hVc : IsCompact (closure V)) {ρ : ℝ} (hρ : 0 < ρ)
    (hcollar : Metric.thickening ρ V ⊆ Ω)
    (U : W^{1,p}(Ω)) {u : ℝ^n → ℝ}
    (hu : baseRepresentative U =ᵐ[domainMeasure n Ω] u)
    {h : ℝ} (hh : h ≠ 0) (hhρ : |h| < ρ) :
    eLpNorm (vectorDifference h u) p (domainMeasure n V) ≤
      ENNReal.ofReal ((n : ℝ) * ‖∇ U‖) := by
  apply eLpNorm_vectorDifference_le_of_restricted_bounds hΩ.measurableSet
    ((Metric.self_subset_thickening hρ V).trans hcollar) (wkpBaseCoordinateCLM U) hu h
  · intro i x hx
    exact hcollar (Metric.mem_thickening_iff.mpr
      ⟨x, hx, by simpa only [dist_eq_norm, add_sub_cancel_left, norm_coordinateStep] using hhρ⟩)
  · intro i
    exact (norm_restricted_differenceQuotient_le hp hΩ hV hVc hρ hcollar U i hh hhρ
      ).trans (norm_derivCoordinate_le_wkpGradientCLM U i)

end SobolevSpace.GraphSpace.DifferenceQuotient
