/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.Duality.Transport

/-!
# Exact scalar `Lp` dual representation on sigma-finite measures

Every continuous real functional on `Lp`, for `1 ≤ p < ∞`, is the integral
pairing against a conjugate `Lq` density with exactly the same norm.
In particular, `L¹` dual densities belong to `L∞`.

A sigma-finite measure is equivalent to a finite measure. Density-root
isometries transfer the finite-measure representation, and the pairing
transport identities identify the integral against the new density.
-/

@[expose] public noncomputable section

open Filter
open scoped ENNReal NNReal

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

/-- A scalar `Lp` functional on a sigma-finite measure, for `1 ≤ p < ∞`, has a
conjugate density whose norm is exactly the operator norm. This includes the
`L¹`–`L∞` endpoint. -/
theorem exists_dualDensity_norm_eq (hp : p ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ p μ)) :
    ∃ g : Lp ℝ q μ, ‖g‖ = ‖Λ‖ ∧
      Λ = (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p g := by
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r = p :=
    ⟨p.toReal, ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp,
      ENNReal.ofReal_toReal hp⟩
  obtain ⟨ν, hν, hμν, hνμ⟩ := exists_isFiniteMeasure_absolutelyContinuous μ
  let := hν
  let w := ν.rnDeriv μ
  have hw : Measurable w := Measure.measurable_rnDeriv ν μ
  have hwpos : ∀ᵐ x ∂μ, 0 < w x := Measure.rnDeriv_pos' hμν
  have hwtop : ∀ᵐ x ∂μ, w x < ∞ := Measure.rnDeriv_lt_top ν μ
  have hwν : μ.withDensity w = ν := Measure.withDensity_rnDeriv_eq ν μ hνμ
  let e := withDensityRootLIEOfEq (E := ℝ) hw hwpos hwtop hwν hr
  let L := Λ.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨g, hgnorm, hgrepr⟩ :=
    exists_dualDensity_norm_eq_of_finite (q := q) hp L
  have hLnorm : ‖L‖ = ‖Λ‖ :=
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv Λ e
  by_cases hq : q = ∞
  · subst q
    obtain ⟨G, hGnorm, hG⟩ := exists_top_density_of_absolutelyContinuous hμν g
    have hrepr : Λ =
        (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ (ENNReal.ofReal r) G := by
      ext f
      obtain ⟨v, rfl⟩ := e.surjective f
      have h := congrArg (fun T : StrongDual ℝ (Lp ℝ (ENNReal.ofReal r) ν) ↦ T v)
        hgrepr
      change Λ (e v) = _ at h
      exact h.trans (lpPairing_withDensity_top hr hw hwpos hwtop hwν g G hG v).symm
    refine ⟨G, le_antisymm (hGnorm.trans_eq (hgnorm.trans hLnorm)) ?_, hrepr⟩
    rw [hrepr]
    exact norm_lpPairing_le G
  · obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ ENNReal.ofReal s = q :=
      ⟨q.toReal, ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq,
        ENNReal.ofReal_toReal hq⟩
    let d := withDensityRootLIEOfEq (E := ℝ) hw hwpos hwtop hwν hs
    refine ⟨d g, (d.norm_map g).trans (hgnorm.trans hLnorm), ?_⟩
    ext f
    obtain ⟨v, rfl⟩ := e.surjective f
    have h := congrArg (fun T : StrongDual ℝ (Lp ℝ (ENNReal.ofReal r) ν) ↦ T v)
      hgrepr
    change Λ (e v) = _ at h
    exact h.trans (lpPairing_withDensity_of_ne_top hr hs hw hwpos hwtop hwν g v).symm

/-- The exact-norm scalar dual density represents every value by the ordinary integral
of the product of representatives. -/
theorem exists_integral_dualDensity_norm_eq (hp : p ≠ ∞)
    (Λ : StrongDual ℝ (Lp ℝ p μ)) :
    ∃ g : Lp ℝ q μ, ‖g‖ = ‖Λ‖ ∧
      ∀ f : Lp ℝ p μ, Λ f = ∫ x, f x * g x ∂μ := by
  obtain ⟨g, hnorm, hrepr⟩ := exists_dualDensity_norm_eq (q := q) hp Λ
  refine ⟨g, hnorm, fun f ↦ ?_⟩
  rw [hrepr, ContinuousLinearMap.lpPairing_eq_integral]
  simp only [ContinuousLinearMap.mul_apply', mul_comm]

/-- Over a sigma-finite measure the scalar integral pairing is onto the dual
of `Lp` for every finite normed exponent, including `p = 1`. -/
theorem surjective_lpPairing_of_sigmaFinite (hp : p ≠ ∞) :
    Function.Surjective ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p) := by
  intro Λ
  obtain ⟨g, _, hrepr⟩ := exists_dualDensity_norm_eq (q := q) hp Λ
  exact ⟨g, hrepr.symm⟩

end MeasureTheory.Lp
