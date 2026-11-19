/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.C1Domain.CompactEmbedding
import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction

/-!
# Compact base coordinates at every finite Sobolev exponent

On an operational C¹ extension domain of dimension at least two, the base
coordinate `W¹ᵖ → Lᵖ` is compact for every finite `p ≥ 1`. The critical and
supercritical source exponents reduce to the subcritical theorem:
choose `1 ≤ s ≤ p` with `s < n` and `p < s*`, lower the Sobolev exponent to
`s`, and use the compact inclusion from `W¹ˢ` into `Lᵖ`.

The composition agrees almost everywhere with the base coordinate. The
restriction `n ≥ 2` comes from the exponent reduction, not from any failure of
compactness in dimension one.

For finite `p` this is the compact embedding `W^{1,p}(U) ⊂⊂ L^p(U)` of the Remark after Evans §5.7,
Theorem 1, which Evans derives from Theorem 1 because `p* > p` and `p* → ∞` as `p → n`; the choice
of `s` above is that argument. For `n < p` Evans also points to Morrey's inequality and the
Arzelà–Ascoli theorem. The subcritical theorem is `inclusion_isCompactOperator_of_c1Domain`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.7, Theorem 1 and the Remark after its proof, pp. 286-289.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.GraphSpace.RellichKondrachov

/-- In dimension at least two, every finite target exponent admits a
subcritical source exponent no larger than itself. Below the dimension the
source can be unchanged; otherwise invert the Sobolev exponent at `p + 1`. -/
private theorem exists_subcritical_source
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ≥0} (hp : 1 ≤ p) :
    ∃ s : ℝ≥0, 1 ≤ s ∧ s ≤ p ∧ (s : ℝ) < n ∧ p < Inequalities.pStar n s := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast zero_lt_one.trans_le hp
  by_cases hpn : (p : ℝ) < n
  · refine ⟨p, hp, le_rfl, hpn, ?_⟩
    apply NNReal.coe_lt_coe.mp
    rw [Inequalities.pStar_coe hn0 hpn]
    apply (lt_div_iff₀ (sub_pos.mpr hpn)).2
    nlinarith [sq_pos_of_pos hp0]
  · have hnq : (n : ℝ) < ((p + 1 : ℝ≥0) : ℝ) := by
      push_cast
      linarith [le_of_not_gt hpn]
    have hq0 : 0 < ((p + 1 : ℝ≥0) : ℝ) := by positivity
    let s := Inequalities.pStarPreimage n (p + 1)
    have hs : (s : ℝ) < n := Inequalities.pStarPreimage_lt_dimension hn0 hq0
    refine ⟨s, Inequalities.one_le_pStarPreimage hn hnq, ?_, hs, ?_⟩
    · exact NNReal.coe_le_coe.mp (hs.le.trans (le_of_not_gt hpn))
    · rw [show Inequalities.pStar n s = p + 1 from
        Inequalities.pStar_pStarPreimage hn0 hq0]
      exact lt_add_of_pos_right _ zero_lt_one

/-- If `Ω` carries a `C1ExtensionAtlas` and `n ≥ 2`, then for every finite `p ≥ 1` the base
coordinate `W^{1,p}(Ω) → L^p(Ω)` is a compact operator, including `p ≥ n`. -/
theorem baseCoordinate_isCompactOperator_of_c1Domain
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    [Boundary.C1ExtensionAtlas n Ω] (hn : 2 ≤ n)
    {p : ℝ≥0} [hp : Fact (1 ≤ p)] :
    IsCompactOperator
      (wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) := by
  obtain ⟨s, hs1, hsp, hsn, hps⟩ := exists_subcritical_source hn hp.out
  have : Fact (1 ≤ s) := ⟨hs1⟩
  have : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨by exact_mod_cast hs1⟩
  have hspE : (s : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hsp
  let lower : W^{1,p}(Ω) →L[ℝ] W^{1,s}(Ω) :=
    lowerExponentOfFiniteMeasureCLM hspE
  let incl : W^{1,s}(Ω) →L[ℝ] DerivLp n p Ω :=
    inclusion hsn hps.le
  have hcompact : IsCompactOperator incl :=
    inclusion_isCompactOperator_of_c1Domain hsn hps
  have heq : wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞))
      (Ω := Ω) = incl.comp lower := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    have hinc := inclusion_apply_ae (n := n) (Ω := Ω) hsn hps.le (lower u)
    have hlow := lowerExponentOfFiniteMeasure_apply_ae hspE u (baseIndex n 1)
    have hlow' : baseRepresentative (lower u) =ᵐ[domainMeasure n Ω]
        baseRepresentative u := by
      simpa only [baseRepresentative, lower, lowerExponentOfFiniteMeasureCLM_apply] using hlow
    exact (hinc.trans hlow').symm
  rw [heq]
  exact hcompact.comp_clm lower

end SobolevSpace.GraphSpace.RellichKondrachov
