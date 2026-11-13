/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.L1.Compactness
public import PDE.Analysis.MeasureTheory.Lp.SignedPower

/-!
# Compactness from translation bounds at every finite exponent

A bounded family in `Lp`, with a common bounded support and a uniform linear
translation modulus, is totally bounded for every finite `p ≥ 1`.

For `p > 1`, the odd power `sign(u) |u|^p` has bounded `L¹` norm. Hölder's
inequality transfers the translation estimate to this family, so the
finite-grid criterion gives compactness in `L¹`. The reciprocal odd power is
continuous from `L¹` to `Lp` and recovers the original family. No boundary
regularity or restriction on the dimension is needed.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.RellichKondrachov

open MeasureTheory Set
open scoped ENNReal Topology

variable {n : ℕ}

/-- A pointwise superposition commutes with translation of equivalence classes.
Measure preservation transports the almost-everywhere representative formula. -/
private theorem translateLp_superposition
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (g : ℝ → ℝ)
    (hmem : ∀ u : DerivLp n p Set.univ,
      MemLp (fun x ↦ g (u x)) q (domainMeasure n Set.univ))
    (h : ℝ^n) (u : DerivLp n p Set.univ) :
    Rellich.translateLp q h (Lp.superposition (fun _ ↦ g) hmem u) =
      Lp.superposition (fun _ ↦ g) hmem (Rellich.translateLp p h u) := by
  apply Lp.ext
  have hcomp :
      (fun x ↦ Lp.superposition (fun _ ↦ g) hmem u (x + h)) =ᵐ[
        domainMeasure n Set.univ] fun x ↦ g (u (x + h)) := by
    simpa only [Function.comp_def, Rellich.translationContinuousMap_apply] using
      (Rellich.translationMeasurePreserving h).quasiMeasurePreserving.ae_eq_comp
        (Lp.coeFn_superposition (fun _ ↦ g) hmem u)
  filter_upwards [
    Rellich.translateLp_apply_ae q h (Lp.superposition (fun _ ↦ g) hmem u),
    Lp.coeFn_superposition (fun _ ↦ g) hmem (Rellich.translateLp p h u),
    Rellich.translateLp_apply_ae p h u, hcomp] with x hleft hright hu hg
  rw [hleft, hright, hu, hg]

/-- At every finite Lebesgue exponent, bounded support and a common linear
translation bound turn a norm-bounded family into a totally bounded family.
The compactness conclusion is derived from the finite-grid `L¹` criterion. -/
theorem totallyBounded_Lp_of_bounded_support_translation
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (S : Set (DerivLp n p Set.univ)) (hS : Bornology.IsBounded S)
    (R C : ℝ) (hC : 0 ≤ C)
    (hsupport : ∀ f ∈ S, ∀ᵐ x ∂volume,
      x ∉ Metric.ball (0 : ℝ^n) R → f x = 0)
    (htrans : ∀ f ∈ S, ∀ h : ℝ^n,
      ‖Rellich.translateLp p h f - f‖ ≤ ‖h‖ * C) :
    TotallyBounded S := by
  by_cases hp1 : p = 1
  · subst p
    exact totallyBounded_L1_of_bounded_support_translation S hS R C hC hsupport htrans
  have hpgt : 1 < p := lt_of_le_of_ne (Fact.out : 1 ≤ p) (Ne.symm hp1)
  let r : ℝ := p.toReal
  have hr : 1 < r := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hpgt
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hp0 : p ≠ 0 := (zero_lt_one.trans hpgt).ne'
  have hdiv : p / ENNReal.ofReal r = 1 := by
    rw [show ENNReal.ofReal r = p from ENNReal.ofReal_toReal hp]
    exact ENNReal.div_self hp0 hp
  have hinv : 1 / ENNReal.ofReal r⁻¹ = p := by
    rw [ENNReal.ofReal_inv_of_pos hr0,
      show ENNReal.ofReal r = p from ENNReal.ofReal_toReal hp, one_div, inv_inv]
  let N : DerivLp n p Set.univ → DerivLp n 1 Set.univ :=
    Lp.superposition (fun _ ↦ Real.signedPower r) (Lp.memLp_signedPower hr0 hdiv)
  let I : DerivLp n 1 Set.univ → DerivLp n p Set.univ :=
    Lp.superposition (fun _ ↦ Real.signedPower r⁻¹)
      (Lp.memLp_signedPower (inv_pos.mpr hr0) hinv)
  have hI : Continuous I :=
    Lp.continuous_superposition_signedPower ENNReal.one_ne_top (inv_pos.mpr hr0) hinv
  have hleft (u : DerivLp n p Set.univ) : I (N u) = u := by
    refine Lp.ext ?_
    filter_upwards [
      Lp.coeFn_superposition (fun _ ↦ Real.signedPower r⁻¹)
        (Lp.memLp_signedPower (inv_pos.mpr hr0) hinv) (N u),
      Lp.coeFn_superposition (fun _ ↦ Real.signedPower r)
        (Lp.memLp_signedPower hr0 hdiv) u] with x hIu hNu
    rw [hIu, hNu, Real.signedPower_inv_signedPower hr0]
  obtain ⟨M, hM, hSM⟩ := hS.subset_closedBall_lt 0 0
  have hnorm (u : DerivLp n p Set.univ) (hu : u ∈ S) : ‖u‖ ≤ M :=
    mem_closedBall_zero_iff.mp (hSM hu)
  let T := N '' S
  have hTbounded : Bornology.IsBounded T :=
    (Metric.isBounded_closedBall (x := (0 : DerivLp n 1 Set.univ)) (r := M ^ r)).subset <| by
      rintro f ⟨u, hu, rfl⟩
      exact mem_closedBall_zero_iff.2 ((Lp.norm_superposition_signedPower hr0 hdiv u).trans_le
        (Real.rpow_le_rpow (norm_nonneg _) (hnorm u hu) hr0.le))
  let D : ℝ := (2 * r) * (2 * M) ^ (r - 1) * C
  have hD : 0 ≤ D := mul_nonneg
    (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)) hC
  have hT : TotallyBounded T := by
    apply totallyBounded_L1_of_bounded_support_translation T hTbounded R D hD
    · rintro f ⟨u, hu, rfl⟩
      have hNu : N u =ᵐ[volume] fun x ↦ Real.signedPower r (u x) := by
        simpa only [domainMeasure, Measure.restrict_univ] using
          Lp.coeFn_superposition (fun _ ↦ Real.signedPower r)
            (Lp.memLp_signedPower hr0 hdiv) u
      filter_upwards [hsupport u hu, hNu] with x hx hNx hxBall
      rw [hNx, hx hxBall, Real.signedPower_zero]
    · rintro f ⟨u, hu, rfl⟩ h
      have hsum : ‖Rellich.translateLp p h u‖ + ‖u‖ ≤ 2 * M := by
        rw [Rellich.norm_translateLp]
        linarith [hnorm u hu]
      calc
        ‖Rellich.translateLp 1 h (N u) - N u‖ = ‖N (Rellich.translateLp p h u) - N u‖ :=
          congrArg (fun v ↦ ‖v - N u‖)
            (translateLp_superposition (Real.signedPower r) (Lp.memLp_signedPower hr0 hdiv) h u)
        _ ≤ (2 * r) * (‖Rellich.translateLp p h u‖ + ‖u‖) ^ (r - 1) *
            ‖Rellich.translateLp p h u - u‖ :=
          Lp.norm_superposition_sub_le_of_twoPointGrowth hp hr hdiv (by positivity)
            (Lp.memLp_signedPower hr0 hdiv) (Real.norm_signedPower_sub_le hr.le) _ _
        _ ≤ ((2 * r) * (2 * M) ^ (r - 1)) * (‖h‖ * C) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (by positivity) hsum (sub_nonneg.mpr hr.le))
              (by positivity))
            (htrans u hu h) (norm_nonneg _) (by positivity)
        _ = ‖h‖ * D := by dsimp [D]; ring
  refine ((hT.closure.isCompact_of_isClosed isClosed_closure).image hI).totallyBounded.subset
    fun u hu ↦ ?_
  exact ⟨N u, subset_closure (mem_image_of_mem N hu), hleft u⟩

end SobolevSpace.GraphSpace.RellichKondrachov
