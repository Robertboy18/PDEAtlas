/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Representative
public import PDE.Analysis.Integration.FiniteMeasureLp

/-!
# The fundamental theorem for Banach-valued Sobolev curves

For every real Banach space and every `1 ≤ p ≤ ∞`, a curve and its weak
derivative in `Lᵖ` determine a continuous representative on the closed time
interval. Its increments are the Bochner integrals of the weak derivative.
The uniform norm is bounded by the Sobolev norm, with a constant depending
only on the interval length. This is Evans §5.9.2, Theorem 2.

The norm in the theorem is the `p`th root of the integral of the sum of the
two `p`th powers for finite `p`, and the essential supremum of the sum of norms
for `p = ∞`, as in Evans's definition of `W^{1,p}(0, T; X)` (§5.9.2).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, the definition of `W^{1,p}(0, T; X)` and Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A Banach-valued `W¹ᵖ` curve has a continuous representative, satisfies the
fundamental theorem at every pair of closed-interval times, and obeys a uniform
norm estimate whose constant depends only on the interval length. -/
theorem exists_continuous_representative_memLp
    {a b : ℝ} (hab : a < b) {u g : ℝ → X} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) u g)
    (hu : MemLp u p (volume.restrict (Ioo a b)))
    (hg : MemLp g p (volume.restrict (Ioo a b))) :
    ∃ v : ℝ → X, Continuous v ∧
      u =ᵐ[volume.restrict (Ioo a b)] v ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, v t = v s + ∫ r in s..t, g r) ∧
      ∀ t ∈ Icc a b, ‖v t‖ ≤
        (2 * ((b - a)⁻¹ + 1) * max 1 (b - a)) *
          (if p = ∞ then essSup (fun r ↦ ‖u r‖ + ‖g r‖) (volume.restrict (Ioo a b))
           else (∫ r in Ioo a b, ‖u r‖ ^ p.toReal + ‖g r‖ ^ p.toReal) ^ p.toReal⁻¹) := by
  obtain ⟨v, hv, huv, hFTC⟩ :=
    hweak.exists_continuous_representative_Icc hab (hg.integrable hp)
  refine ⟨v, hv, huv, ?_, ?_⟩
  · intro s hs t ht
    exact (sub_eq_iff_eq_add.mp (hFTC s hs t ht)).trans (add_comm _ _)
  · intro t ht
    have hlen : 0 < b - a := sub_pos.mpr hab
    have hfactor : 0 ≤ (b - a)⁻¹ + 1 := by positivity
    have hC : 0 ≤ ((b - a)⁻¹ + 1) * max 1 (b - a) := by positivity
    have hmeasure : (volume.restrict (Ioo a b)).real univ = b - a := by
      rw [measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le hab.le]
    have huL1 := hu.integral_norm_le_max_measure_mul_lpNorm hp
    have hgL1 := hg.integral_norm_le_max_measure_mul_lpNorm hp
    rw [hmeasure] at huL1 hgL1
    have huNonneg : 0 ≤ ∫ r in Ioo a b, ‖u r‖ := integral_nonneg fun _ ↦ norm_nonneg _
    have hgNonneg : 0 ≤ ∫ r in Ioo a b, ‖g r‖ := integral_nonneg fun _ ↦ norm_nonneg _
    have hnorm :
        ‖v t‖ ≤ (((b - a)⁻¹ + 1) * max 1 (b - a)) *
          (lpNorm u p (volume.restrict (Ioo a b)) +
            lpNorm g p (volume.restrict (Ioo a b))) := by
      calc
        ‖v t‖ ≤ (b - a)⁻¹ * (∫ r in Ioo a b, ‖u r‖) +
            ∫ r in Ioo a b, ‖g r‖ :=
          norm_le_average_add_integral_of_intervalIntegral hab (hu.integrable hp)
            (hg.integrable hp) huv hFTC ht
        _ ≤ ((b - a)⁻¹ + 1) *
            ((∫ r in Ioo a b, ‖u r‖) + ∫ r in Ioo a b, ‖g r‖) := by
          nlinarith [mul_nonneg (inv_nonneg.mpr hlen.le) hgNonneg]
        _ ≤ ((b - a)⁻¹ + 1) *
            (max 1 (b - a) * lpNorm u p (volume.restrict (Ioo a b)) +
              max 1 (b - a) * lpNorm g p (volume.restrict (Ioo a b))) :=
          mul_le_mul_of_nonneg_left (add_le_add huL1 hgL1) hfactor
        _ = _ := by ring
    have hsum :
        lpNorm u p (volume.restrict (Ioo a b)) +
            lpNorm g p (volume.restrict (Ioo a b)) ≤
          2 * (if p = ∞ then
              essSup (fun r ↦ ‖u r‖ + ‖g r‖) (volume.restrict (Ioo a b))
            else (∫ r in Ioo a b, ‖u r‖ ^ p.toReal + ‖g r‖ ^ p.toReal) ^
              p.toReal⁻¹) := by
      by_cases htop : p = ∞
      · subst p
        rw [ite_eq_left rfl]
        have hsumLp :
            MemLp (fun r ↦ ‖u r‖ + ‖g r‖) ∞ (volume.restrict (Ioo a b)) :=
          hu.norm.add hg.norm
        have hule := lpNorm_mono_real hsumLp
          (fun r ↦ le_add_of_nonneg_right (norm_nonneg (g r)))
        have hgle := lpNorm_mono_real hsumLp
          (fun r ↦ le_add_of_nonneg_left (norm_nonneg (u r)))
        have heq :
            lpNorm (fun r ↦ ‖u r‖ + ‖g r‖) ∞ (volume.restrict (Ioo a b)) =
              essSup (fun r ↦ ‖u r‖ + ‖g r‖) (volume.restrict (Ioo a b)) := by
          rw [lpNorm_exponent_top_eq_essSup hsumLp]
          simp only [Real.norm_eq_abs,
            abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        rw [heq] at hule hgle
        linarith
      · rw [ite_eq_right htop]
        exact lpNorm_add_lpNorm_le_two_mul_integral_rpow_add hu hg
          (ne_of_gt (zero_lt_one.trans_le hp)) htop
    calc
      ‖v t‖ ≤ _ := hnorm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hC
      _ = _ := by ring

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
