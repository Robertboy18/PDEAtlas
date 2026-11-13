/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.LocalBoundedness

/-!
# An interior L²-to-L∞ estimate for weak solutions

Scaling the first De Giorgi lemma gives a quantitative local bound in terms of the original
solution's L² norm. Applying the same weak equation to both signs gives a bound for its absolute
value. The state initially belongs only to H¹, and the coefficient entries are merely essentially
bounded.

This is the local boundedness estimate `‖u‖_{L∞(B_r)} ≤ C ‖u‖_{L²(B_R)}` from which the De Giorgi
oscillation argument starts (`exists_local_norm_le_sqrt_integral_sq`). Evans states the
De Giorgi-Nash theorem in §8.3.2 without proof and refers to Gilbarg-Trudinger, Chapter 8.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.3.2, the De Giorgi-Nash theorem for the linear equation
  (17), stated without proof, p. 487.
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 8 (Generalized Solutions and Regularity).
  <https://doi.org/10.1007/978-3-642-61798-0_8>
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped NNReal Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- A homogeneous measurable uniformly elliptic equation controls the local
essential supremum by the original L² norm on a larger ball. The constant
is uniform in the centre, solution, and coefficients within the given bounds.
The H¹ state is proved locally essentially bounded, without any assumption
on its continuity. -/
theorem exists_local_norm_le_sqrt_integral_sq
    {W : Set ℝ^n} (hW : IsOpen W) (hWb : Bornology.IsBounded W)
    {q : ℝ≥0∞}
    (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Fin n → Fin n → DerivLp n ∞ W),
        (∀ i j, ‖a i j‖ ≤ Λ) → AEUniformlyElliptic a α →
      ∀ (u : H¹(W)), IsInteriorWeakDivergenceSolution a 0 u →
      ∀ (z : ℝ^n), ball z R ⊆ W →
        ∀ᵐ x ∂volume.restrict (ball z r),
          ‖wkpBaseCoordinateCLM u x‖ ≤
            C * Real.sqrt (∫ y in ball z R, wkpBaseCoordinateCLM u y ^ 2) := by
  obtain ⟨ε, hε, hthreshold⟩ :=
    exists_small_tail_threshold_on_balls hWb hq2 hq hα hΛ hr hrR
  refine ⟨(Real.sqrt ε)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hε), ?_⟩
  intro a haΛ ha u hu z hz
  let μ := volume.restrict (ball z R)
  let ν := volume.restrict (ball z r)
  have hμ : μ ≤ domainMeasure n W := domainMeasure_le hz
  have hν : ν ≤ μ := Measure.restrict_mono (ball_subset_ball hrR.le) le_rfl
  have hmem : MemLp (wkpBaseCoordinateCLM u) 2 μ := (Lp.memLp _).mono_measure hμ
  let I := ∫ x, wkpBaseCoordinateCLM u x ^ 2 ∂μ
  have hI : 0 ≤ I := integral_nonneg (fun _ ↦ sq_nonneg _)
  by_cases hIzero : I = 0
  · filter_upwards [((integral_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _)
      hmem.integrable_sq).mp hIzero).filter_mono (ae_mono hν)] with x hx
    rw [sq_eq_zero_iff.mp hx, norm_zero]
    positivity
  have hIpos : 0 < I := lt_of_le_of_ne hI (Ne.symm hIzero)
  let H := Real.sqrt I / Real.sqrt ε
  have hH : 0 < H := div_pos (Real.sqrt_pos.mpr hIpos) (Real.sqrt_pos.mpr hε)
  have hHsq : H ^ 2 = I / ε := by
    dsimp only [H]
    rw [div_pow, Real.sq_sqrt hI, Real.sq_sqrt hε.le]
  have hupper (σ : ℝ) (hσ : σ ^ 2 = 1) :
      ∀ᵐ x ∂ν, (σ / H) * wkpBaseCoordinateCLM u x ≤ 1 := by
    let v : H¹(W) := (σ / H) • u
    have hv : IsInteriorWeakDivergenceSolution a 0 v := by
      refine ⟨hW, fun φ ↦ ?_⟩
      change interiorVariableCoeffForm (multiplicationCoefficientOperator a)
        ((σ / H) • u) φ = loadFunctional 0 φ
      rw [map_smul, smul_apply, hu.equation φ]
      simp only [loadFunctional_apply, inner_zero_left, smul_zero]
    have hrep : (wkpBaseCoordinateCLM v : ℝ^n → ℝ) =ᵐ[domainMeasure n W]
        fun x ↦ (σ / H) * wkpBaseCoordinateCLM u x := by
      rw [show wkpBaseCoordinateCLM v = (σ / H) • wkpBaseCoordinateCLM u from map_smul _ _ _]
      exact Lp.coeFn_smul _ _
    have hvmem : MemLp (wkpBaseCoordinateCLM v) 2 μ := (Lp.memLp _).mono_measure hμ
    have htail :
        (∫ x in ball z R, max (wkpBaseCoordinateCLM v x - 0) 0 ^ 2) ≤ ε := by
      calc
        _ ≤ ∫ x, wkpBaseCoordinateCLM v x ^ 2 ∂μ := by
          simp only [sub_zero]
          exact integral_mono hvmem.pos_part.integrable_sq hvmem.integrable_sq fun x ↦
            (pow_le_pow_left₀ (le_max_right _ _) (max_le (le_abs_self _) (abs_nonneg _)) 2).trans_eq
              (sq_abs _)
        _ = (σ / H) ^ 2 * I := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [hrep.filter_mono (ae_mono hμ)] with x hx
          rw [hx, mul_pow]
        _ = ε := by rw [div_pow, hσ, hHsq]; field_simp
    have hvbound := hthreshold a haΛ ha v hv z hz 0 htail
    filter_upwards [hvbound, hrep.filter_mono (ae_mono (hν.trans hμ))] with x hx heq
    simpa only [heq, zero_add] using hx
  filter_upwards [hupper 1 (by norm_num), hupper (-1) (by norm_num)] with x hp hm
  rw [div_mul_eq_mul_div, div_le_one hH] at hp hm
  change ‖wkpBaseCoordinateCLM u x‖ ≤ (Real.sqrt ε)⁻¹ * Real.sqrt I
  have habs : ‖wkpBaseCoordinateCLM u x‖ ≤ H := abs_le.mpr ⟨by linarith, by linarith⟩
  simpa only [H, div_eq_mul_inv, mul_comm (Real.sqrt I)] using habs

end SobolevSpace.GraphSpace
