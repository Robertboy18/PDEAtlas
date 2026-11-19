/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.StationaryPhase.ChartAmplitude
public import PDE.Analysis.Fourier.StationaryPhase.Signature

/-!
# Stationary phase near one nondegenerate critical point

The smooth Morse chart and the transformed density reduce the phase to
its Hessian quadratic form. The resulting leading term includes the phase at
the critical point, the determinant magnitude, and the intrinsic signature.

`exists_local_stationary_phase` is the computation near a critical point `y_k` in Evans's
stationary phase method, §4.5.3(b): his Lemma 3(ii), here `exists_smooth_morse_chart`,
followed by his Lemma 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(b), Lemma 2, p. 221, Lemma 3(ii), p. 223, and
  the stationary phase method, p. 226. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory Complex
open scoped Topology

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- The oscillatory integral in the scale parameter `ε`, with frequency `ε⁻²`. -/
def oscillatoryIntegral (φ : ℝ^n → ℝ) (a : ℝ^n → ℂ) (ε : ℝ) : ℂ :=
  ∫ x, Complex.exp ((φ x / ε ^ 2 : ℝ) * I) * a x

/-- The exact change of variables in a quadratic phase chart. -/
theorem oscillatoryIntegral_eq_quadratic
    {φ : ℝ^n → ℝ} {p : ℝ^n}
    (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    (hq : ∀ x ∈ e.source, φ x = φ p +
      fderiv ℝ (fderiv ℝ φ) p (e x) (e x) / 2)
    {a : ℝ^n → ℂ} (hs : tsupport a ⊆ e.source) (ε : ℝ) :
    oscillatoryIntegral φ a ε = Complex.exp ((φ p / ε ^ 2 : ℝ) * I) *
      ∫ y, Complex.exp
        ((fderiv ℝ (fderiv ℝ φ) p y y / 2 / ε ^ 2 : ℝ) * I) * chartAmplitude e a y := by
  classical
  rw [oscillatoryIntegral, integral_mul_eq_integral_chartAmplitude e
    (hi.differentiableOn (by simp)) hs, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ e.target
  · have h := hq (e.symm y) (e.map_target hy)
    rw [e.right_inv hy] at h
    rw [h, add_div, Complex.ofReal_add, add_mul, Complex.exp_add]
    ring
  · simp [chartAmplitude, hy]

/-- Every smooth phase with a nondegenerate critical point has a neighborhood
on which every smooth compact amplitude has the full stationary-phase remainder
limit. The neighborhood and all coordinate maps are constructed. -/
theorem exists_local_stationary_phase
    {φ : ℝ^n → ℝ} {p : ℝ^n}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hp : fderiv ℝ φ p = 0)
    (hdet : (PDE.Analysis.hessianMatrix φ p).det ≠ 0) :
    ∃ U : Set (ℝ^n), IsOpen U ∧ p ∈ U ∧
      ∀ (a : ℝ^n → ℂ), ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a →
        tsupport a ⊆ U →
        Tendsto (fun ε : ℝ ↦ ((ε : ℂ) ^ n)⁻¹ *
          (oscillatoryIntegral φ a ε - (ε : ℂ) ^ n *
            (Complex.exp ((φ p / ε ^ 2 : ℝ) * I) * hessianFresnel φ p * a p)))
          (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨e, hps, hep, hd, he, hi, hq⟩ := exists_smooth_morse_chart hφ hp hdet
  refine ⟨e.source, e.open_source, hps, ?_⟩
  intro a ha hc hs
  have hvalue : chartAmplitude e a 0 = a p := by
    rw [← hep]
    exact chartAmplitude_apply e hps hd
      ((hi.contDiffAt (e.open_target.mem_nhds (e.map_source hps))).differentiableAt
        (by simp)) a
  have h := (tendsto_integral_hessian_quadratic
    (hφ.contDiffAt.of_le (by simp)) hdet
    (contDiff_chartAmplitude e he hi ha hc hs)
    (hasCompactSupport_chartAmplitude e hc hs)).sub_const
      (hessianFresnel φ p * a p)
  rw [hvalue, sub_self] at h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hn := h.norm
  rw [norm_zero] at hn
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [oscillatoryIntegral_eq_quadratic e hi hq hs]
  have hcancel : ((ε : ℂ) ^ n)⁻¹ * (ε : ℂ) ^ n = 1 :=
    inv_mul_cancel₀ (pow_ne_zero n (Complex.ofReal_ne_zero.mpr hε.ne'))
  have halg (J C z : ℂ) :
      ((ε : ℂ) ^ n)⁻¹ * (z * J - (ε : ℂ) ^ n * (z * C)) =
        z * (((ε : ℂ) ^ n)⁻¹ * J - C) := by
    calc
      _ = z * (((ε : ℂ) ^ n)⁻¹ * J -
          (((ε : ℂ) ^ n)⁻¹ * (ε : ℂ) ^ n) * C) := by ring
      _ = _ := by rw [hcancel, one_mul]
  rw [mul_assoc (Complex.exp _) (hessianFresnel φ p), halg,
    norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

end PDE.Analysis.StationaryPhase
