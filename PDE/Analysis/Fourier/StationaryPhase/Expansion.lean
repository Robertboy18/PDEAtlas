/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.StationaryPhase.Partition
public import PDE.Analysis.Fourier.StationaryPhase.Noncritical

/-!
# The stationary-phase expansion on a compact amplitude support

For a smooth phase whose critical points on the support of a smooth compactly supported
amplitude are nondegenerate, `exists_stationary_phase_expansion_scale` gives the leading
term of `∫ exp (i φ x / ε²) a x dx` as `ε → 0`: the sum over the critical points of
`ε^n exp (i φ p / ε²) hessianFresnel φ p a p`, with an error `o(ε^n)`. This is formula (54)
of Evans, §4.5.3(b), with his `ε` replaced by `ε²` and his relative error `O(ε)` by `o(1)`.

## Main results

* `exists_stationary_phase_expansion_scale`: the leading stationary-phase expansion, with the
  finite critical set constructed.

## How it works

We follow Evans's stationary phase method. He assumes that the critical set in the support
of `a` is finite, (52); `finite_criticalPoints` derives this from nondegeneracy and
compactness. `exists_stationary_partition` splits `a` as `r + ∑ p, b p`, with `b p` supported
near the critical point `p` and `r` supported away from all critical points, in place of his
partition of unity. The part with `r` is `o(ε^n)` by `tendsto_noncritical_remainder`, which
integrates by parts along the normalized gradient instead of using his Lemma 3(i) and
Lemma 1. Near each critical point, `exists_local_stationary_phase` uses a Morse chart, his
Lemma 3(ii), and the quadratic asymptotics of his Lemma 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(b), Lemmas 1-3, pp. 221-226, and the stationary
  phase method, (52)-(54), p. 226. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Complex
open scoped Topology

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- A compact continuous amplitude makes every smooth-phase oscillatory integral integrable. -/
theorem integrable_oscillatory {φ : ℝ^n → ℝ} (hφ : Continuous φ)
    {a : ℝ^n → ℂ} (ha : Continuous a) (hc : HasCompactSupport a) (ε : ℝ) :
    Integrable (fun x ↦ Complex.exp ((φ x / ε ^ 2 : ℝ) * I) * a x) := by
  have hphase : Continuous (fun x ↦ Complex.exp ((φ x / ε ^ 2 : ℝ) * I)) := by
    fun_prop
  exact (hphase.mul ha).integrable_of_hasCompactSupport hc.mul_left

/-- The full leading stationary-phase expansion at scale `ε`, including the
remainder limit, the exact finite critical set, determinant magnitude, and
intrinsic Hessian signature. All localization data are constructed. -/
theorem exists_stationary_phase_expansion_scale
    {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {a : ℝ^n → ℂ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hc : HasCompactSupport a)
    (hdet : ∀ p ∈ tsupport a, fderiv ℝ φ p = 0 →
      (PDE.Analysis.hessianMatrix φ p).det ≠ 0) :
    ∃ C : Finset (ℝ^n),
      (∀ p, p ∈ C ↔ p ∈ tsupport a ∧ fderiv ℝ φ p = 0) ∧
      Tendsto (fun ε : ℝ ↦ ((ε : ℂ) ^ n)⁻¹ *
        (oscillatoryIntegral φ a ε - (ε : ℂ) ^ n *
          ∑ p : C, Complex.exp ((φ p / ε ^ 2 : ℝ) * I) * hessianFresnel φ p * a p))
        (𝓝[>] 0) (𝓝 0) := by
  classical
  let hfinite := finite_criticalPoints hφ hc hdet
  let C := hfinite.toFinset
  have hC (p : ℝ^n) : p ∈ C ↔ p ∈ tsupport a ∧ fderiv ℝ φ p = 0 :=
    hfinite.mem_toFinset
  choose U hU hpU hlocal using fun p : C ↦
    exists_local_stationary_phase hφ ((hC p).mp p.property).2
      (hdet p ((hC p).mp p.property).1 ((hC p).mp p.property).2)
  obtain ⟨b, r, hb, hrd, hrc, hrne, hsplit⟩ :=
    exists_stationary_partition ha hc C hC U hU hpU
  have hlin (ε : ℝ) :
      oscillatoryIntegral φ a ε =
        oscillatoryIntegral φ r ε + ∑ p : C, oscillatoryIntegral φ (b p) ε := by
    have hri := integrable_oscillatory hφ.continuous hrd.continuous hrc ε
    have hbi (p : C) := integrable_oscillatory hφ.continuous
      (hb p).1.continuous (hb p).2.1 ε
    unfold oscillatoryIntegral
    calc
      _ = ∫ x, (Complex.exp ((φ x / ε ^ 2 : ℝ) * I) * r x +
          ∑ p : C, Complex.exp ((φ x / ε ^ 2 : ℝ) * I) * b p x) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hsplit x, mul_add, Finset.mul_sum]
      _ = _ := by
        rw [integral_add hri (integrable_finsetSum _ (fun p _ ↦ hbi p)),
          integral_finsetSum _ (fun p _ ↦ hbi p)]
  have hterm (p : C) :
      Tendsto (fun ε : ℝ ↦ ((ε : ℂ) ^ n)⁻¹ *
        (oscillatoryIntegral φ (b p) ε - (ε : ℂ) ^ n *
          (Complex.exp ((φ p / ε ^ 2 : ℝ) * I) * hessianFresnel φ p * a p)))
        (𝓝[>] 0) (𝓝 0) := by
    simpa only [(hb p).2.2.2] using
      hlocal p (b p) (hb p).1 (hb p).2.1 (hb p).2.2.1
  have hsum := tendsto_finsetSum Finset.univ (fun p _ ↦ hterm p)
  simp only [Finset.sum_const_zero] at hsum
  have h := (tendsto_noncritical_remainder hφ hrd hrc hrne).add hsum
  rw [add_zero] at h
  refine ⟨C, hC, h.congr ?_⟩
  intro ε
  rw [hlin]
  simp only [mul_sub, mul_add, Finset.mul_sum, Finset.sum_sub_distrib]
  exact (add_sub_assoc _ _ _).symm

end PDE.Analysis.StationaryPhase
