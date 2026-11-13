/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import CAS.ExactTactic

/-!
# Polynomial weight allocation in an L² pairing

For a nonnegative scalar function `S`, a coefficient satisfying `S |f| ≤ C`
leaves square weight `S³` on the second factor when the test weight is
bounded by `B S⁵`. The conclusion includes membership of the product and
integrability of its pairing with a represented test function. The measure
is arbitrary, and all weight comparisons hold almost everywhere.
-/

@[expose] public section

noncomputable section

namespace MeasureTheory

open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- The polynomial weight allocation controls the source itself in L².
This keeps the bound independent of whichever test is paired with it later. -/
theorem polynomial_weighted_memLp_and_lpNorm_le
    (A B C : ℝ) (S f H Φ : X → ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hS : 0 ≤ᵐ[ν] S) (hf : AEStronglyMeasurable f ν)
    (hH : AEStronglyMeasurable H ν)
    (hΦmeas : AEStronglyMeasurable Φ ν)
    (hcompare : ∀ᵐ x ∂ν, Φ x ≤ B * S x ^ 5)
    (hpoint : ∀ᵐ x ∂ν, S x * |f x| ≤ C)
    (hmem : MemLp (fun x ↦ H x * √(S x) ^ 3) 2 ν) :
    MemLp (fun x ↦ (A * f x * H x) * √(Φ x)) 2 ν ∧
      lpNorm (fun x ↦ (A * f x * H x) * √(Φ x)) 2 ν ≤
        (A * √B * C) *
          lpNorm (fun x ↦ H x * √(S x) ^ 3) 2 ν := by
  let K := A * √B * C
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hscaled : MemLp (fun x ↦ K * (H x * √(S x) ^ 3)) 2 ν :=
    hmem.const_mul K
  have hmeas : AEStronglyMeasurable
      (fun x ↦ (A * f x * H x) * √(Φ x)) ν :=
    ((hf.const_mul A).mul hH).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hΦmeas)
  have hdom : ∀ᵐ x ∂ν,
      ‖(A * f x * H x) * √(Φ x)‖ ≤
        ‖K * (H x * √(S x) ^ 3)‖ := by
    filter_upwards [hcompare, hpoint, hS] with x hx hfx hSx
    have hsquare : (√B * S x * √(S x) ^ 3) ^ 2 = B * S x ^ 5 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hB, ← pow_mul, Nat.mul_comm 3 2, pow_mul,
        Real.sq_sqrt hSx]
      cas
    have hs : √(Φ x) ≤ √B * S x * √(S x) ^ 3 := by
      have hnonneg : 0 ≤ √B * S x * √(S x) ^ 3 :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg B) hSx)
          (pow_nonneg (Real.sqrt_nonneg (S x)) 3)
      have h := Real.sqrt_le_sqrt hx
      rw [← hsquare, Real.sqrt_sq hnonneg] at h
      exact h
    have hfscaled : |f x| * √(Φ x) ≤
        √B * C * √(S x) ^ 3 := by
      calc
        _ ≤ |f x| * (√B * S x * √(S x) ^ 3) :=
          mul_le_mul_of_nonneg_left hs (abs_nonneg _)
        _ = √B * (S x * |f x|) * √(S x) ^ 3 := by cas
        _ ≤ √B * C * √(S x) ^ 3 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfx (Real.sqrt_nonneg _)) (by positivity)
    calc
      _ = (A * |H x|) * (|f x| * √(Φ x)) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hA,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        cas
      _ ≤ (A * |H x|) * (√B * C * √(S x) ^ 3) :=
        mul_le_mul_of_nonneg_left hfscaled (by positivity)
      _ = _ := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK, abs_mul,
          abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)]
        dsimp only [K]
        cas
  have hsource := hscaled.mono hmeas hdom
  have hnorm : lpNorm (fun x ↦ (A * f x * H x) * √(Φ x)) 2 ν ≤
      K * lpNorm (fun x ↦ H x * √(S x) ^ 3) 2 ν := by
    have hn : lpNorm (fun x ↦ (A * f x * H x) * √(Φ x)) 2 ν ≤
        lpNorm (fun x ↦ K * (H x * √(S x) ^ 3)) 2 ν := by
      rw [← toReal_eLpNorm, ← toReal_eLpNorm]
      exact ENNReal.toReal_mono hscaled.eLpNorm_ne_top (eLpNorm_mono_ae hmeas hdom)
    change lpNorm (fun x ↦ (A * f x * H x) * √(Φ x)) 2 ν ≤
      lpNorm (K • (fun x ↦ H x * √(S x) ^ 3)) 2 ν at hn
    simpa only [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hK] using hn
  exact ⟨hsource, hnorm⟩

/-- Transfer two square powers to the low factor, and pair the remaining
weighted norm with a represented test function. No positivity away from zero
or regularity of the scalar weight is required. -/
theorem polynomial_weighted_work_le_of_norm
    (A B C : ℝ) (S f H g Φ : X → ℝ) (test : Lp ℝ 2 ν)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hS : 0 ≤ᵐ[ν] S) (hf : AEStronglyMeasurable f ν)
    (hH : AEStronglyMeasurable H ν)
    (hΦmeas : AEStronglyMeasurable Φ ν) (hΦ : 0 ≤ᵐ[ν] Φ)
    (hcompare : ∀ᵐ x ∂ν, Φ x ≤ B * S x ^ 5)
    (hpoint : ∀ᵐ x ∂ν, S x * |f x| ≤ C)
    (hmem : MemLp (fun x ↦ H x * √(S x) ^ 3) 2 ν)
    (htest : (test : X → ℝ) =ᵐ[ν] fun x ↦ g x * √(Φ x)) :
    MemLp (fun x ↦ (A * f x * H x) * √(Φ x)) 2 ν ∧
      Integrable (fun x ↦ A * f x * H x * g x * Φ x) ν ∧
      |∫ x, A * f x * H x * g x * Φ x ∂ν| ≤
        (A * √B * C) *
          lpNorm (fun x ↦ H x * √(S x) ^ 3) 2 ν * ‖test‖ := by
  rcases polynomial_weighted_memLp_and_lpNorm_le A B C S f H Φ hA hB hC
    hS hf hH hΦmeas hcompare hpoint hmem with ⟨hsource, hnorm⟩
  have hi := hsource.integrable_mul (Lp.memLp test)
  have heq : (fun x ↦ ((A * f x * H x) * √(Φ x)) * test x) =ᵐ[ν]
      fun x ↦ A * f x * H x * g x * Φ x := by
    filter_upwards [htest, hΦ] with x hx hxΦ
    rw [hx]
    calc
      _ = A * f x * H x * g x * √(Φ x) ^ 2 := by cas
      _ = _ := by rw [Real.sq_sqrt hxΦ]
  have htestNorm : lpNorm (test : X → ℝ) 2 ν = ‖test‖ := by
    rw [← toReal_eLpNorm]
    exact (Lp.norm_def test).symm
  have hpair := abs_integral_mul_le_lpNorm_two_mul_lpNorm_two hsource (Lp.memLp test)
  rw [htestNorm] at hpair
  refine ⟨hsource, hi.congr heq, ?_⟩
  calc
    _ = |∫ x, ((A * f x * H x) * √(Φ x)) * test x ∂ν| := by
      rw [integral_congr_ae heq]
    _ ≤ lpNorm (fun x ↦ (A * f x * H x) * √(Φ x)) 2 ν * ‖test‖ := hpair
    _ ≤ _ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

end MeasureTheory
