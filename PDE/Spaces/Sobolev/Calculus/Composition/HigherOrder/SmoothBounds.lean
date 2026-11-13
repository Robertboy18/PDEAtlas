/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.GagliardoNirenberg.TensorNorm

/-!
# Bounds for smooth nonlinear composition

Taking the `j`-th root of each order-`j` derivative norm produces a common
majorant for the higher chain rule. Derivative interpolation puts this
majorant in `L^{2k}`, so its `k`-th power is square integrable.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.Composition

open GagliardoNirenberg

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A common majorant for all positive derivative orders through `k`. -/
def higherChainGauge (k : ℕ) (u : ℝ^n → E) (x : ℝ^n) : ℝ :=
  ∑ i : Fin k, ‖iteratedFDeriv ℝ (i.val + 1) u x‖ ^ (((i.val + 1 : ℕ) : ℝ)⁻¹)

theorem higherChainGauge_nonneg (k : ℕ) (u : ℝ^n → E) (x : ℝ^n) :
    0 ≤ higherChainGauge k u x :=
  Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _

/-- Each order-`j` derivative norm is bounded by the `j`-th power of the gauge. -/
theorem norm_iteratedFDeriv_le_higherChainGauge_pow
    {k j : ℕ} (hj : 0 < j) (hjk : j ≤ k) (u : ℝ^n → E) (x : ℝ^n) :
    ‖iteratedFDeriv ℝ j u x‖ ≤ higherChainGauge k u x ^ j := by
  let i : Fin k := ⟨j - 1, by omega⟩
  have hi : i.val + 1 = j := by dsimp only [i]; omega
  have hsum : ‖iteratedFDeriv ℝ j u x‖ ^ ((j : ℝ)⁻¹) ≤ higherChainGauge k u x := by
    have h := Finset.single_le_sum
        (fun l (_ : l ∈ (Finset.univ : Finset (Fin k))) ↦
          Real.rpow_nonneg (norm_nonneg (iteratedFDeriv ℝ (l.val + 1) u x))
            (((l.val + 1 : ℕ) : ℝ)⁻¹))
        (Finset.mem_univ i)
    change ‖iteratedFDeriv ℝ (i.val + 1) u x‖ ^ (((i.val + 1 : ℕ) : ℝ)⁻¹) ≤
      higherChainGauge k u x at h
    rwa [hi] at h
  calc
    _ = (‖iteratedFDeriv ℝ j u x‖ ^ ((j : ℝ)⁻¹)) ^ j :=
      (Real.rpow_inv_natCast_pow (norm_nonneg _) hj.ne').symm
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hsum j

/-- The ordinary higher chain rule is controlled by the common gauge. -/
theorem norm_iteratedFDeriv_comp_le_higherChainGauge
    (k : ℕ) {f : E → ℝ} {u : ℝ^n → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (x : ℝ^n) {C : ℝ}
    (hC : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f (u x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (f ∘ u) x‖ ≤
      (k.factorial : ℝ) * C * higherChainGauge k u x ^ k :=
  norm_iteratedFDeriv_comp_le hf hu (by simp) x hC
    (fun j hj hjk ↦ norm_iteratedFDeriv_le_higherChainGauge_pow hj hjk u x)

theorem continuous_higherChainGauge {u : ℝ^n → E}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (k : ℕ) :
    Continuous (higherChainGauge k u) := by
  apply continuous_finsetSum
  intro i _
  exact (hu.continuous_iteratedFDeriv (by simp)).norm.rpow_const
    (fun _ ↦ Or.inr (by positivity))

theorem HasCompactSupport.higherChainGauge {u : ℝ^n → E}
    (hu : HasCompactSupport u) (k : ℕ) :
    HasCompactSupport (higherChainGauge k u) := by
  have hcomp (i : Fin k) :
      HasCompactSupport
        (fun x ↦ ‖iteratedFDeriv ℝ (i.val + 1) u x‖ ^ (((i.val + 1 : ℕ) : ℝ)⁻¹)) := by
    apply (hu.iteratedFDeriv (i.val + 1)).comp_left
      (g := fun T ↦ ‖T‖ ^ (((i.val + 1 : ℕ) : ℝ)⁻¹))
    simp only [norm_zero]
    exact Real.zero_rpow (by positivity)
  have hsum := HasCompactSupport.finset_sum (s := Finset.univ) fun i _ ↦ hcomp i
  convert hsum using 1
  ext x
  simp only [SobolevSpace.Composition.higherChainGauge, Finset.sum_apply]

private theorem lpNorm_norm_rpow {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {ν : Measure X} {v : X → E} {q : ℝ≥0∞} {a : ℝ}
    (hv : AEStronglyMeasurable v ν) (ha : 0 < a) :
    lpNorm (fun x ↦ ‖v x‖ ^ a) q ν = lpNorm v (q * ENNReal.ofReal a) ν ^ a := by
  simpa only [← ENNReal.toReal_rpow, toReal_eLpNorm] using
    congrArg ENNReal.toReal (eLpNorm_norm_rpow v hv ha (p := q))

/-- Interpolation exponents convert the roots of all derivative norms into
the same `L^{2k}` space. This explicit estimate is uniform in the support. -/
theorem lpNorm_higherChainGauge_le {k : ℕ} (hk : 0 < k) {u : ℝ^n → E}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huc : HasCompactSupport u)
    (C : Fin k → ℝ)
    (hC : ∀ i : Fin k,
      lpNorm (iteratedFDeriv ℝ (i.val + 1) u)
        (derivativeExponent k (i.val + 1)) volume ≤ C i) :
    lpNorm (higherChainGauge k u) (ENNReal.ofReal (2 * (k : ℝ))) volume ≤
      ∑ i : Fin k, C i ^ (((i.val + 1 : ℕ) : ℝ)⁻¹) := by
  let v (i : Fin k) (x : ℝ^n) :=
    ‖iteratedFDeriv ℝ (i.val + 1) u x‖ ^ (((i.val + 1 : ℕ) : ℝ)⁻¹)
  have hmem (i : Fin k) : MemLp (v i) (ENNReal.ofReal (2 * (k : ℝ))) volume := by
    have hc : Continuous (v i) :=
      (hu.continuous_iteratedFDeriv (by simp)).norm.rpow_const
        (fun _ ↦ Or.inr (by positivity))
    have hs : HasCompactSupport (v i) := by
      apply (huc.iteratedFDeriv (i.val + 1)).comp_left
        (g := fun T ↦ ‖T‖ ^ (((i.val + 1 : ℕ) : ℝ)⁻¹))
      simp only [norm_zero]
      exact Real.zero_rpow (by positivity)
    exact hc.memLp_of_hasCompactSupport hs
  have hv (i : Fin k) :
      lpNorm (v i) (ENNReal.ofReal (2 * (k : ℝ))) volume ≤
        C i ^ (((i.val + 1 : ℕ) : ℝ)⁻¹) := by
    dsimp only [v]
    rw [lpNorm_norm_rpow (v := iteratedFDeriv ℝ (i.val + 1) u)
      (a := (((i.val + 1 : ℕ) : ℝ)⁻¹))
      (hu.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable (by positivity)]
    have heq : ENNReal.ofReal (2 * (k : ℝ)) *
        ENNReal.ofReal (((i.val + 1 : ℕ) : ℝ)⁻¹) = derivativeExponent k (i.val + 1) := by
      rw [derivativeExponent_eq_of_pos hk (by omega), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
    rw [heq]
    exact Real.rpow_le_rpow lpNorm_nonneg (hC i) (by positivity)
  have heq : higherChainGauge k u = ∑ i : Fin k, v i := by
    ext x
    simp only [higherChainGauge, Finset.sum_apply, v]
  rw [heq]
  apply (lpNorm_sum_le (fun i _ ↦ hmem i) ?_).trans
    (Finset.sum_le_sum fun i _ ↦ hv i)
  have hk' : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hr : (1 : ℝ) ≤ 2 * k := by linarith
  simpa using ENNReal.ofReal_le_ofReal hr

/-- Bounds on the reaction derivatives and on the interpolated spatial
derivatives give an `L²` bound for the full derivative of the composition.
Only reaction values attained by the input appear in the hypotheses. -/
theorem memLp_and_lpNorm_iteratedFDeriv_comp_le {k : ℕ} (hk : 0 < k)
    {f : E → ℝ} {u : ℝ^n → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (huc : HasCompactSupport u) {C : ℝ} (hC : 0 ≤ C)
    (hreact : ∀ x j, j ≤ k → ‖iteratedFDeriv ℝ j f (u x)‖ ≤ C)
    (A : Fin k → ℝ)
    (hA : ∀ i : Fin k,
      lpNorm (iteratedFDeriv ℝ (i.val + 1) u)
        (derivativeExponent k (i.val + 1)) volume ≤ A i) :
    MemLp (iteratedFDeriv ℝ k (f ∘ u)) 2 volume ∧
      lpNorm (iteratedFDeriv ℝ k (f ∘ u)) 2 volume ≤
        (k.factorial : ℝ) * C * (∑ i : Fin k, A i ^ (((i.val + 1 : ℕ) : ℝ)⁻¹)) ^ k := by
  let G := higherChainGauge k u
  have hG : Continuous G := continuous_higherChainGauge hu k
  have hGc : HasCompactSupport G := HasCompactSupport.higherChainGauge huc k
  have hGp : MemLp (fun x ↦ G x ^ k) 2 volume :=
    (hG.pow k).memLp_of_hasCompactSupport
      (hGc.comp_left (g := fun x : ℝ ↦ x ^ k) (zero_pow hk.ne'))
  have hmajor : MemLp (fun x ↦ (k.factorial : ℝ) * C * G x ^ k) 2 volume :=
    hGp.const_mul _
  have hpoint (x : ℝ^n) :
      ‖iteratedFDeriv ℝ k (f ∘ u) x‖ ≤ (k.factorial : ℝ) * C * G x ^ k :=
    norm_iteratedFDeriv_comp_le_higherChainGauge k hf hu x (hreact x)
  refine ⟨hmajor.mono' ((hf.comp hu).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
    (Filter.Eventually.of_forall hpoint), ?_⟩
  have hpower : lpNorm (fun x ↦ G x ^ k) 2 volume =
      lpNorm G (ENNReal.ofReal (2 * (k : ℝ))) volume ^ k := by
    have h := lpNorm_norm_rpow (ν := volume) (q := 2) (a := (k : ℝ)) hG.aestronglyMeasurable
      (by exact_mod_cast hk)
    have heq : (fun x ↦ ‖G x‖ ^ (k : ℝ)) = fun x ↦ G x ^ k := by
      ext x
      rw [Real.norm_eq_abs, abs_of_nonneg (higherChainGauge_nonneg k u x),
        Real.rpow_natCast]
    rw [heq, Real.rpow_natCast] at h
    have hexp : (2 : ℝ≥0∞) * ENNReal.ofReal (k : ℝ) =
        ENNReal.ofReal (2 * (k : ℝ)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      norm_num
    simpa only [hexp] using h
  calc
    _ ≤ lpNorm (fun x ↦ (k.factorial : ℝ) * C * G x ^ k) 2 volume :=
      lpNorm_mono_real hmajor hpoint
    _ = (k.factorial : ℝ) * C * lpNorm (fun x ↦ G x ^ k) 2 volume := by
      change lpNorm (((k.factorial : ℝ) * C) • (fun x ↦ G x ^ k)) 2 volume = _
      rw [lpNorm_const_smul]
      simp only [coe_nnnorm, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hC)]
    _ ≤ _ := by
      rw [hpower]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ lpNorm_nonneg (lpNorm_higherChainGauge_le hk hu huc A hA) k)
        (mul_nonneg (by positivity) hC)

end SobolevSpace.Composition
