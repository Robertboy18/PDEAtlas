/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import CAS.ExactTactic

/-!
# Differentiation of weighted radial averages

Integration over the fixed interval `[0,1]` replaces a removable radial quotient.
Radial differentiation increases the power weight by one, while differentiation
in an external parameter preserves it. Compactness of a
smaller radial interval supplies the domination needed by Mathlib's parametric
integral theorem; no global smoothness or assumed integral derivative is needed.
-/

@[expose] public section
noncomputable section
namespace PDE.Calculus
open Filter MeasureTheory Set
open scoped Topology Interval

/-- A power-weighted average along the radial segment from zero to `r`. -/
def weightedRadialAverage (f : ℝ → ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t ^ n * f (t * r)

/-- At the axis the power weight integrates to the reciprocal of its successor. -/
theorem weightedRadialAverage_zero (f : ℝ → ℝ) (n : ℕ) :
    weightedRadialAverage f n 0 = f 0 / (n + 1) := by
  simp only [weightedRadialAverage, mul_zero, intervalIntegral.integral_mul_const,
    integral_pow, one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero]
  simp only [div_eq_mul_inv, one_mul, mul_comm]

/-- A continuous derivative on a symmetric open interval differentiates the
weighted radial average there. The extra factor `t` increments the weight. -/
theorem hasDerivAt_weightedRadialAverage {f f' : ℝ → ℝ} {R r : ℝ} (n : ℕ)
    (hderiv : ∀ x ∈ Ioo (-R) R, HasDerivAt f (f' x) x)
    (hcont' : ContinuousOn f' (Ioo (-R) R)) (hr : r ∈ Ioo (-R) R) :
    HasDerivAt (weightedRadialAverage f n)
      (weightedRadialAverage f' (n + 1) r) r := by
  have habs : |r| < R := abs_lt.mpr hr
  let b := (|r| + R) / 2
  have hrb : |r| < b := by dsimp [b]; linarith
  have hbR : b < R := by dsimp [b]; linarith
  have harg {x t : ℝ} (hx : x ∈ Icc (-b) b) (ht : t ∈ Icc (0 : ℝ) 1) :
      t * x ∈ Ioo (-R) R := by
    apply abs_lt.mp
    calc
      |t * x| = t * |x| := by rw [abs_mul, abs_of_nonneg ht.1]
      _ ≤ 1 * b := mul_le_mul ht.2 (abs_le.mpr hx) (abs_nonneg x) (by norm_num)
      _ < R := by simpa using hbR
  have hcont : ContinuousOn f (Ioo (-R) R) :=
    fun x hx ↦ (hderiv x hx).continuousAt.continuousWithinAt
  have hF (x : ℝ) (hx : x ∈ Icc (-b) b) :
      ContinuousOn (fun t ↦ t ^ n * f (t * x)) (Icc (0 : ℝ) 1) :=
    (continuous_id.pow n).continuousOn.mul
      (hcont.comp (continuous_id.mul continuous_const).continuousOn (fun _ ht ↦ harg hx ht))
  have hF' (x : ℝ) (hx : x ∈ Icc (-b) b) :
      ContinuousOn (fun t ↦ t ^ (n + 1) * f' (t * x)) (Icc (0 : ℝ) 1) :=
    (continuous_id.pow (n + 1)).continuousOn.mul
      (hcont'.comp (continuous_id.mul continuous_const).continuousOn (fun _ ht ↦ harg hx ht))
  let K := Icc (-b) b ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hJoint : ContinuousOn (fun p : ℝ × ℝ ↦ p.2 ^ (n + 1) * f' (p.2 * p.1)) K :=
    (continuous_snd.pow (n + 1)).continuousOn.mul
      (hcont'.comp (continuous_snd.mul continuous_fst).continuousOn
        (fun _ hp ↦ harg hp.1 hp.2))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hJoint
  have hsub : Ι (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using
      (Set.uIoc_subset_uIcc : Ι (0 : ℝ) 1 ⊆ uIcc (0 : ℝ) 1)
  have hnr : Ioo (-b) b ∈ nhds r := isOpen_Ioo.mem_nhds (abs_lt.mp hrb)
  have hrclosed : r ∈ Icc (-b) b := ⟨(abs_lt.mp hrb).1.le, (abs_lt.mp hrb).2.le⟩
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (F := fun x t ↦ t ^ n * f (t * x))
    (F' := fun x t ↦ t ^ (n + 1) * f' (t * x)) (bound := fun _ ↦ C) hnr
    (by
      filter_upwards [hnr] with x hx
      exact ((hF x ⟨hx.1.le, hx.2.le⟩).mono hsub).aestronglyMeasurable
        measurableSet_uIoc)
    ((hF r hrclosed).intervalIntegrable_of_Icc (by norm_num))
    (((hF' r hrclosed).mono hsub).aestronglyMeasurable measurableSet_uIoc)
    (by
      filter_upwards [] with t ht x hx
      exact hC (x, t) ⟨⟨hx.1.le, hx.2.le⟩, hsub ht⟩)
    (intervalIntegrable_const)
    (by
      filter_upwards [] with t ht x hx
      have ht' : t ∈ Icc (0 : ℝ) 1 := hsub ht
      have hd := ((hderiv (t * x) (harg ⟨hx.1.le, hx.2.le⟩ ht')).comp x
        ((hasDerivAt_id x).const_mul t)).const_mul (t ^ n)
      convert! hd using 1
      simp only [pow_succ]
      cas)
  exact h.2

/-- An explicit continuous derivative family gives every radial derivative of the
weighted average on the same open interval, including at zero. This is a radial
statement; mixed derivatives in an additional parameter are not covered. -/
theorem iteratedDeriv_weightedRadialAverage (F : ℕ → ℝ → ℝ) {R : ℝ} (m n : ℕ)
    (hcont : ∀ j ≤ m, ContinuousOn (F j) (Ioo (-R) R))
    (hderiv : ∀ j < m, ∀ x ∈ Ioo (-R) R, HasDerivAt (F j) (F (j + 1) x) x)
    (k : ℕ) (hk : k ≤ m) {r : ℝ} (hr : r ∈ Ioo (-R) R) :
    iteratedDeriv k (weightedRadialAverage (F 0) n) r =
      weightedRadialAverage (F k) (n + k) r := by
  induction k generalizing r with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv k (weightedRadialAverage (F 0) n) =ᶠ[𝓝 r]
        weightedRadialAverage (F k) (n + k) := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx
      exact ih (Nat.le_of_succ_le hk) hx
    rw [heq.deriv_eq]
    simpa only [Nat.add_assoc] using
      (hasDerivAt_weightedRadialAverage (n + k) (hderiv k (Nat.lt_of_succ_le hk))
        (hcont (k + 1) hk) hr).deriv

/-- Differentiation in an external parameter keeps the radial power weight fixed.
Joint continuity is only required on the radial segment and an open parameter interval. -/
theorem hasDerivAt_weightedRadialAverage_parameter {f fz : ℝ → ℝ → ℝ}
    {r a b z : ℝ} (n : ℕ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ ↦ f p.1 p.2) (uIcc 0 r ×ˢ Ioo a b))
    (hcontz : ContinuousOn (fun p : ℝ × ℝ ↦ fz p.1 p.2) (uIcc 0 r ×ˢ Ioo a b))
    (hderiv : ∀ s ∈ uIcc 0 r, ∀ y ∈ Ioo a b, HasDerivAt (f s) (fz s y) y)
    (hz : z ∈ Ioo a b) :
    HasDerivAt (fun y ↦ weightedRadialAverage (fun s ↦ f s y) n r)
      (weightedRadialAverage (fun s ↦ fz s z) n r) z := by
  let l := (a + z) / 2
  let u := (z + b) / 2
  have hl : a < l ∧ l < z := by dsimp [l]; constructor <;> linarith [hz.1]
  have hu : z < u ∧ u < b := by dsimp [u]; constructor <;> linarith [hz.2]
  have hsubz : Icc l u ⊆ Ioo a b := fun _ hy ↦
    ⟨hl.1.trans_le hy.1, hy.2.trans_lt hu.2⟩
  have harg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t * r ∈ uIcc 0 r := by
    rcases le_total 0 r with hr | hr
    · rw [uIcc_of_le hr]
      exact ⟨mul_nonneg ht.1 hr, by simpa using mul_le_mul_of_nonneg_right ht.2 hr⟩
    · rw [uIcc_of_ge hr]
      exact ⟨by simpa using mul_le_mul_of_nonpos_right ht.2 hr,
        mul_nonpos_of_nonneg_of_nonpos ht.1 hr⟩
  have hF (g : ℝ → ℝ → ℝ)
      (hg : ContinuousOn (fun p : ℝ × ℝ ↦ g p.1 p.2) (uIcc 0 r ×ˢ Ioo a b))
      (y : ℝ) (hy : y ∈ Icc l u) :
      ContinuousOn (fun t ↦ t ^ n * g (t * r) y) (Icc (0 : ℝ) 1) :=
    (continuous_id.pow n).continuousOn.mul
      (hg.comp ((continuous_id.mul continuous_const).prodMk continuous_const).continuousOn
        (fun _ ht ↦ ⟨harg ht, hsubz hy⟩))
  have hJoint : ContinuousOn (fun p : ℝ × ℝ ↦ p.2 ^ n * fz (p.2 * r) p.1)
      (Icc l u ×ˢ Icc (0 : ℝ) 1) :=
    (continuous_snd.pow n).continuousOn.mul
      (hcontz.comp ((continuous_snd.mul continuous_const).prodMk continuous_fst).continuousOn
        (fun _ hp ↦ ⟨harg hp.2, hsubz hp.1⟩))
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hJoint
  have hsub : Ι (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using
      (Set.uIoc_subset_uIcc : Ι (0 : ℝ) 1 ⊆ uIcc (0 : ℝ) 1)
  have hnz : Ioo l u ∈ nhds z := isOpen_Ioo.mem_nhds ⟨hl.2, hu.1⟩
  have hzclosed : z ∈ Icc l u := ⟨hl.2.le, hu.1.le⟩
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (F := fun y t ↦ t ^ n * f (t * r) y)
    (F' := fun y t ↦ t ^ n * fz (t * r) y) (bound := fun _ ↦ C) hnz
    (by
      filter_upwards [hnz] with y hy
      exact ((hF f hcont y ⟨hy.1.le, hy.2.le⟩).mono hsub).aestronglyMeasurable
        measurableSet_uIoc)
    ((hF f hcont z hzclosed).intervalIntegrable_of_Icc (by norm_num))
    (((hF fz hcontz z hzclosed).mono hsub).aestronglyMeasurable measurableSet_uIoc)
    (by
      filter_upwards [] with t ht y hy
      exact hC (y, t) ⟨⟨hy.1.le, hy.2.le⟩, hsub ht⟩)
    intervalIntegrable_const
    (by
      filter_upwards [] with t ht y hy
      exact (hderiv (t * r) (harg (hsub ht)) y
        (hsubz ⟨hy.1.le, hy.2.le⟩)).const_mul (t ^ n))
  exact h.2

/-- An actual derivative family in the external parameter differentiates its
radial average to any supported order, without changing the power weight. -/
theorem iteratedDeriv_weightedRadialAverage_parameter (F : ℕ → ℝ → ℝ → ℝ)
    {r a b : ℝ} (m n : ℕ)
    (hcont : ∀ j ≤ m,
      ContinuousOn (fun p : ℝ × ℝ ↦ F j p.1 p.2) (uIcc 0 r ×ˢ Ioo a b))
    (hderiv : ∀ j < m, ∀ s ∈ uIcc 0 r, ∀ y ∈ Ioo a b,
      HasDerivAt (F j s) (F (j + 1) s y) y)
    (k : ℕ) (hk : k ≤ m) {z : ℝ} (hz : z ∈ Ioo a b) :
    iteratedDeriv k (fun y ↦ weightedRadialAverage (fun s ↦ F 0 s y) n r) z =
      weightedRadialAverage (fun s ↦ F k s z) n r := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have heq :
        iteratedDeriv k (fun y ↦ weightedRadialAverage (fun s ↦ F 0 s y) n r) =ᶠ[𝓝 z]
        (fun y ↦ weightedRadialAverage (fun s ↦ F k s y) n r) := by
      filter_upwards [isOpen_Ioo.mem_nhds hz] with y hy
      exact ih (Nat.le_of_succ_le hk) hy
    rw [heq.deriv_eq]
    exact (hasDerivAt_weightedRadialAverage_parameter n (hcont k (Nat.le_of_succ_le hk))
      (hcont (k + 1) hk) (hderiv k (Nat.lt_of_succ_le hk)) hz).deriv

/-- A uniform segment bound gives the sharp power-average factor. -/
theorem abs_weightedRadialAverage_le {f : ℝ → ℝ} (n : ℕ) (r M : ℝ)
    (hf : ContinuousOn f (uIcc 0 r))
    (hbound : ∀ s ∈ uIcc 0 r, |f s| ≤ M) :
    |weightedRadialAverage f n r| ≤ M / ((n : ℝ) + 1) := by
  have hsegment {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t * r ∈ uIcc 0 r := by
    rcases le_total 0 r with hr | hr
    · rw [uIcc_of_le hr]
      constructor <;> nlinarith [ht.1, ht.2]
    · rw [uIcc_of_ge hr]
      constructor <;> nlinarith [ht.1, ht.2]
  have hc : ContinuousOn (fun t : ℝ ↦ t ^ n * f (t * r)) (Icc (0 : ℝ) 1) :=
    (continuous_id.pow n).continuousOn.mul
      (hf.comp (continuous_id.mul continuous_const).continuousOn (fun _ ht ↦ hsegment ht))
  have hmajor : Continuous (fun t : ℝ ↦ t ^ n * M) :=
    (continuous_id.pow n).mul continuous_const
  calc
    |weightedRadialAverage f n r| ≤ ∫ t in (0 : ℝ)..1, |t ^ n * f (t * r)| :=
      intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, t ^ n * M :=
      intervalIntegral.integral_mono_on zero_le_one
        (hc.abs.intervalIntegrable_of_Icc zero_le_one) (hmajor.intervalIntegrable 0 1)
        (fun t ht ↦ by
          rw [abs_mul, abs_of_nonneg (pow_nonneg ht.1 n)]
          exact mul_le_mul_of_nonneg_left (hbound _ (hsegment ht)) (pow_nonneg ht.1 n))
    _ = M / ((n : ℝ) + 1) := by
      rw [intervalIntegral.integral_mul_const, integral_pow]
      simp [div_eq_mul_inv, mul_comm]

end PDE.Calculus
