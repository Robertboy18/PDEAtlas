/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.Radial.Average.L2
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import PDE.Analysis.MeasureTheory.LpNorm
import CAS.ExactTactic

/-!
# Sharp radial-average bounds with polynomial weights

Radial dilation by `t` has squared L² cost `1/t` for the physical measure `dr`.
Splitting the averaging power symmetrically around this half power gives the
constant `1/(n+1/2)`. In particular, the zeroth average is bounded.

For `S(r,z) = 1+r²+z²`, the comparison `t² S(r,z) ≤ S(tr,z)` moves the weight
inside the average and lowers its power from `n` to `n-q`. The endpoint `n=q`
therefore has norm bound `2`. Only the weighted source belongs to L² by
hypothesis; the actual integral supplies the output.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Calculus

private theorem halfPower_time_mass (n : ℕ) :
    Integrable (fun t : ℝ ↦ |t| ^ ((n : ℝ) - 1 / 2))
        (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      (∫ t in Ioc (0 : ℝ) 1, |t| ^ ((n : ℝ) - 1 / 2)) =
        1 / ((n : ℝ) + 1 / 2) := by
  have hn : -1 < (n : ℝ) - 1 / 2 := by
    have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    cas using this
  have heq : (fun t : ℝ ↦ t ^ ((n : ℝ) - 1 / 2)) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) 1)]
      (fun t ↦ |t| ^ ((n : ℝ) - 1 / 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [abs_of_pos ht.1]
  refine ⟨((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
    (intervalIntegral.intervalIntegrable_rpow' hn)).congr heq, ?_⟩
  rw [← integral_congr_ae heq, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl hn)]
  have hexp : (n : ℝ) - 1 / 2 + 1 = (n : ℝ) + 1 / 2 := by cas
  rw [hexp, Real.one_rpow, Real.zero_rpow (by positivity), sub_zero]

/-- The radial average of a continuous function is continuous. -/
private theorem continuous_weightedRadialAverage {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    Continuous (weightedRadialAverage f n) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) 0 1

/-- The actual radial average has L² norm at most `1/(n+1/2)` times the
source norm. This includes `n=0`; the half-power time weight is integrable
there. Continuity supplies joint measurability, while source L² membership
supplies all integrability estimates. -/
theorem weightedRadialAverage_memLp_and_lpNorm_le_sharp
    (n : ℕ) {f : ℝ → ℝ} (hcont : Continuous f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (weightedRadialAverage f n) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      lpNorm (weightedRadialAverage f n) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
        (1 / ((n : ℝ) + 1 / 2)) *
          lpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let τ : Measure ℝ := volume.restrict (Ioc 0 1)
  let C : ℝ := 1 / ((n : ℝ) + 1 / 2)
  let H : ℝ → ℝ := fun t ↦ |t| ^ ((n : ℝ) - 1 / 2)
  let Q : ℝ × ℝ → ℝ := fun p ↦
    |p.2| ^ ((n : ℝ) + 1 / 2) * f (p.2 * p.1) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hH0 (t : ℝ) : 0 ≤ H t := Real.rpow_nonneg (abs_nonneg t) _
  obtain ⟨hHi, hHint⟩ := halfPower_time_mass n
  have hQ0 (p : ℝ × ℝ) : 0 ≤ Q p :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)
  have hQm : AEStronglyMeasurable Q (ν.prod τ) :=
    (((Real.continuous_rpow_const (by positivity : 0 ≤ (n : ℝ) + 1 / 2)).comp
      continuous_snd.abs).mul
        ((hcont.comp (continuous_snd.mul continuous_fst)).pow 2)).aestronglyMeasurable
  have hQcol : ∀ᵐ t ∂τ,
      Integrable (fun r ↦ Q (r, t)) ν ∧
        (∫ r, Q (r, t) ∂ν) = H t * (∫ r, f r ^ 2 ∂ν) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hi : Integrable (fun r ↦ f (t * r) ^ 2) ν := by
      apply (integrableOn_Ioi_comp_mul_left_iff (fun r ↦ f r ^ 2) 0 ht.1).2
      simpa only [mul_zero] using! hf.integrable_sq
    have hcol : Integrable (fun r ↦ Q (r, t)) ν := by
      simpa only [Q] using! hi.const_mul (|t| ^ ((n : ℝ) + 1 / 2))
    refine ⟨hcol, ?_⟩
    change (∫ r in Ioi (0 : ℝ),
      |t| ^ ((n : ℝ) + 1 / 2) * f (t * r) ^ 2) = _
    rw [integral_const_mul, integral_comp_mul_left_Ioi (fun r ↦ f r ^ 2) 0 ht.1,
      mul_zero, smul_eq_mul, ← mul_assoc]
    have hscale : |t| ^ ((n : ℝ) + 1 / 2) * t⁻¹ = H t := by
      dsimp only [H]
      rw [abs_of_pos ht.1, ← div_eq_mul_inv,
        ← Real.rpow_sub_one ht.1.ne']
      congr 1
      cas
    rw [hscale]
  have hQnorm (p : ℝ × ℝ) : ‖Q p‖ = Q p := Real.norm_of_nonneg (hQ0 p)
  have hQinner : Integrable (fun t ↦ ∫ r, ‖Q (r, t)‖ ∂ν) τ := by
    apply (hHi.mul_const (∫ r, f r ^ 2 ∂ν)).congr
    filter_upwards [hQcol] with t ht
    simpa only [hQnorm] using ht.2.symm
  have hQi : Integrable Q (ν.prod τ) :=
    (integrable_prod_iff' hQm).2 ⟨hQcol.mono fun _ h ↦ h.1, hQinner⟩
  have hQtotal : (∫ p, Q p ∂ν.prod τ) = C * (∫ r, f r ^ 2 ∂ν) := by
    rw [integral_prod_symm Q hQi]
    calc
      _ = ∫ t, H t * (∫ r, f r ^ 2 ∂ν) ∂τ :=
        integral_congr_ae (hQcol.mono fun _ h ↦ h.2)
      _ = _ := by rw [integral_mul_const, hHint]
  have hHLp : MemLp (fun t ↦ √(H t)) 2 τ :=
    (memLp_two_iff_integrable_sq hHi.aemeasurable.sqrt.aestronglyMeasurable).2
      (hHi.congr (.of_forall fun t ↦ (Real.sq_sqrt (hH0 t)).symm))
  have hpoint : ∀ᵐ r ∂ν,
      weightedRadialAverage f n r ^ 2 ≤ C * (∫ t, Q (r, t) ∂τ) := by
    filter_upwards [hQi.prod_right_ae] with r hQr
    have hQLp : MemLp (fun t ↦ √(Q (r, t))) 2 τ :=
      (memLp_two_iff_integrable_sq hQr.aemeasurable.sqrt.aestronglyMeasurable).2
        (hQr.congr (.of_forall fun t ↦ (Real.sq_sqrt (hQ0 (r, t))).symm))
    have hfactor : (fun t ↦ √(H t) * √(Q (r, t))) =ᵐ[τ]
        (fun t ↦ t ^ n * |f (t * r)|) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      dsimp only [Q, H]
      rw [abs_of_pos ht.1, Real.sqrt_mul (Real.rpow_nonneg ht.1.le _),
        Real.sqrt_sq_eq_abs, ← mul_assoc,
        ← Real.sqrt_mul (Real.rpow_nonneg ht.1.le _), ← Real.rpow_add ht.1]
      have hexp : (n : ℝ) - 1 / 2 + ((n : ℝ) + 1 / 2) = (n : ℝ) * 2 := by cas
      rw [hexp, Real.rpow_mul ht.1.le, Real.rpow_two, Real.rpow_natCast,
        Real.sqrt_sq (pow_nonneg ht.1.le n)]
    have hprod : Integrable (fun t ↦ t ^ n * |f (t * r)|) τ :=
      (hHLp.integrable_mul hQLp).congr hfactor
    have hcs : (∫ t, t ^ n * |f (t * r)| ∂τ) ≤
        √C * √(∫ t, Q (r, t) ∂τ) := by
      have hHs (t : ℝ) : √(H t) ^ 2 = H t := Real.sq_sqrt (hH0 t)
      have hQs (t : ℝ) : √(Q (r, t)) ^ 2 = Q (r, t) :=
        Real.sq_sqrt (hQ0 (r, t))
      have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
        (f := fun t ↦ √(H t)) (g := fun t ↦ √(Q (r, t)))
        (by simpa using hHLp) (by simpa using hQLp)
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.rpow_two, ← Real.sqrt_eq_rpow, hHs, hQs] at h
      rw [integral_congr_ae hfactor, hHint] at h
      exact h
    have hnorm : ‖weightedRadialAverage f n r‖ ≤ √C * √(∫ t, Q (r, t) ∂τ) := by
      rw [weightedRadialAverage, intervalIntegral.integral_of_le zero_le_one]
      refine (norm_integral_le_of_norm_le hprod ?_).trans hcs
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul, norm_pow, Real.norm_of_nonneg ht.1.le, Real.norm_eq_abs]
    calc
      _ = ‖weightedRadialAverage f n r‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      _ ≤ (√C * √(∫ t, Q (r, t) ∂τ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = _ := by
        rw [mul_pow, Real.sq_sqrt hC, Real.sq_sqrt (integral_nonneg fun t ↦ hQ0 (r, t))]
  have hgm : AEStronglyMeasurable (weightedRadialAverage f n) ν :=
    (continuous_weightedRadialAverage hcont n).aestronglyMeasurable
  have hgi : Integrable (fun r ↦ weightedRadialAverage f n r ^ 2) ν :=
    (hQi.integral_prod_left.const_mul C).mono_nonneg (hgm.pow 2)
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _) hpoint
  have hg : MemLp (weightedRadialAverage f n) 2 ν :=
    (memLp_two_iff_integrable_sq hgm).2 hgi
  have hint : (∫ r, weightedRadialAverage f n r ^ 2 ∂ν) ≤
      C ^ 2 * (∫ r, f r ^ 2 ∂ν) := by
    calc
      _ ≤ ∫ r, C * (∫ t, Q (r, t) ∂τ) ∂ν :=
        integral_mono_ae hgi (hQi.integral_prod_left.const_mul C) hpoint
      _ = C * (∫ p, Q p ∂ν.prod τ) := by
        rw [integral_const_mul, ← integral_prod Q hQi]
      _ = _ := by rw [hQtotal]; cas
  refine ⟨hg, ?_⟩
  apply (sq_le_sq₀ lpNorm_nonneg (mul_nonneg hC lpNorm_nonneg)).1
  rw [mul_pow, ← hg.integral_sq_eq_lpNorm_sq,
    ← hf.integral_sq_eq_lpNorm_sq]
  exact hint

/-- Moving toward the axis loses at most `t^q` in the square root of the
weight `(1+r²+z²)^q`. The comparison also holds at the axis endpoint `t=0`. -/
theorem pow_mul_sqrt_one_add_sq_add_sq_pow_le (q : ℕ) (r z : ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t ^ q * √(1 + r ^ 2 + z ^ 2) ^ q ≤
      √(1 + (t * r) ^ 2 + z ^ 2) ^ q := by
  have hscale : t ^ 2 * (1 + r ^ 2 + z ^ 2) ≤ 1 + (t * r) ^ 2 + z ^ 2 := by
    have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 ht.2
    have hrest := mul_le_mul_of_nonneg_right ht2 (by positivity : 0 ≤ 1 + z ^ 2)
    cas using hrest
  have hroot : t * √(1 + r ^ 2 + z ^ 2) ≤
      √(1 + (t * r) ^ 2 + z ^ 2) := by
    calc
      _ = √(t ^ 2 * (1 + r ^ 2 + z ^ 2)) := by
        rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.1]
      _ ≤ _ := Real.sqrt_le_sqrt hscale
  simpa only [mul_pow] using
    pow_le_pow_left₀ (mul_nonneg ht.1 (Real.sqrt_nonneg _)) hroot q

/-- Moving the polynomial weight inside the actual integral reduces its
averaging power by `q`, including the critical case `n=q`. -/
theorem weightedRadialAverage_one_add_polynomial_weight_le
    (n q : ℕ) (hqn : q ≤ n) {f : ℝ → ℝ} (hf : Continuous f) (r z : ℝ) :
    |weightedRadialAverage f n r| * √(1 + r ^ 2 + z ^ 2) ^ q ≤
      weightedRadialAverage
        (fun s ↦ |f s| * √(1 + s ^ 2 + z ^ 2) ^ q) (n - q) r := by
  unfold weightedRadialAverage
  refine (mul_le_mul_of_nonneg_right (intervalIntegral.abs_integral_le_integral_abs zero_le_one)
    (by positivity)).trans ?_
  rw [← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_mono_on zero_le_one (Continuous.intervalIntegrable
    (by fun_prop) 0 1) (Continuous.intervalIntegrable (by fun_prop) 0 1) fun t ht ↦ ?_
  rw [abs_mul, abs_of_nonneg (pow_nonneg ht.1 n), ← pow_sub_mul_pow t hqn]
  calc _ = t ^ (n - q) * |f (t * r)| * (t ^ q * √(1 + r ^ 2 + z ^ 2) ^ q) := by ring
    _ ≤ t ^ (n - q) * |f (t * r)| * √(1 + (t * r) ^ 2 + z ^ 2) ^ q :=
      mul_le_mul_of_nonneg_left (pow_mul_sqrt_one_add_sq_add_sq_pow_le q r z ht)
        (mul_nonneg (pow_nonneg ht.1 _) (abs_nonneg _))
    _ = _ := mul_assoc _ _ _

/-- The physical radial average acts on the polynomially weighted L² space
with constant `1/(n-q+1/2)`. At `n=q`, this is the finite constant `2`. -/
theorem weightedRadialAverage_polynomial_memLp_and_lpNorm_le_sharp
    (n q : ℕ) (hqn : q ≤ n) {f : ℝ → ℝ} (hcont : Continuous f) (z : ℝ)
    (hf : MemLp (fun r ↦ f r * √(1 + r ^ 2 + z ^ 2) ^ q)
      2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (fun r ↦ weightedRadialAverage f n r * √(1 + r ^ 2 + z ^ 2) ^ q)
        2 (volume.restrict (Ioi (0 : ℝ))) ∧
      lpNorm (fun r ↦ weightedRadialAverage f n r * √(1 + r ^ 2 + z ^ 2) ^ q)
        2 (volume.restrict (Ioi (0 : ℝ))) ≤
        (1 / ((n : ℝ) - q + 1 / 2)) *
          lpNorm (fun r ↦ f r * √(1 + r ^ 2 + z ^ 2) ^ q)
            2 (volume.restrict (Ioi (0 : ℝ))) := by
  let G : ℝ → ℝ := fun r ↦ |f r| * √(1 + r ^ 2 + z ^ 2) ^ q
  have hGcont : Continuous G := by dsimp only [G]; fun_prop
  have hG_eq : G = fun r ↦ ‖f r * √(1 + r ^ 2 + z ^ 2) ^ q‖ := by
    funext r
    simp only [G, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) q)]
  have hG : MemLp G 2 (volume.restrict (Ioi (0 : ℝ))) := hG_eq ▸ hf.norm
  have hnormG : lpNorm G 2 (volume.restrict (Ioi (0 : ℝ))) =
      lpNorm (fun r ↦ f r * √(1 + r ^ 2 + z ^ 2) ^ q)
        2 (volume.restrict (Ioi (0 : ℝ))) := by
    rw [hG_eq, lpNorm_norm hf.aestronglyMeasurable]
  obtain ⟨haverage, hnorm⟩ :=
    weightedRadialAverage_memLp_and_lpNorm_le_sharp (n - q) hGcont hG
  have hdom (r : ℝ) :
      ‖weightedRadialAverage f n r * √(1 + r ^ 2 + z ^ 2) ^ q‖ ≤
        weightedRadialAverage G (n - q) r := by
    simpa only [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) q), G] using
      weightedRadialAverage_one_add_polynomial_weight_le n q hqn hcont r z
  refine ⟨haverage.mono' ((continuous_weightedRadialAverage hcont n).mul
    (by fun_prop)).aestronglyMeasurable (.of_forall hdom), ?_⟩
  calc
    _ ≤ lpNorm (weightedRadialAverage G (n - q)) 2 (volume.restrict (Ioi (0 : ℝ))) :=
      lpNorm_mono_real haverage hdom
    _ ≤ _ := by simpa only [hnormG, Nat.cast_sub hqn] using hnorm

/-- The sharp polynomially weighted bound is unchanged by integration in
the axial variable. This is the `dr dz` form used by physical profiles.
The same source supplies the almost-everywhere radial slices through Fubini. -/
theorem weightedRadialAverage_polynomial_prod_memLp_and_lpNorm_le_sharp
    (n q : ℕ) (hqn : q ≤ n) {f : ℝ × ℝ → ℝ} (hcont : Continuous f)
    (hf : MemLp (fun p : ℝ × ℝ ↦
      f p * √(1 + p.1 ^ 2 + p.2 ^ 2) ^ q)
      2 ((volume.restrict (Ioi (0 : ℝ))).prod volume)) :
    MemLp (fun p : ℝ × ℝ ↦
      weightedRadialAverage (fun r ↦ f (r, p.2)) n p.1 *
        √(1 + p.1 ^ 2 + p.2 ^ 2) ^ q)
      2 ((volume.restrict (Ioi (0 : ℝ))).prod volume) ∧
    lpNorm (fun p : ℝ × ℝ ↦
      weightedRadialAverage (fun r ↦ f (r, p.2)) n p.1 *
        √(1 + p.1 ^ 2 + p.2 ^ 2) ^ q)
      2 ((volume.restrict (Ioi (0 : ℝ))).prod volume) ≤
      (1 / ((n : ℝ) - q + 1 / 2)) *
        lpNorm (fun p : ℝ × ℝ ↦
          f p * √(1 + p.1 ^ 2 + p.2 ^ 2) ^ q)
          2 ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let C : ℝ := 1 / ((n : ℝ) - q + 1 / 2)
  let F : ℝ × ℝ → ℝ := fun p ↦
    f p * √(1 + p.1 ^ 2 + p.2 ^ 2) ^ q
  let g : ℝ × ℝ → ℝ := fun p ↦
    weightedRadialAverage (fun r ↦ f (r, p.2)) n p.1 *
      √(1 + p.1 ^ 2 + p.2 ^ 2) ^ q
  have hdiff : 0 ≤ (n : ℝ) - q := sub_nonneg.mpr (Nat.cast_le.mpr hqn)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hFcont : Continuous F := by dsimp only [F]; fun_prop
  have hgm : AEStronglyMeasurable g (ν.prod volume) :=
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (p : ℝ × ℝ) (t : ℝ) ↦ t ^ n * f (t * p.1, p.2)) (by fun_prop) 0 1).mul
      (by fun_prop : Continuous fun p : ℝ × ℝ ↦
        √(1 + p.1 ^ 2 + p.2 ^ 2) ^ q)).aestronglyMeasurable
  have hslices : ∀ᵐ z ∂(volume : Measure ℝ),
      Integrable (fun r ↦ g (r, z) ^ 2) ν ∧
        (∫ r, g (r, z) ^ 2 ∂ν) ≤ C ^ 2 * (∫ r, F (r, z) ^ 2 ∂ν) := by
    filter_upwards [hf.integrable_sq.prod_left_ae] with z hz
    have hfz : MemLp (fun r ↦ F (r, z)) 2 ν :=
      (memLp_two_iff_integrable_sq
        (hFcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable).2 hz
    obtain ⟨hgz, hnorm⟩ :=
      weightedRadialAverage_polynomial_memLp_and_lpNorm_le_sharp n q hqn
        (f := fun r ↦ f (r, z))
        (hcont.comp (continuous_id.prodMk continuous_const)) z hfz
    change MemLp (fun r ↦ g (r, z)) 2 ν at hgz
    change lpNorm (fun r ↦ g (r, z)) 2 ν ≤
      C * lpNorm (fun r ↦ F (r, z)) 2 ν at hnorm
    refine ⟨hgz.integrable_sq, ?_⟩
    rw [hgz.integral_sq_eq_lpNorm_sq, hfz.integral_sq_eq_lpNorm_sq]
    exact (pow_le_pow_left₀ lpNorm_nonneg hnorm 2).trans_eq (mul_pow _ _ _)
  have houter : Integrable (fun z ↦ ∫ r, g (r, z) ^ 2 ∂ν) :=
    (hf.integrable_sq.integral_prod_right.const_mul (C ^ 2)).mono_nonneg
      (hgm.pow 2).prod_swap.integral_prod_right'
      (Filter.Eventually.of_forall fun z ↦ integral_nonneg fun r ↦ sq_nonneg (g (r, z)))
      (hslices.mono fun _ h ↦ h.2)
  have hgi : Integrable (fun p ↦ g p ^ 2) (ν.prod volume) := by
    apply (integrable_prod_iff' (hgm.pow 2)).2
    refine ⟨hslices.mono fun _ h ↦ h.1, ?_⟩
    simpa only [Real.norm_eq_abs, Pi.pow_apply, abs_pow, sq_abs] using houter
  have hg : MemLp g 2 (ν.prod volume) := (memLp_two_iff_integrable_sq hgm).2 hgi
  have hint : (∫ p, g p ^ 2 ∂ν.prod volume) ≤
      C ^ 2 * (∫ p, F p ^ 2 ∂ν.prod volume) := by
    calc
      _ = ∫ z, ∫ r, g (r, z) ^ 2 ∂ν := integral_prod_symm _ hgi
      _ ≤ ∫ z, C ^ 2 * (∫ r, F (r, z) ^ 2 ∂ν) :=
        integral_mono_ae houter (hf.integrable_sq.integral_prod_right.const_mul (C ^ 2))
          (hslices.mono fun _ h ↦ h.2)
      _ = _ := by rw [integral_const_mul, ← integral_prod_symm _ hf.integrable_sq]
  refine ⟨hg, ?_⟩
  apply (sq_le_sq₀ lpNorm_nonneg (mul_nonneg hC lpNorm_nonneg)).1
  rw [mul_pow, ← hg.integral_sq_eq_lpNorm_sq,
    ← hf.integral_sq_eq_lpNorm_sq]
  exact hint

end PDE.Calculus
