/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.FDeriv.PartialDeriv.Energy
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.IncrementIntegral
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.NormalKernel
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.TangentialKernel

/-!
# The fractional trace estimate for smooth half-space functions

The boundary difference is split at height equal to the tangential distance.
Hardy's inequality controls the two normal increments; the translation estimate
controls the tangential increment after integration over its base point.
The coordinate estimate includes the finite-dimensional operator-norm bound.
All estimates allow an arbitrary real Banach codomain; the constants depend
only on the dimension of the domain and the exponent.
-/

@[expose] public section

open PDE (partialDeriv)

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℝ^(n + 1) → F}

private theorem lintegral_normal_kernel_le_fderiv (hn : 1 ≤ n)
    {p : ℝ} (hp : 1 < p) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    (∫⁻ x : ℝ^n, ∫⁻ h : ℝ^n,
      ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1))) *
        ENNReal.ofReal (‖normalSlice f x ‖h‖ - smoothBoundaryValue f x‖ ^ p)) ≤
      (volume : Measure (ℝ^n)).toSphere univ * ENNReal.ofReal ((p / (p - 1)) ^ p) *
        ∫⁻ x in ℝ^(n + 1)₊, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hd : Continuous (∂[Fin.last n] f) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc : HasCompactSupport (∂[Fin.last n] f) := hfc.fderiv_apply ℝ _
  have hi : Integrable (fun x ↦ ‖(∂[Fin.last n] f) x‖ ^ p)
      (volume.restrict (ℝ^(n + 1)₊)) :=
    (hd.norm.rpow_const (fun _ ↦ Or.inr hp0.le)).integrable_of_hasCompactSupport
      (hc.norm.rpow_const hp0.ne')
  have heq := ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
  calc
    _ ≤ (volume : Measure (ℝ^n)).toSphere univ *
        ENNReal.ofReal ((p / (p - 1)) ^ p *
          ∫ x in ℝ^(n + 1)₊, ‖(∂[Fin.last n] f) x‖ ^ p) :=
      lintegral_normal_kernel_le hn hp hf hfc
    _ = (volume : Measure (ℝ^n)).toSphere univ * ENNReal.ofReal ((p / (p - 1)) ^ p) *
        ∫⁻ x in ℝ^(n + 1)₊, ENNReal.ofReal (‖(∂[Fin.last n] f) x‖ ^ p) := by
      rw [ENNReal.ofReal_mul (by positivity), heq, mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow (norm_nonneg _) _ hp0.le
      simpa [partialDeriv] using
        (fderiv ℝ f x).le_opNorm (EuclideanSpace.single (Fin.last n) (1 : ℝ))

omit [CompleteSpace F] in
private theorem lintegral_fderiv_rpow_le_coordinate_energy
    {p : ℝ} (hp : 1 ≤ p) (hf : ContDiff ℝ 1 f) :
    (∫⁻ x in ℝ^(n + 1)₊, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ p)) ≤
      ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (p - 1)) * ∑ i : Fin (n + 1),
        ∫⁻ x in ℝ^(n + 1)₊, ‖(∂[i] f) x‖ₑ ^ p := by
  have hd (i : Fin (n + 1)) : Continuous (∂[i] f) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  calc
    _ ≤ ∫⁻ x in ℝ^(n + 1)₊, ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (p - 1)) *
        ∑ i : Fin (n + 1), ‖(∂[i] f) x‖ₑ ^ p := by
      apply lintegral_mono
      intro x
      have hb := ENNReal.ofReal_le_ofReal
        (PDE.norm_fderiv_rpow_le_sum_norm_partialDeriv_rpow f x hp)
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
        (fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)] at hb
      simpa only [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (zero_le_one.trans hp),
        ofReal_norm] using hb
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      exact lintegral_finsetSum _ (fun i _ ↦ ((hd i).enorm.measurable.pow_const p))

/-- The full smooth fractional trace estimate in positive boundary dimension.
The coefficient is `3^(p-1) Sₙ (2H+1)`, where `H = (p/(p-1))^p` and `Sₙ` is
the angular mass of the unit sphere. The derivative is measured in operator norm. -/
theorem lintegral_smoothBoundaryValue_pair_le_fderiv (hn : 1 ≤ n)
    {p : ℝ} (hp : 1 < p) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    (∫⁻ x : ℝ^n, ∫⁻ y : ℝ^n,
      ENNReal.ofReal (‖x - y‖ ^ (-((n : ℝ) + p - 1))) *
        ENNReal.ofReal (‖smoothBoundaryValue f x - smoothBoundaryValue f y‖ ^ p)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) * (volume : Measure (ℝ^n)).toSphere univ *
        ENNReal.ofReal (2 * (p / (p - 1)) ^ p + 1) *
          ∫⁻ x in ℝ^(n + 1)₊, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ p) := by
  have hnormal := lintegral_normal_kernel_le_fderiv hn hp hf hfc
  have htangent := lintegral_tangential_increment_kernel_le
    (zero_lt_one.trans_le hn) hp.le hf hfc
  calc
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) *
        (2 * (∫⁻ x : ℝ^n, ∫⁻ h : ℝ^n,
            ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1))) *
              ENNReal.ofReal (‖normalSlice f x ‖h‖ - smoothBoundaryValue f x‖ ^ p)) +
          ∫⁻ h : ℝ^n, ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1))) *
            ∫⁻ x : ℝ^n, ENNReal.ofReal
              (‖normalSlice f (x + h) ‖h‖ - normalSlice f x ‖h‖‖ ^ p)) :=
      lintegral_smoothBoundaryValue_pair_le_normal_tangential hf.continuous hp.le
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) *
        (2 * ((volume : Measure (ℝ^n)).toSphere univ *
            ENNReal.ofReal ((p / (p - 1)) ^ p) *
              ∫⁻ x in ℝ^(n + 1)₊, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ p)) +
          (volume : Measure (ℝ^n)).toSphere univ *
            ∫⁻ x in ℝ^(n + 1)₊, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ p)) :=
      mul_le_mul_right (add_le_add (mul_le_mul_right hnormal 2) htangent) _
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat, ENNReal.ofReal_one]
      ring

/-- The smooth trace bound in the product-measure quotient form, with the sum of
coordinate partial energies. Passing from operator norm to coordinates contributes
`(n+1)^(p-1)`; no dimension-free gradient identity is used. -/
theorem lintegral_smoothBoundaryValue_enorm_div_le_coordinate_energy (hn : 1 ≤ n)
    {p : ℝ} (hp : 1 < p) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    (∫⁻ z : ℝ^n × ℝ^n,
      ‖smoothBoundaryValue f z.1 - smoothBoundaryValue f z.2‖ₑ ^ p /
        (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
      ∂((volume : Measure (ℝ^n)).prod volume)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) * (volume : Measure (ℝ^n)).toSphere univ *
        ENNReal.ofReal (2 * (p / (p - 1)) ^ p + 1) *
        ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (p - 1)) * ∑ i : Fin (n + 1),
          ∫⁻ x in ℝ^(n + 1)₊, ‖(∂[i] f) x‖ₑ ^ p := by
  rw [lintegral_smoothBoundaryValue_enorm_div_eq_pair hf.continuous (zero_lt_one.trans hp)]
  apply (lintegral_smoothBoundaryValue_pair_le_fderiv hn hp hf hfc).trans
  simpa only [mul_assoc] using mul_le_mul_right
    (lintegral_fderiv_rpow_le_coordinate_energy hp.le hf)
    (ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) * (volume : Measure (ℝ^n)).toSphere univ *
      ENNReal.ofReal (2 * (p / (p - 1)) ^ p + 1))

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- In boundary dimension zero every pair is diagonal, so the fractional trace
energy vanishes for every function. No polar formula is used. -/
theorem lintegral_smoothBoundaryValue_enorm_div_zero_dimensional
    (f : ℝ^(0 + 1) → F) {p : ℝ} (hp : 0 < p) :
    (∫⁻ z : ℝ^0 × ℝ^0,
      ‖smoothBoundaryValue f z.1 - smoothBoundaryValue f z.2‖ₑ ^ p /
        (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((0 : ℝ) + p - 1)
      ∂((volume : Measure (ℝ^0)).prod volume)) = 0 := by
  have hz (z : ℝ^0 × ℝ^0) : z.1 = z.2 := Subsingleton.elim _ _
  simp [hz, ENNReal.zero_rpow_of_pos hp]

/-- A finite uniform coordinate-energy bound for compactly supported C¹ functions
in every boundary dimension. In positive dimension its witness is the explicit
angular/Hardy coefficient above; in dimension zero the boundary difference vanishes. -/
theorem exists_lintegral_smoothBoundaryValue_enorm_div_le (n : ℕ)
    {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ f : ℝ^(n + 1) → F, ContDiff ℝ 1 f → HasCompactSupport f →
      (∫⁻ z : ℝ^n × ℝ^n,
        ‖smoothBoundaryValue f z.1 - smoothBoundaryValue f z.2‖ₑ ^ p /
          (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
        ∂((volume : Measure (ℝ^n)).prod volume)) ≤
      (C : ℝ≥0∞) * ∑ i : Fin (n + 1),
        ∫⁻ x in ℝ^(n + 1)₊, ‖(∂[i] f) x‖ₑ ^ p := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1, fun f _ _ ↦ ?_⟩
    simp only [Nat.cast_zero]
    rw [lintegral_smoothBoundaryValue_enorm_div_zero_dimensional f (zero_lt_one.trans hp)]
    exact bot_le
  · refine ⟨Real.toNNReal ((3 : ℝ) ^ (p - 1)) *
      ((volume : Measure (ℝ^n)).toSphere univ).toNNReal *
      Real.toNNReal (2 * (p / (p - 1)) ^ p + 1) *
      Real.toNNReal (((n + 1 : ℕ) : ℝ) ^ (p - 1)), ?_⟩
    intro f hf hfc
    simpa only [ENNReal.coe_mul, ENNReal.coe_toNNReal (measure_ne_top _ _),
      ENNReal.ofReal] using
        lintegral_smoothBoundaryValue_enorm_div_le_coordinate_energy
          (Nat.one_le_iff_ne_zero.mpr hn) hp hf hfc

end SobolevSpace.Trace.HalfSpace
