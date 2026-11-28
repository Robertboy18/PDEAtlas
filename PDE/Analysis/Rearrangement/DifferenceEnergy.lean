/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import PDE.Analysis.Rearrangement.Polarization
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.Normalize
import PDE.Analysis.MeasureTheory.Integral.Substitution

/-!
# The Dirichlet integral as a limit of difference energies

Polarization does not increase the difference energies
`∬_{|x - y| ≤ t} j (w x - w y) dx dy` (`diffEnergy`, `diffEnergy_polarize_le`), and they see no
derivative. We show that, suitably scaled, they converge to a fixed multiple of `∫ |∇w|^p` as
`t → 0`, for a Lipschitz function `w` with compact support. This is how the Pólya–Szegő
inequality `exists_radial_lintegral_fderiv_le` reaches the Dirichlet integral. The constant is
`∫_{|z| ≤ 1} |z₁|^p dz`; we do not compute it, since only its positivity and finiteness are
used. Functions without compact support are not treated.

## Main results

* `diffEnergy_eq_smul`: the difference energy in the variables `(x, z)`, `y = x + t z`, for
  measurable `j` and `w` and every `t > 0`.
* `exists_lintegral_closedBall_abs_rpow_eq`: on a finite-dimensional real inner product space
  and for `p > 0`, there is one constant `0 < c < ∞` with `∫_{|z| ≤ 1} |ℓ z|^p dz = c ‖ℓ‖^p` for
  every continuous linear functional `ℓ`.
* `tendsto_lintegral_diffQuotient`: for a Lipschitz `w` that vanishes outside a ball and
  `p > 0`, the scaled difference energies converge to `∫ ∫_{|z| ≤ 1} |∇w(x) · z|^p dz dx`.

## How it works

Take the cost `j(s) = |c s|^p` at the scale `t = 1 / c`. The substitution `y = x + t z`
(`MeasureTheory.Measure.lintegral_comp_add_smul`) turns the difference energy into `tⁿ` times

`∫ ∫_{|z| ≤ 1} |c (w(x) - w(x + z / c))|^p dz dx`,

the integral of the `p`-th power of a difference quotient over the unit ball of directions.
The difference quotients are bounded by the Lipschitz constant and vanish for `x` outside a
fixed ball. By Rademacher's theorem (`LipschitzWith.ae_differentiableAt`) they converge to
`∇w(x) · z` for almost every `x` and every `z`. Dominated convergence, first in `z` and then in
`x`, gives the limit `∫ ∫_{|z| ≤ 1} |∇w(x) · z|^p dz dx`. The inner integral is the same for
all vectors `∇w(x)` of one length, because a reflection (`Submodule.reflection_sub`) maps any
unit vector to any other and preserves the ball and the volume. So it equals `c_p |∇w(x)|^p`.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Graduate Studies in Mathematics 14, American
  Mathematical Society, 2001, Chapter 7: the gradient energy as a limit of energies without
  derivatives, which rearrangement does not increase. <https://doi.org/10.1090/gsm/014>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Metric Function Module
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace PDE.Analysis.Rearrangement

/-! ## The difference energy in scaled variables -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

/-- **The difference energy in the variables `(x, z)`, `y = x + t z`.** It is `tⁿ` times the
integral of `j (w x - w (x + t z))` over `x` in the space and `z` in the closed unit ball. -/
theorem diffEnergy_eq_smul {j : ℝ → ℝ} (hj : Measurable j) {t : ℝ} (ht : 0 < t) {w : E → ℝ}
    (hw : Measurable w) :
    diffEnergy j t w = ENNReal.ofReal (t ^ finrank ℝ E) *
      ∫⁻ x, ∫⁻ z in closedBall (0 : E) 1, ENNReal.ofReal (j (w x - w (x + t • z))) := by
  rw [diffEnergy, lintegral_prod _ (measurable_diffEnergy_integrand hj t hw).aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x ↦ ?_
  have htn : 0 < t ^ finrank ℝ E := pow_pos ht _
  have hcv : ∫⁻ y, nearWeight t x y * ENNReal.ofReal (j (w x - w y)) =
      ENNReal.ofReal (t ^ finrank ℝ E) *
        ∫⁻ z, nearWeight t x (x + t • z) * ENNReal.ofReal (j (w x - w (x + t • z))) := by
    rw [Measure.lintegral_comp_add_smul volume
        (fun y ↦ nearWeight t x y * ENNReal.ofReal (j (w x - w y))) x ht.ne', ← mul_assoc,
      ← ENNReal.ofReal_mul htn.le, abs_of_pos (inv_pos.mpr htn), mul_inv_cancel₀ htn.ne',
      ENNReal.ofReal_one, one_mul]
  rw [hcv, ← lintegral_indicator measurableSet_closedBall]
  congr 1
  refine lintegral_congr fun z ↦ ?_
  have hd : dist x (x + t • z) ≤ t ↔ z ∈ closedBall (0 : E) 1 := by
    have e : dist x (x + t • z) = t * ‖z‖ := by
      simp [dist_eq_norm, norm_smul, abs_of_pos ht]
    rw [e, mem_closedBall_zero_iff]
    exact mul_le_iff_le_one_right ht
  by_cases hz : z ∈ closedBall (0 : E) 1
  · rw [indicator_of_mem hz, nearWeight, ite_eq_left (hd.mpr hz), one_mul]
  · rw [indicator_of_notMem hz, nearWeight, ite_eq_right (mt hd.mp hz), zero_mul]

/-! ## The moment of a linear functional over the unit ball -/

/-- **Rotation invariance.** On a finite-dimensional real inner product space and for `p > 0`
there is a constant `0 < c < ∞` with `∫_{|z| ≤ 1} |ℓ z|^p dz = c ‖ℓ‖^p` for every continuous
linear functional `ℓ`. The functional is `z ↦ ⟪g, z⟫`, and a reflection maps `g / |g|` to a
fixed unit vector. In dimension zero every functional is zero and `c = 1` works. -/
theorem exists_lintegral_closedBall_abs_rpow_eq {p : ℝ} (hp : 0 < p) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ ℓ : E →L[ℝ] ℝ,
      ∫⁻ z in closedBall (0 : E) 1, ENNReal.ofReal (|ℓ z| ^ p) =
        c * ENNReal.ofReal (‖ℓ‖ ^ p) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨1, one_ne_zero, ENNReal.one_ne_top, fun ℓ ↦ ?_⟩
    obtain rfl : ℓ = 0 := Subsingleton.elim _ _
    simp [Real.zero_rpow hp.ne']
  obtain ⟨e₀, he₀⟩ := exists_norm_eq E zero_le_one
  set f₀ : E → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (|⟪e₀, z⟫| ^ p) with hf₀
  have hf₀m : Measurable f₀ :=
    (ENNReal.continuous_ofReal.comp
      ((continuous_const.inner continuous_id).abs.rpow_const fun _ ↦ Or.inr hp.le)).measurable
  refine ⟨∫⁻ z in closedBall (0 : E) 1, f₀ z, ?_, ?_, fun ℓ ↦ ?_⟩
  · -- the integrand is at least `(1/4)^p` on the ball of radius `1/4` around `e₀ / 2`
    have hsub : ball ((2⁻¹ : ℝ) • e₀) 4⁻¹ ⊆ closedBall (0 : E) 1 := fun z hz ↦ by
      have hz' : ‖z - (2⁻¹ : ℝ) • e₀‖ < 4⁻¹ := mem_ball_iff_norm.mp hz
      have h2 : ‖(2⁻¹ : ℝ) • e₀‖ = 2⁻¹ := by rw [norm_smul, he₀]; norm_num
      have := norm_add_le (z - (2⁻¹ : ℝ) • e₀) ((2⁻¹ : ℝ) • e₀)
      rw [sub_add_cancel, h2] at this
      rw [mem_closedBall_zero_iff]
      linarith
    have hlow : ∀ z ∈ ball ((2⁻¹ : ℝ) • e₀) 4⁻¹, ENNReal.ofReal ((4⁻¹ : ℝ) ^ p) ≤ f₀ z := by
      intro z hz
      have hz' : ‖z - (2⁻¹ : ℝ) • e₀‖ < 4⁻¹ := mem_ball_iff_norm.mp hz
      have h1 : ⟪e₀, z⟫ = ⟪e₀, z - (2⁻¹ : ℝ) • e₀⟫ + 2⁻¹ := by
        rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he₀]
        ring
      have h2 : |⟪e₀, z - (2⁻¹ : ℝ) • e₀⟫| ≤ 4⁻¹ :=
        (abs_real_inner_le_norm _ _).trans (by rw [he₀, one_mul]; exact hz'.le)
      have h3 : (4⁻¹ : ℝ) ≤ |⟪e₀, z⟫| := by
        rw [h1]
        have := abs_le.mp h2
        exact le_trans (by linarith) (le_abs_self _)
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by norm_num) h3 hp.le)
    have hpos : 0 < ENNReal.ofReal ((4⁻¹ : ℝ) ^ p) * volume (ball ((2⁻¹ : ℝ) • e₀) 4⁻¹) :=
      ENNReal.mul_pos (by simpa using Real.rpow_pos_of_pos (by norm_num) p)
        (measure_ball_pos volume _ (by norm_num)).ne'
    refine (hpos.trans_le ?_).ne'
    calc ENNReal.ofReal ((4⁻¹ : ℝ) ^ p) * volume (ball ((2⁻¹ : ℝ) • e₀) 4⁻¹)
        = ∫⁻ _ in ball ((2⁻¹ : ℝ) • e₀) 4⁻¹, ENNReal.ofReal ((4⁻¹ : ℝ) ^ p) :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ z in ball ((2⁻¹ : ℝ) • e₀) 4⁻¹, f₀ z := setLIntegral_mono hf₀m hlow
      _ ≤ ∫⁻ z in closedBall (0 : E) 1, f₀ z := lintegral_mono_set hsub
  · -- the integrand is at most `1` on the unit ball
    have hle : ∀ z ∈ closedBall (0 : E) 1, f₀ z ≤ 1 := fun z hz ↦ by
      have h1 : |⟪e₀, z⟫| ≤ 1 :=
        (abs_real_inner_le_norm _ _).trans
          (by rw [he₀, one_mul]; exact mem_closedBall_zero_iff.mp hz)
      rw [hf₀, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one (abs_nonneg _) h1 hp.le)
    refine ((setLIntegral_mono measurable_const hle).trans_lt ?_).ne
    rw [setLIntegral_const, one_mul]
    exact measure_closedBall_lt_top
  · set g : E := (InnerProductSpace.toDual ℝ E).symm ℓ with hg
    have hℓ (z : E) : ℓ z = ⟪g, z⟫ := InnerProductSpace.toDual_symm_apply.symm
    have hgn : ‖g‖ = ‖ℓ‖ := LinearIsometryEquiv.norm_map _ _
    rcases eq_or_ne g 0 with h0 | h0
    · have hz : ∀ z, ENNReal.ofReal (|ℓ z| ^ p) = 0 := fun z ↦ by
        rw [hℓ, h0, inner_zero_left, abs_zero, Real.zero_rpow hp.ne', ENNReal.ofReal_zero]
      rw [← hgn, h0, norm_zero, Real.zero_rpow hp.ne', ENNReal.ofReal_zero, mul_zero]
      simp [hz]
    · have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr h0
      have hunit : ‖NormedSpace.normalize g‖ = ‖e₀‖ := by
        rw [NormedSpace.norm_normalize h0, he₀]
      set ρ : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (NormedSpace.normalize g - e₀))ᗮ.reflection with hρ
      have hρg : ρ (NormedSpace.normalize g) = e₀ := Submodule.reflection_sub hunit
      have hpt (z : E) : ENNReal.ofReal (|ℓ z| ^ p) = ENNReal.ofReal (‖g‖ ^ p) * f₀ (ρ z) := by
        have e1 : ⟪g, z⟫ = ‖g‖ * ⟪e₀, ρ z⟫ := by
          rw [← hρg, ρ.inner_map_map, ← real_inner_smul_left, NormedSpace.norm_smul_normalize]
        rw [hℓ, e1, abs_mul, abs_of_pos hgpos, Real.mul_rpow hgpos.le (abs_nonneg _),
          ENNReal.ofReal_mul (by positivity)]
      have hpre : ρ ⁻¹' closedBall (0 : E) 1 = closedBall (0 : E) 1 := by
        ext z
        simp
      have hcomp : ∫⁻ z in closedBall (0 : E) 1, f₀ (ρ z) = ∫⁻ z in closedBall (0 : E) 1, f₀ z := by
        have := ρ.measurePreserving.setLIntegral_comp_preimage
          (measurableSet_closedBall (x := (0 : E)) (ε := 1)) hf₀m
        rwa [hpre] at this
      simp only [hpt]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hcomp, hgn, mul_comm]

/-! ## The limit of the difference quotients -/

/-- **The scaled difference energies converge.** Let `w` be Lipschitz and zero outside a ball,
and `p > 0`. The integrals over `x` in the space and `z` in the unit ball of the `p`-th power
of the difference quotient `(k + 1) (w x - w (x + z / (k + 1)))` converge, as `k → ∞`, to the
integral of `|∇w(x) · z|^p`. The proof is dominated convergence in `z` and then in `x`, with
Rademacher's theorem for the pointwise limit. -/
theorem tendsto_lintegral_diffQuotient {L : ℝ≥0} {R : ℝ} {w : E → ℝ} (hw : LipschitzWith L w)
    (hR : ∀ x, R < ‖x‖ → w x = 0) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun k : ℕ ↦ ∫⁻ x, ∫⁻ z in closedBall (0 : E) 1,
        ENNReal.ofReal (|((k : ℝ) + 1) * (w x - w (x + ((k : ℝ) + 1)⁻¹ • z))| ^ p)) atTop
      (𝓝 (∫⁻ x, ∫⁻ z in closedBall (0 : E) 1, ENNReal.ofReal (|fderiv ℝ w x z| ^ p))) := by
  have hwc : Continuous w := hw.continuous
  have hck (k : ℕ) : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hck1 (k : ℕ) : (1 : ℝ) ≤ (k : ℝ) + 1 := by simp
  have hc : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
  have hφ : Continuous fun s : ℝ ↦ ENNReal.ofReal (|s| ^ p) :=
    ENNReal.continuous_ofReal.comp (continuous_abs.rpow_const fun _ ↦ Or.inr hp.le)
  -- the integrand, jointly measurable in `(x, z)`
  have hFm (k : ℕ) : Measurable fun q : E × E ↦
      ENNReal.ofReal (|((k : ℝ) + 1) * (w q.1 - w (q.1 + ((k : ℝ) + 1)⁻¹ • q.2))| ^ p) :=
    (hφ.comp (continuous_const.mul ((hwc.comp continuous_fst).sub
      (hwc.comp (continuous_fst.add (continuous_snd.const_smul _)))))).measurable
  -- the difference quotients are bounded by the Lipschitz constant on the unit ball
  have hbd (k : ℕ) (x : E) {z : E} (hz : z ∈ closedBall (0 : E) 1) :
      ENNReal.ofReal (|((k : ℝ) + 1) * (w x - w (x + ((k : ℝ) + 1)⁻¹ • z))| ^ p) ≤
        ENNReal.ofReal ((L : ℝ) ^ p) := by
    have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have h1 := hw.dist_le_mul x (x + ((k : ℝ) + 1)⁻¹ • z)
    have e : dist x (x + ((k : ℝ) + 1)⁻¹ • z) = ((k : ℝ) + 1)⁻¹ * ‖z‖ := by
      simp [dist_eq_norm, norm_smul, abs_of_pos (hck k)]
    rw [Real.dist_eq, e] at h1
    have h2 : |((k : ℝ) + 1) * (w x - w (x + ((k : ℝ) + 1)⁻¹ • z))| ≤ L :=
      calc |((k : ℝ) + 1) * (w x - w (x + ((k : ℝ) + 1)⁻¹ • z))|
          = ((k : ℝ) + 1) * |w x - w (x + ((k : ℝ) + 1)⁻¹ • z)| := by
            rw [abs_mul, abs_of_pos (hck k)]
        _ ≤ ((k : ℝ) + 1) * (L * (((k : ℝ) + 1)⁻¹ * ‖z‖)) :=
            mul_le_mul_of_nonneg_left h1 (hck k).le
        _ = L * ‖z‖ := by
            field_simp
        _ ≤ L * 1 := mul_le_mul_of_nonneg_left hz1 L.coe_nonneg
        _ = L := mul_one _
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) h2 hp.le)
  -- they vanish for `x` outside the ball of radius `R + 1`
  have hvan (k : ℕ) {x : E} (hx : R + 1 < ‖x‖) {z : E} (hz : z ∈ closedBall (0 : E) 1) :
      ENNReal.ofReal (|((k : ℝ) + 1) * (w x - w (x + ((k : ℝ) + 1)⁻¹ • z))| ^ p) = 0 := by
    have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have hy : ‖((k : ℝ) + 1)⁻¹ • z‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hck k)]
      calc ((k : ℝ) + 1)⁻¹ * ‖z‖ ≤ 1 * 1 :=
            mul_le_mul (inv_le_one_of_one_le₀ (hck1 k)) hz1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hxy : R < ‖x + ((k : ℝ) + 1)⁻¹ • z‖ := by
      have := norm_sub_le (x + ((k : ℝ) + 1)⁻¹ • z) (((k : ℝ) + 1)⁻¹ • z)
      rw [add_sub_cancel_right] at this
      linarith
    rw [hR x (by linarith), hR _ hxy, sub_zero, mul_zero, abs_zero, Real.zero_rpow hp.ne',
      ENNReal.ofReal_zero]
  set bound : E → ℝ≥0∞ := (closedBall (0 : E) (R + 1)).indicator
    fun _ ↦ ENNReal.ofReal ((L : ℝ) ^ p) * volume (closedBall (0 : E) 1) with hbound
  refine tendsto_lintegral_of_dominated_convergence bound
    (fun k ↦ (hFm k).lintegral_prod_right') (fun k ↦ Eventually.of_forall fun x ↦ ?_) ?_ ?_
  · -- the bound
    by_cases hx : x ∈ closedBall (0 : E) (R + 1)
    · rw [hbound, indicator_of_mem hx, ← setLIntegral_const]
      exact setLIntegral_mono measurable_const fun z hz ↦ hbd k x hz
    · have hx' : R + 1 < ‖x‖ := by simpa using hx
      rw [hbound, indicator_of_notMem hx]
      refine le_of_eq ?_
      rw [← lintegral_zero (μ := volume.restrict (closedBall (0 : E) 1))]
      exact setLIntegral_congr_fun measurableSet_closedBall fun z hz ↦ hvan k hx' hz
  · -- the bound is integrable
    rw [hbound, lintegral_indicator_const measurableSet_closedBall]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      measure_closedBall_lt_top.ne) measure_closedBall_lt_top.ne
  · -- the pointwise limit, at the points where `w` is differentiable
    filter_upwards [hw.ae_differentiableAt (μ := (volume : Measure E))] with x hx
    have hFx (k : ℕ) : Measurable fun z : E ↦
        ENNReal.ofReal (|((k : ℝ) + 1) * (w x - w (x + ((k : ℝ) + 1)⁻¹ • z))| ^ p) :=
      (hφ.comp (continuous_const.mul (continuous_const.sub
        (hwc.comp (continuous_const.add (continuous_id.const_smul _)))))).measurable
    refine tendsto_lintegral_of_dominated_convergence
      (F := fun k z ↦
        ENNReal.ofReal (|((k : ℝ) + 1) * (w x - w (x + ((k : ℝ) + 1)⁻¹ • z))| ^ p))
      (f := fun z ↦ ENNReal.ofReal (|fderiv ℝ w x z| ^ p))
      (fun _ ↦ ENNReal.ofReal ((L : ℝ) ^ p)) hFx
      (fun k ↦ ae_restrict_of_forall_mem measurableSet_closedBall fun z hz ↦ hbd k x hz) ?_
      (Eventually.of_forall fun z ↦ ?_)
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
    · have hlim := (hx.hasFDerivAt.lim_real z).comp hc
      have e (k : ℕ) : |((k : ℝ) + 1) * (w x - w (x + ((k : ℝ) + 1)⁻¹ • z))| =
          |((k : ℝ) + 1) • (w (x + ((k : ℝ) + 1)⁻¹ • z) - w x)| := by
        rw [smul_eq_mul, ← abs_neg]
        congr 1
        ring
      simp only [e]
      exact (hφ.tendsto _).comp hlim

end PDE.Analysis.Rearrangement
