/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import PDE.Analysis.Geometry.EuclideanBall
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.Global
public import PDE.Analysis.Rearrangement.PolyaSzego
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.Sharp.Bliss
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Rademacher
import PDE.Analysis.MeasureTheory.Integral.Polar
import PDE.Analysis.Calculus.Radial.NormDerivative
import PDE.Analysis.Geometry.SphereMeasure
import PDE.Analysis.MeasureTheory.Integral.IntervalOfReal

/-!
# The sharp Sobolev inequality on a Euclidean space of dimension at least three

Let `E` be a real inner product space of dimension `n ≥ 3` and `u : E → F` a Lipschitz map with
compact support into a finite-dimensional real normed space. Then

`‖u‖_{2n/(n-2)} ≤ S_n ‖∇u‖₂`,  `S_n⁻² = (n (n - 2) / 4) (4 κ σ_n)^{2/n}`,

where `σ_n` is the area of the unit sphere and `κ = ∫₀¹ s √(1 - s^{4/(n-2)}) ds`. This is the
constant of Aubin and Talenti: `sharpSobolevConstant_eq` writes it as
`(π n (n - 2))^{-1/2} (Γ(n) / Γ(n/2))^{1/n}`, and for `n = 3` it is
`K_s = 2^{2/3} / (√3 π^{2/3})`. For `C¹` maps, Mathlib's
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner` gives the same inequality with a constant
that has no value, and `eLpNorm_le_explicit_mul_eLpNorm_fderiv_pStar` gives it with the constant
`2n (n - 1) / (n - 2)`. That no constant smaller than `S_n` works is not proved here, since the
extremal functions `(1 + |x|²)^{-(n-2)/2}` do not have compact support. The exponent `2` of the
gradient is the only one treated.

## Main results

* `lintegral_rpow_le_lintegral_fderiv_sq_of_mem_lipClass`: the inequality in integral form, for
  the functions of `lipClass L R M` (Lipschitz, with values in `[0, M]`, zero outside a ball).
* `sharpSobolevConstant`, `sharpSobolevConstant_pos`: the constant `S_n`, positive for `n ≥ 3`.
* `coe_pStar`, `coe_pStar_two`: the Sobolev exponent `pStar n p` as an extended number is
  `ENNReal.ofReal (p n / (n - p))`, and `ENNReal.ofReal (2n / (n - 2))` for `p = 2`.
* `eLpNorm_le_sharpSobolevConstant_mul_eLpNorm_fderiv`: the sharp Sobolev inequality above.
  Smooth maps with compact support are a case.

## How it works

The proof has Talenti's three steps.

1. *Length.* The length `|u|` is a nonnegative Lipschitz function, and `‖∇|u|‖ ≤ ‖∇u‖` wherever
   `u` is differentiable (`PDE.norm_fderiv_norm_le`). So it is enough to treat nonnegative
   functions.
2. *Symmetrization.* The Pólya–Szegő inequality
   (`PDE.Analysis.Rearrangement.exists_radial_lintegral_fderiv_le`) replaces a nonnegative
   Lipschitz function with compact support by a radial nonincreasing one, `v(x) = φ(|x|)`,
   with the same integral of `u^p` and with `∫ ‖∇v‖² ≤ ∫ ‖∇u‖²`.
3. *One variable.* In polar coordinates (`MeasureTheory.lintegral_fun_norm_addHaar`),
   `∫ v^p = σ ∫₀^∞ r^{n-1} φ^p dr` and `∫ ‖∇v‖² ≥ σ ∫₀^∞ r^{n-1} φ'² dr`, because the radial
   derivative of `v` is `φ'` (`PDE.Analysis.Radial.abs_deriv_le_norm_fderiv_comp_norm`). Bliss's
   inequality (`bliss_inequality`) compares the two one-dimensional integrals.

With `a = (n - 2) / 2` this gives the constant `S_n` above.

## References

* G. Talenti, "Best constant in Sobolev inequality", *Ann. Mat. Pura Appl.* 110 (1976), 353-372:
  the three steps of the proof, and the constant in formula (2).
  <https://doi.org/10.1007/BF02418013>
* T. Aubin, "Problèmes isopérimétriques et espaces de Sobolev", *J. Differential Geom.* 11
  (1976), 573-598: the same constant.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Metric Module PDE.Analysis.Rearrangement
open scoped ENNReal NNReal Topology

namespace SobolevSpace.Inequalities

/-! ## Nonnegative Lipschitz functions with compact support -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

/-- **The sharp Sobolev inequality for the functions of the class**, in integral form. Let
`E` have dimension `n = 2a + 2 ≥ 3` and let `u` be Lipschitz with values in `[0, M]` and zero
outside a ball. With `p = 2 + 2/a = 2n / (n - 2)`, the area `σ` of the unit sphere and
`κ = blissKappa a`,

`a (a + 1) (4κ)^{1/(a+1)} σ^{1/(a+1)} (∫ u^p)^{a/(a+1)} ≤ ∫ ‖∇u‖²`.

The Pólya–Szegő inequality replaces `u` by a radial nonincreasing function `v(x) = φ(|x|)`,
polar coordinates turn the two integrals into `σ ∫ r^{n-1} φ^p` and at least `σ ∫ r^{n-1} φ'²`,
and Bliss's inequality compares them. -/
theorem lintegral_rpow_le_lintegral_fderiv_sq_of_mem_lipClass {L : ℝ≥0} {R M : ℝ} {u : E → ℝ}
    (hu : u ∈ lipClass L R M) {a : ℝ} (ha : 2 * a + 2 = finrank ℝ E) (hn : 3 ≤ finrank ℝ E) :
    ENNReal.ofReal (a * (a + 1) * (4 * blissKappa a) ^ (1 / (a + 1))) *
        (volume : Measure E).toSphere univ ^ (1 / (a + 1)) *
          (∫⁻ x, ENNReal.ofReal (u x ^ (2 + 2 / a))) ^ (a / (a + 1)) ≤
      ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (2 : ℝ) := by
  have hE : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have ha0 : 0 < a := by
    have h3 : (3 : ℝ) ≤ finrank ℝ E := by exact_mod_cast hn
    linarith
  set p : ℝ := 2 + 2 / a with hp
  have hp0 : 0 < p := by positivity
  set σ : ℝ≥0∞ := (volume : Measure E).toSphere univ with hσ
  -- the radial rearrangement and its profile
  obtain ⟨v, hvK, hrad, hdist, hgrad⟩ := exists_radial_lintegral_fderiv_le hu
  obtain ⟨e₀, he₀⟩ := exists_norm_eq E zero_le_one
  set φ : ℝ → ℝ := fun r ↦ v (r • e₀) with hφdef
  have hφL : LipschitzWith L φ := LipschitzWith.of_dist_le_mul fun r s ↦ by
    have h := hvK.1.dist_le_mul (r • e₀) (s • e₀)
    rwa [dist_eq_norm (r • e₀) (s • e₀), ← sub_smul, norm_smul, he₀, mul_one, Real.norm_eq_abs,
      ← Real.dist_eq] at h
  have hφ0 : ∀ r, 0 ≤ φ r := fun r ↦ (hvK.2.1 _).1
  have hvφ : ∀ x, v x = φ ‖x‖ := fun x ↦ by
    have hn' : ‖‖x‖ • e₀‖ = ‖x‖ := by rw [norm_smul, norm_norm, he₀, mul_one]
    exact le_antisymm (hrad _ _ hn'.le) (hrad _ _ hn'.ge)
  set R' : ℝ := max R 0 + 1 with hR'
  have hRR' : R < R' := lt_of_le_of_lt (le_max_left R 0) (lt_add_one _)
  have hR'0 : 0 < R' := lt_of_le_of_lt (le_max_right R 0) (lt_add_one _)
  have hφz : ∀ r, R' ≤ r → φ r = 0 := fun r hr ↦ hvK.2.2 _ (by
    rw [norm_smul, he₀, mul_one, Real.norm_eq_abs]
    exact hRR'.trans_le (hr.trans (le_abs_self r)))
  have hφd : ∀ r, R' < r → deriv φ r = 0 := fun r hr ↦ by
    have heq : φ =ᶠ[𝓝 r] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hr] with s hs using hφz s (mem_Ioi.mp hs).le
    rw [heq.deriv_eq, deriv_const]
  -- the one-dimensional inequality
  have hbliss := bliss_inequality ha0 hR'0.le hφL (fun r _ ↦ hφ0 r) (hφz R' le_rfl)
  set C : ℝ := a * (a + 1) * (4 * blissKappa a) ^ (1 / (a + 1)) with hC
  set N : ℝ := ∫ r in (0 : ℝ)..R', r ^ (2 * a + 1) * φ r ^ p with hN
  set I : ℝ := ∫ r in (0 : ℝ)..R', r ^ (2 * a + 1) * deriv φ r ^ 2 with hI
  have hN0 : 0 ≤ N :=
    intervalIntegral.integral_nonneg hR'0.le fun r hr ↦
      mul_nonneg (Real.rpow_nonneg hr.1 _) (Real.rpow_nonneg (hφ0 r) _)
  have hw (r : ℝ) : r ^ (finrank ℝ E - 1) = r ^ (2 * a + 1) := by
    rw [← Real.rpow_natCast, Nat.cast_sub (by omega), ← ha]
    congr 1
    push_cast
    ring
  have hcf : Continuous fun r : ℝ ↦ r ^ (2 * a + 1) * φ r ^ p :=
    continuous_rpow_mul_rpow (by positivity) hp0.le hφL.continuous
  -- the `L^p` side in polar coordinates
  have hA : ∫⁻ x, ENNReal.ofReal (u x ^ p) = σ * ENNReal.ofReal N := by
    have h1 := hdist (fun s ↦ |s| ^ p) (continuous_abs.rpow_const fun _ ↦ Or.inr hp0.le)
      (by simp [Real.zero_rpow hp0.ne'])
    calc ∫⁻ x, ENNReal.ofReal (u x ^ p) = ∫⁻ x, ENNReal.ofReal (|u x| ^ p) :=
          lintegral_congr fun x ↦ by rw [abs_of_nonneg (hu.2.1 x).1]
      _ = ∫⁻ x, ENNReal.ofReal (|v x| ^ p) := h1.symm
      _ = ∫⁻ x, (fun r ↦ ENNReal.ofReal (φ r ^ p)) ‖x‖ :=
          lintegral_congr fun x ↦ by rw [hvφ, abs_of_nonneg (hφ0 _)]
      _ = σ * ∫⁻ r in Ioi (0 : ℝ),
            ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * ENNReal.ofReal (φ r ^ p) :=
          lintegral_fun_norm_addHaar volume (ENNReal.continuous_ofReal.comp
            (hφL.continuous.rpow_const fun _ ↦ Or.inr hp0.le)).measurable
      _ = σ * ENNReal.ofReal N := by
          congr 1
          rw [hN, ← setLIntegral_Ioi_ofReal_eq_intervalIntegral hR'0.le
            (fun r hr ↦ mul_nonneg (Real.rpow_nonneg hr.1.le _) (Real.rpow_nonneg (hφ0 r) _))
            (fun r hr ↦ by rw [hφz r hr.le, Real.zero_rpow hp0.ne', mul_zero])
            (hcf.intervalIntegrable 0 R')]
          refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
          rw [← ENNReal.ofReal_mul (pow_nonneg (mem_Ioi.mp hr).le _), hw]
  -- the gradient side: the radial derivative is at most the gradient
  have hv' : (fun y ↦ φ ‖y‖) = v := funext fun y ↦ (hvφ y).symm
  have hB : σ * ENNReal.ofReal I ≤ ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (2 : ℝ) := by
    calc σ * ENNReal.ofReal I
        = σ * ∫⁻ r in Ioi (0 : ℝ),
            ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * ENNReal.ofReal (deriv φ r ^ 2) := by
          congr 1
          rw [hI, ← setLIntegral_Ioi_ofReal_eq_intervalIntegral hR'0.le
            (fun r hr ↦ mul_nonneg (Real.rpow_nonneg hr.1.le _) (sq_nonneg _))
            (fun r hr ↦ by rw [hφd r hr]; simp)
            (intervalIntegrable_rpow_mul_deriv_sq hφL (by positivity) 0 R')]
          refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
          rw [← ENNReal.ofReal_mul (pow_nonneg (mem_Ioi.mp hr).le _), hw]
      _ = ∫⁻ x, (fun r ↦ ENNReal.ofReal (deriv φ r ^ 2)) ‖x‖ :=
          (lintegral_fun_norm_addHaar volume
            (ENNReal.measurable_ofReal.comp ((measurable_deriv φ).pow_const 2))).symm
      _ ≤ ∫⁻ x, ‖fderiv ℝ v x‖ₑ ^ (2 : ℝ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hvK.1.ae_differentiableAt (μ := (volume : Measure E)),
            Measure.ae_ne volume (0 : E)] with x hd hx0
          have h := PDE.Analysis.Radial.abs_deriv_le_norm_fderiv_comp_norm (φ := φ) hx0
            (by rw [hv']; exact hd)
          rw [hv'] at h
          rw [← ofReal_norm (fderiv ℝ v x),
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (fderiv ℝ v x)) zero_le_two,
            Real.rpow_two, ← sq_abs (deriv φ ‖x‖)]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) h 2)
      _ ≤ ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (2 : ℝ) := hgrad 2 one_le_two
  -- combine
  have hC0 : 0 ≤ C :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (mul_nonneg (by norm_num) (blissKappa_nonneg a)) _)
  have hσσ : σ ^ (1 / (a + 1)) * σ ^ (a / (a + 1)) = σ := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
      show 1 / (a + 1) + a / (a + 1) = 1 by field_simp; ring, ENNReal.rpow_one]
  have e : ENNReal.ofReal C * σ ^ (1 / (a + 1)) *
      (σ ^ (a / (a + 1)) * ENNReal.ofReal (N ^ (a / (a + 1)))) =
      σ ^ (1 / (a + 1)) * σ ^ (a / (a + 1)) *
        (ENNReal.ofReal C * ENNReal.ofReal (N ^ (a / (a + 1)))) := by ring
  calc ENNReal.ofReal C * σ ^ (1 / (a + 1)) *
        (∫⁻ x, ENNReal.ofReal (u x ^ p)) ^ (a / (a + 1))
      = σ * ENNReal.ofReal (C * N ^ (a / (a + 1))) := by
        rw [hA, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.ofReal_rpow_of_nonneg hN0 (by positivity), e, hσσ, ← ENNReal.ofReal_mul hC0]
    _ ≤ σ * ENNReal.ofReal I := by
        gcongr
    _ ≤ ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (2 : ℝ) := hB

/-! ## Lipschitz maps with compact support -/

/-- **The constant of Aubin and Talenti in the Sobolev inequality**
`‖u‖_{2n/(n-2)} ≤ S_n ‖∇u‖₂` on `ℝⁿ`, `n ≥ 3`:

`S_n = (n (n - 2) / 4 · (4 κ σ_n)^{2/n})^{-1/2}`,

where `σ_n = PDE.Analysis.unitSphereArea n` is the area of the unit sphere of `ℝⁿ` and
`κ = blissKappa ((n - 2) / 2) = ∫₀¹ s √(1 - s^{4/(n-2)}) ds`. For `n = 3` it is
`2^{2/3} / (√3 π^{2/3})` (`sharpSobolevConstant_three`). It is the sharp constant of the
literature; that no smaller constant works is not proved here. -/
def sharpSobolevConstant (n : ℕ) : ℝ :=
  ((n : ℝ) * (n - 2) / 4 *
    (4 * blissKappa (((n : ℝ) - 2) / 2) * PDE.Analysis.unitSphereArea n) ^ ((2 : ℝ) / n)) ^
      (-(1 / 2 : ℝ))

/-- The number `n (n - 2) / 4 · (4 κ σ_n)^{2/n}`, whose power `-1/2` is `S_n`, is positive for
`n ≥ 3`. -/
private theorem sharpSobolevConstant_base_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < (n : ℝ) * (n - 2) / 4 *
      (4 * blissKappa (((n : ℝ) - 2) / 2) * PDE.Analysis.unitSphereArea n) ^ ((2 : ℝ) / n) := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have : Fact (0 < n) := ⟨by omega⟩
  have h1 : (0 : ℝ) < (n : ℝ) * (n - 2) / 4 := by
    have : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    positivity
  have h2 : (0 : ℝ) < 4 * blissKappa (((n : ℝ) - 2) / 2) * PDE.Analysis.unitSphereArea n :=
    mul_pos (mul_pos (by norm_num) (blissKappa_pos (by linarith))) PDE.Analysis.unitSphereArea_pos
  exact mul_pos h1 (Real.rpow_pos_of_pos h2 _)

/-- The constant `S_n` is positive for `n ≥ 3`. For `n ≤ 2` the definition gives `0`. -/
theorem sharpSobolevConstant_pos {n : ℕ} (hn : 3 ≤ n) : 0 < sharpSobolevConstant n :=
  Real.rpow_pos_of_pos (sharpSobolevConstant_base_pos hn) _

/-- The Sobolev exponent `pStar n p` as an extended nonnegative number is
`ENNReal.ofReal (p n / (n - p))`, for every `n` and `p`. For `p < n` this is `p n / (n - p)`;
otherwise the real number is negative or a division by zero and both sides are `0`. -/
theorem coe_pStar (n : ℕ) (p : ℝ≥0) :
    ((pStar n p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((p : ℝ) * n / (n - p)) :=
  rfl

/-- For the gradient exponent `2` the Sobolev exponent `pStar n 2` is
`ENNReal.ofReal (2 n / (n - 2))`. For `n ≥ 3` this is `2n / (n - 2)`; for `n ≤ 2` both sides
are `0`. -/
theorem coe_pStar_two (n : ℕ) :
    ((pStar n 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (2 * n / (n - 2)) := by
  rw [coe_pStar, NNReal.coe_ofNat]

/-- **The sharp Sobolev inequality** (Aubin, Talenti). Let `E` be a real inner product space
of dimension `n ≥ 3` and `u : E → F` a Lipschitz map with compact support into a
finite-dimensional real normed space. Then

`‖u‖_{2n/(n-2)} ≤ S_n ‖∇u‖₂`,  `S_n = sharpSobolevConstant n`,

where the exponent is `pStar n 2` and `‖∇u‖₂` is the `L²` norm of the operator norm of the
Fréchet derivative, which exists almost everywhere. The length `|u|` is a nonnegative Lipschitz
function with compact support and `‖∇|u|‖ ≤ ‖∇u‖` almost everywhere, so the statement follows
from the one for the functions of the class `lipClass`. That `S_n` is the smallest constant is
not proved. -/
theorem eLpNorm_le_sharpSobolevConstant_mul_eLpNorm_fderiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {u : E → F} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hc : HasCompactSupport u) (hn : 3 ≤ finrank ℝ E) :
    eLpNorm u (pStar (finrank ℝ E) 2) volume ≤
      ENNReal.ofReal (sharpSobolevConstant (finrank ℝ E)) * eLpNorm (fderiv ℝ u) 2 volume := by
  rw [coe_pStar_two]
  have hE : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have : Fact (0 < finrank ℝ E) := ⟨by omega⟩
  set n : ℕ := finrank ℝ E with hn'
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  set a : ℝ := ((n : ℝ) - 2) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha2 : 2 * a + 2 = n := by rw [ha]; ring
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have hp : 2 * (n : ℝ) / (n - 2) = 2 + 2 / a := by
    rw [ha]
    field_simp
    ring
  have hp0 : 0 < 2 + 2 / a := by positivity
  -- the length of `u` is a function of the class
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hu.continuous
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : E)
  have hwL : LipschitzWith L fun x ↦ ‖u x‖ := by
    have h := lipschitzWith_one_norm.comp hu
    rw [one_mul] at h
    exact h
  have hw : (fun x ↦ ‖u x‖) ∈ lipClass L R M :=
    ⟨hwL, fun x ↦ ⟨norm_nonneg _, hM x⟩, fun x hx ↦ by
      have hx' : x ∉ tsupport u := fun h ↦ by
        have := mem_closedBall_zero_iff.mp (hR h)
        linarith
      change ‖u x‖ = 0
      rw [image_eq_zero_of_notMem_tsupport hx', norm_zero]⟩
  have key := lintegral_rpow_le_lintegral_fderiv_sq_of_mem_lipClass hw ha2 hn
  have hkato : ∫⁻ x, ‖fderiv ℝ (fun y ↦ ‖u y‖) x‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (2 : ℝ) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hu.ae_differentiableAt (μ := (volume : Measure E))] with x h1
    rw [← ofReal_norm (fderiv ℝ (fun y ↦ ‖u y‖) x), ← ofReal_norm (fderiv ℝ u x)]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (PDE.norm_fderiv_norm_le h1)) zero_le_two
  have hA : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ (2 + 2 / a)) = ∫⁻ x, ‖u x‖ₑ ^ (2 + 2 / a) :=
    lintegral_congr fun x ↦ by
      rw [← ofReal_norm (u x), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (u x)) hp0.le]
  rw [hA] at key
  -- the constant
  have hκ := blissKappa_pos ha0
  have hσ0 : 0 < PDE.Analysis.unitSphereArea n := PDE.Analysis.unitSphereArea_pos
  set D : ℝ := (n : ℝ) * (n - 2) / 4 * (4 * blissKappa a * PDE.Analysis.unitSphereArea n) ^
    ((2 : ℝ) / n) with hD
  have hD0 : 0 < D := sharpSobolevConstant_base_pos hn
  have hconst : ENNReal.ofReal (a * (a + 1) * (4 * blissKappa a) ^ (1 / (a + 1))) *
      (volume : Measure E).toSphere univ ^ (1 / (a + 1)) = ENNReal.ofReal D := by
    have e1 : 1 / (a + 1) = (2 : ℝ) / n := by
      rw [show a + 1 = (n : ℝ) / 2 by rw [ha]; ring, one_div_div]
    have e2 : a * (a + 1) = (n : ℝ) * (n - 2) / 4 := by
      rw [ha]
      ring
    rw [PDE.Analysis.toSphere_univ_eq_ofReal_unitSphereArea,
      ENNReal.ofReal_rpow_of_nonneg hσ0.le (by positivity),
      ← ENNReal.ofReal_mul (by positivity), hD, e1, e2, mul_assoc,
      ← Real.mul_rpow (by positivity) hσ0.le]
  rw [hconst] at key
  -- from the integral form to the norms
  have hDne : ENNReal.ofReal D ≠ 0 := (ENNReal.ofReal_pos.mpr hD0).ne'
  have hle : (∫⁻ x, ‖u x‖ₑ ^ (2 + 2 / a)) ^ (a / (a + 1)) ≤
      (ENNReal.ofReal D)⁻¹ * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (2 : ℝ) := by
    calc (∫⁻ x, ‖u x‖ₑ ^ (2 + 2 / a)) ^ (a / (a + 1))
        = (ENNReal.ofReal D)⁻¹ * (ENNReal.ofReal D *
            (∫⁻ x, ‖u x‖ₑ ^ (2 + 2 / a)) ^ (a / (a + 1))) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hDne ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal D)⁻¹ * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (2 : ℝ) := by
          gcongr
          exact key.trans hkato
  have hS : ((ENNReal.ofReal D)⁻¹) ^ (1 / 2 : ℝ) = ENNReal.ofReal (sharpSobolevConstant n) := by
    rw [← ENNReal.ofReal_inv_of_pos hD0, ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hD0.le)
      (by norm_num), Real.inv_rpow hD0.le, ← Real.rpow_neg hD0.le, sharpSobolevConstant]
  have hmeas : AEStronglyMeasurable (fderiv ℝ u) (volume : Measure E) := by
    borelize (E →L[ℝ] F)
    exact (measurable_fderiv ℝ u).aestronglyMeasurable
  have hexp : a / (a + 1) * (1 / 2) = 1 / (2 + 2 / a) := by
    field_simp
  have hp' : 0 < 2 * (n : ℝ) / (n - 2) := hp ▸ hp0
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.ofReal_pos.mpr hp').ne'
      ENNReal.ofReal_ne_top hu.continuous.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hmeas,
    ENNReal.toReal_ofReal hp'.le, ENNReal.toReal_ofNat, hp, ← hS, ← hexp,
    ENNReal.rpow_mul, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  exact ENNReal.rpow_le_rpow hle (by norm_num)

end SobolevSpace.Inequalities
