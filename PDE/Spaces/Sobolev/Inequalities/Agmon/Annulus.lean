/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Average
public import PDE.Analysis.MeasureTheory.Lp.Continuous
public import PDE.Analysis.Fourier.AgmonContDiff
public import PDE.Spaces.Sobolev.Inequalities.Poincare.Annulus

/-!
# Agmon's inequality on the annulus `1 < |y| < 2`

For a `C²` function `w` with compact support on `ℝ³`, Agmon's inequality bounds `|w(x)|²` by
`‖Dw‖₂ ‖D²w‖₂`. On a bounded set it cannot hold as it stands, since a constant has no
derivative. On the annulus `A = {1 < |y| < 2}` of `ℝ³`, with all norms taken over `A` only, the
right form is

`|v(y)| ≤ C (‖v‖_{L²(A)} + ‖Dv‖_{L²(A)}^{1/2} ‖D²v‖_{L²(A)}^{1/2})`,  `y ∈ A`,

for every `C²` function `v : ℝ³ → F` with values in a real normed space. The norms are
Mathlib's `lpNorm` for Lebesgue measure restricted to `A`, with the operator norms of the
Fréchet derivatives. The constant is not explicit. Functions of `W^{2,2}(A)` that are not
restrictions of `C²` functions on `ℝ³` are not covered; they would follow by density once the
three norms are known to be continuous on `W^{2,2}(A)`.

## Main results

* `exists_lpNorm_annulusExtension_sq_le`: on a finite-dimensional real inner product space, the
  extension `annulusExtension v` of a `C²` function is bounded from `L²`, `H¹` and `H²` of the
  annulus to the same spaces on the whole space, with one constant. The first-order bound does
  not involve the second derivative.
* `exists_norm_le_unitAnnulus`: Agmon's inequality on `A` above.

## How it works

Write `a₀, a₁, a₂` for the three norms over `A` and `m` for the mean of `v` over `A`.

* The mean is small: `|m| ≤ |A|^{-1/2} a₀`.
* For `w = v - m`, Poincaré's inequality on the annulus
  (`exists_eLpNorm_sub_average_le_unitAnnulus`) gives `‖w‖_{L²(A)} ≤ C a₁`. The extension of `w`
  is bounded order by order, so the whole-space inequality
  `PDE.Analysis.Fourier.norm_sq_le_of_contDiff_two` gives `sup_A |w|² ≤ C a₁ (a₁ + a₂)`.
* The term `a₁²` is the only one of the wrong shape. If `a₁ ≤ a₂` it is at most `a₁ a₂`. If
  `a₂ < a₁`, the interpolation inequality `‖DV‖₂² ≤ 3 ‖V‖₂ ‖D²V‖₂` for the extension `V` of `v`
  (`PDE.Analysis.Fourier.lpNorm_fderiv_sq_le`) gives `a₁² ≤ C a₀ (a₀ + a₁ + a₂) ≤ C a₀ (a₀ + 2 a₁)`,
  hence `a₁ ≤ C a₀`.

So `sup_A |w|² ≤ C (a₀² + a₁ a₂)`, which is the claim for real `v`; no affine correction is
needed. A functional of norm one that attains `‖v(y)‖` gives the claim for vector-valued `v`.

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.1, Step 3 of the proof
  of Proposition 4, which uses this local form of Agmon's inequality.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

namespace PDE.Analysis

/-! ## The extension in terms of `L²` norms -/

section Extension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous function is in `Lᵖ` of the annulus `1 < |y| < 2`. -/
theorem memLp_restrict_unitAnnulus {G : Type*} [NormedAddCommGroup G] {f : E → G}
    (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p (volume.restrict (unitAnnulus E)) :=
  hf.continuousOn.memLp_of_subset_isCompact isBounded_unitAnnulus.isCompact_closure
    isOpen_unitAnnulus.measurableSet subset_closure

/-- For a `C²` function, the `L²` norms of the iterated derivatives of order `0`, `1` and `2` are
those of the function, of its derivative and of its second derivative. -/
private theorem lpNorm_iteratedFDeriv_eq {f : E → F} (hf : ContDiff ℝ 2 f) (ν : Measure E) :
    lpNorm (iteratedFDeriv ℝ 0 f) 2 ν = lpNorm f 2 ν ∧
      lpNorm (iteratedFDeriv ℝ 1 f) 2 ν = lpNorm (fderiv ℝ f) 2 ν ∧
      lpNorm (iteratedFDeriv ℝ 2 f) 2 ν = lpNorm (fderiv ℝ (fderiv ℝ f)) 2 ν := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hc (i : ℕ) (hi : (i : WithTop ℕ∞) ≤ 2) : AEStronglyMeasurable (iteratedFDeriv ℝ i f) ν :=
    (hf.continuous_iteratedFDeriv hi).aestronglyMeasurable
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae (hc 0 (by norm_num))
      hf.continuous.aestronglyMeasurable (Eventually.of_forall fun x ↦ norm_iteratedFDeriv_zero))
  · exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae (hc 1 (by norm_num))
      hf1.continuous.aestronglyMeasurable (Eventually.of_forall fun x ↦ norm_iteratedFDeriv_one f))
  · exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae (hc 2 (by norm_num))
      (hf1.continuous_fderiv one_ne_zero).aestronglyMeasurable (Eventually.of_forall fun x ↦ by
        rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]))

/-- The bound of the extension, order by order, in terms of `L²` norms. -/
private theorem exists_lpNorm_iteratedFDeriv_annulusExtension_sq_le {k : ℕ} (hk : k ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : E → F, ContDiff ℝ 2 v →
      lpNorm (iteratedFDeriv ℝ k (annulusExtension v)) 2 volume ^ 2 ≤
        C * ∑ i ∈ Finset.range (k + 1),
          lpNorm (iteratedFDeriv ℝ i v) 2 (volume.restrict (unitAnnulus E)) ^ 2 := by
  obtain ⟨C, hC⟩ := exists_lintegral_iteratedFDeriv_annulusExtension_le (E := E) (F := F) hk
  refine ⟨C, C.2, fun v hv ↦ ?_⟩
  have hk2 : (k : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
  have hcW : Continuous (iteratedFDeriv ℝ k (annulusExtension v)) :=
    (contDiff_annulusExtension hv).continuous_iteratedFDeriv hk2
  have hci (i : ℕ) (hi : i ∈ Finset.range (k + 1)) : Continuous (iteratedFDeriv ℝ i v) := by
    have hi2 : (i : WithTop ℕ∞) ≤ 2 := by
      have := Finset.mem_range.1 hi
      exact_mod_cast (by omega : i ≤ 2)
    exact hv.continuous_iteratedFDeriv hi2
  have hfin (i : ℕ) (hi : i ∈ Finset.range (k + 1)) :
      eLpNorm (iteratedFDeriv ℝ i v) 2 (volume.restrict (unitAnnulus E)) < ⊤ :=
    (memLp_restrict_unitAnnulus (hci i hi) 2).eLpNorm_lt_top
  have hsum : ∫⁻ x in unitAnnulus E, jetEnergy k v x = ∑ i ∈ Finset.range (k + 1),
      eLpNorm (iteratedFDeriv ℝ i v) 2 (volume.restrict (unitAnnulus E)) ^ 2 := by
    simp only [jetEnergy]
    rw [lintegral_finsetSum _ fun i hi ↦ (hci i hi).eNorm.measurable.pow_const 2]
    exact Finset.sum_congr rfl fun i hi ↦ (eLpNorm_two_sq (hci i hi).aestronglyMeasurable).symm
  have h := hC v hv
  rw [← eLpNorm_two_sq hcW.aestronglyMeasurable, hsum] at h
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.sum_lt_top.2 fun i hi ↦ ENNReal.pow_lt_top (hfin i hi)).ne) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_sum fun i hi ↦ (ENNReal.pow_lt_top (hfin i hi)).ne,
    ENNReal.toReal_pow] at h'
  simpa only [ENNReal.toReal_pow, ENNReal.coe_toReal, toReal_eLpNorm] using h'

/-- **The extension from the annulus is bounded on `L²`, `H¹` and `H²` at once.** There is a
constant `C` such that, for every `C²` function `v`, the extension `V = annulusExtension v`
satisfies `‖V‖² ≤ C a₀²`, `‖DV‖² ≤ C (a₀² + a₁²)` and `‖D²V‖² ≤ C (a₀² + a₁² + a₂²)`, where
`aᵢ` is the norm of `Dⁱ v` in `L²` of the annulus `1 < |y| < 2`. The first-order bound does not
involve the second derivative. -/
theorem exists_lpNorm_annulusExtension_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : E → F, ContDiff ℝ 2 v →
      lpNorm (annulusExtension v) 2 volume ^ 2 ≤
          C * lpNorm v 2 (volume.restrict (unitAnnulus E)) ^ 2 ∧
        lpNorm (fderiv ℝ (annulusExtension v)) 2 volume ^ 2 ≤
          C * (lpNorm v 2 (volume.restrict (unitAnnulus E)) ^ 2 +
            lpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus E)) ^ 2) ∧
        lpNorm (fderiv ℝ (fderiv ℝ (annulusExtension v))) 2 volume ^ 2 ≤
          C * (lpNorm v 2 (volume.restrict (unitAnnulus E)) ^ 2 +
            lpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus E)) ^ 2 +
            lpNorm (fderiv ℝ (fderiv ℝ v)) 2 (volume.restrict (unitAnnulus E)) ^ 2) := by
  obtain ⟨C₀, hC₀, h0⟩ := exists_lpNorm_iteratedFDeriv_annulusExtension_sq_le (E := E) (F := F)
    (k := 0) (by norm_num)
  obtain ⟨C₁, hC₁, h1⟩ := exists_lpNorm_iteratedFDeriv_annulusExtension_sq_le (E := E) (F := F)
    (k := 1) (by norm_num)
  obtain ⟨C₂, hC₂, h2⟩ := exists_lpNorm_iteratedFDeriv_annulusExtension_sq_le (E := E) (F := F)
    (k := 2) le_rfl
  refine ⟨C₀ + C₁ + C₂, by positivity, fun v hv ↦ ?_⟩
  obtain ⟨e0, e1, e2⟩ := lpNorm_iteratedFDeriv_eq hv (volume.restrict (unitAnnulus E))
  obtain ⟨f0, f1, f2⟩ := lpNorm_iteratedFDeriv_eq (contDiff_annulusExtension hv) volume
  have h0' := h0 v hv
  have h1' := h1 v hv
  have h2' := h2 v hv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e0, e1, e2, f0, f1, f2]
    at h0' h1' h2'
  have hx := sq_nonneg (lpNorm v 2 (volume.restrict (unitAnnulus E)))
  have hy := sq_nonneg (lpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus E)))
  have hz := sq_nonneg (lpNorm (fderiv ℝ (fderiv ℝ v)) 2 (volume.restrict (unitAnnulus E)))
  exact ⟨h0'.trans (mul_le_mul_of_nonneg_right (by linarith) hx),
    h1'.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)),
    h2'.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))⟩

end Extension

/-! ## The algebra -/

/-- The algebra behind the inequality on the annulus, for the squares `Aᵢ = aᵢ²` of the three
norms: an interpolation bound for `A₁`, a Poincaré bound for `B` and a bound for `S` by
`(B + A₁)(B + A₁ + A₂)` give `S ≤ C (A₀² + A₁ A₂)`. -/
private theorem annulus_algebra {A₀ A₁ A₂ B M P K S : ℝ} (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hA₂ : 0 ≤ A₂) (hB : 0 ≤ B) (hM : 0 ≤ M) (hP : 0 ≤ P) (hK : 0 ≤ K)
    (h1 : A₁ ^ 2 ≤ M * (A₀ * (A₀ + A₁ + A₂))) (h2 : B ≤ P * A₁)
    (h3 : S ≤ K * ((B + A₁) * (B + A₁ + A₂))) :
    S ≤ 2 * K * (P + 1) ^ 2 * (1 + 2 * M + 4 * M ^ 2) * (A₀ ^ 2 + A₁ * A₂) := by
  have h5 : B + A₁ ≤ (P + 1) * A₁ := by linarith
  have h6 : B + A₁ + A₂ ≤ (P + 1) * (A₁ + A₂) := by nlinarith [mul_nonneg hP hA₂]
  have h7 : (B + A₁) * (B + A₁ + A₂) ≤ (P + 1) * A₁ * ((P + 1) * (A₁ + A₂)) :=
    mul_le_mul h5 h6 (by positivity) (by positivity)
  have hQ0 : 0 ≤ 1 + 2 * M + 4 * M ^ 2 := by positivity
  have h12 : 0 ≤ A₁ * A₂ := mul_nonneg hA₁ hA₂
  have hQ : A₁ * (A₁ + A₂) ≤ 2 * (1 + 2 * M + 4 * M ^ 2) * (A₀ ^ 2 + A₁ * A₂) := by
    rcases le_total A₁ A₂ with h | h
    · have h8 : A₁ * (A₁ + A₂) ≤ 2 * (A₁ * A₂) := by
        nlinarith [mul_le_mul_of_nonneg_left h hA₁]
      nlinarith [sq_nonneg A₀, mul_nonneg hM h12, mul_nonneg (sq_nonneg M) h12,
        mul_nonneg hQ0 (sq_nonneg A₀)]
    · have h1' : A₁ ^ 2 ≤ M * (A₀ * (A₀ + 2 * A₁)) :=
        h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hA₀) hM)
      have hA : A₁ ^ 2 ≤ (2 * M + 4 * M ^ 2) * A₀ ^ 2 := by
        nlinarith [sq_nonneg (A₁ - 2 * M * A₀)]
      have h8 : A₁ * (A₁ + A₂) ≤ 2 * A₁ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left h hA₁]
      nlinarith [sq_nonneg A₀, mul_nonneg hQ0 h12]
  calc S ≤ K * ((B + A₁) * (B + A₁ + A₂)) := h3
    _ ≤ K * ((P + 1) * A₁ * ((P + 1) * (A₁ + A₂))) := mul_le_mul_of_nonneg_left h7 hK
    _ = K * (P + 1) ^ 2 * (A₁ * (A₁ + A₂)) := by ring
    _ ≤ K * (P + 1) ^ 2 * (2 * (1 + 2 * M + 4 * M ^ 2) * (A₀ ^ 2 + A₁ * A₂)) :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = _ := by ring

/-! ## The inequality -/

section Three

/-- The mean over the annulus is bounded by the `L²` norm over the annulus. -/
private theorem exists_abs_setAverage_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ v : ℝ^3 → ℝ, Continuous v →
      |⨍ x in unitAnnulus (ℝ^3), v x| ≤ c * lpNorm v 2 (volume.restrict (unitAnnulus (ℝ^3))) := by
  have hfinμ : IsFiniteMeasure ((volume : Measure (ℝ^3)).restrict (unitAnnulus (ℝ^3))) :=
    ⟨by simpa using isBounded_unitAnnulus.measure_lt_top⟩
  refine ⟨(volume.real (unitAnnulus (ℝ^3)))⁻¹ *
    (((volume : Measure (ℝ^3)).restrict (unitAnnulus (ℝ^3))) univ ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal,
    mul_nonneg (inv_nonneg.2 measureReal_nonneg) ENNReal.toReal_nonneg, fun v hv ↦ ?_⟩
  have h2 : |∫ x in unitAnnulus (ℝ^3), v x| ≤
      lpNorm v 1 (volume.restrict (unitAnnulus (ℝ^3))) := by
    rw [lpNorm_one_eq_integral_norm hv.aestronglyMeasurable]
    exact (Real.norm_eq_abs _).symm.trans_le (norm_integral_le_integral_norm v)
  have h3 : lpNorm v 1 (volume.restrict (unitAnnulus (ℝ^3))) ≤
      lpNorm v 2 (volume.restrict (unitAnnulus (ℝ^3))) *
        (((volume : Measure (ℝ^3)).restrict (unitAnnulus (ℝ^3))) univ ^
          (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := (volume : Measure (ℝ^3)).restrict (unitAnnulus (ℝ^3))) (p := 1) (q := 2)
      (by norm_num) hv.aestronglyMeasurable
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top
      (memLp_restrict_unitAnnulus hv 2).eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ univ))) h
    rwa [ENNReal.toReal_mul] at h'
  rw [setAverage_eq, smul_eq_mul, abs_mul, abs_inv, abs_of_nonneg measureReal_nonneg, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2.trans (h3.trans_eq (mul_comm _ _)))
    (inv_nonneg.2 measureReal_nonneg)

/-- Poincaré's inequality on the annulus of `ℝ³`, for the `L²` norms. -/
private theorem exists_lpNorm_sub_setAverage_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ^3 → ℝ, ContDiff ℝ 1 v →
      lpNorm (fun x ↦ v x - ⨍ y in unitAnnulus (ℝ^3), v y) 2
          (volume.restrict (unitAnnulus (ℝ^3))) ≤
        C * lpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus (ℝ^3))) := by
  obtain ⟨CP, hP⟩ : ∃ C : ℝ≥0, ∀ v : ℝ^3 → ℝ, ContDiff ℝ 1 v →
      eLpNorm (fun x ↦ v x - ⨍ y in unitAnnulus (ℝ^3), v y) 2
          (volume.restrict (unitAnnulus (ℝ^3))) ≤
        C * eLpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus (ℝ^3))) :=
    exists_eLpNorm_sub_average_le_unitAnnulus 1 2
  refine ⟨CP, CP.2, fun v hv ↦ ?_⟩
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
    (memLp_restrict_unitAnnulus (hv.continuous_fderiv one_ne_zero) 2).eLpNorm_ne_top) (hP v hv)
  rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at h'

/-- The interpolation inequality on the annulus: `a₁⁴ ≤ M a₀² (a₀² + a₁² + a₂²)` for the norms
`aᵢ` of `Dⁱ v` in `L²` of the annulus. -/
private theorem exists_lpNorm_fderiv_pow_four_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v : ℝ^3 → ℝ, ContDiff ℝ 2 v →
      (lpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2) ^ 2 ≤
        M * (lpNorm v 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2 *
          (lpNorm v 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2 +
            lpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2 +
            lpNorm (fderiv ℝ (fderiv ℝ v)) 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2)) := by
  obtain ⟨CE, hCE, hE⟩ := exists_lpNorm_annulusExtension_sq_le (E := ℝ^3) (F := ℝ)
  refine ⟨9 * (CE * CE), by positivity, fun v hv ↦ ?_⟩
  obtain ⟨hv0, -, hv2⟩ := hE v hv
  have hres : lpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus (ℝ^3))) ≤
      lpNorm (fderiv ℝ (annulusExtension v)) 2 volume := by
    have hae : fderiv ℝ v =ᵐ[volume.restrict (unitAnnulus (ℝ^3))]
        fderiv ℝ (annulusExtension v) :=
      (ae_restrict_iff' isOpen_unitAnnulus.measurableSet).2 (Eventually.of_forall fun x hx ↦
        ((annulusExtension_eventuallyEq_mid v hx.1 hx.2).fderiv_eq).symm)
    have hle : eLpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus (ℝ^3))) ≤
        eLpNorm (fderiv ℝ (annulusExtension v)) 2 volume := by
      rw [eLpNorm_congr_ae hae]
      exact eLpNorm_mono_measure _ Measure.restrict_le_self
    exact ENNReal.toReal_mono
      (((contDiff_annulusExtension hv).fderiv_right (m := 1) (by norm_num)).continuous
        |>.memLp_of_hasCompactSupport
          ((hasCompactSupport_annulusExtension v).fderiv ℝ)).eLpNorm_ne_top hle
  have hint := Fourier.lpNorm_fderiv_sq_le (contDiff_annulusExtension hv)
    (hasCompactSupport_annulusExtension v)
  have h1 : lpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2 ≤
      3 * (lpNorm (annulusExtension v) 2 volume *
        lpNorm (fderiv ℝ (fderiv ℝ (annulusExtension v))) 2 volume) :=
    (pow_le_pow_left₀ lpNorm_nonneg hres 2).trans (by exact_mod_cast hint)
  calc (lpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2) ^ 2
      ≤ (3 * (lpNorm (annulusExtension v) 2 volume *
          lpNorm (fderiv ℝ (fderiv ℝ (annulusExtension v))) 2 volume)) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = 9 * (lpNorm (annulusExtension v) 2 volume ^ 2 *
          lpNorm (fderiv ℝ (fderiv ℝ (annulusExtension v))) 2 volume ^ 2) := by ring
    _ ≤ 9 * (CE * lpNorm v 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2 * (CE *
          (lpNorm v 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2 +
            lpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2 +
            lpNorm (fderiv ℝ (fderiv ℝ v)) 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hv0 hv2 (sq_nonneg _) (by positivity))
          (by norm_num)
    _ = _ := by ring

/-- The whole-space inequality for the extension, read on the annulus:
`|w(y)|⁴ ≤ K (b² + a₁²)(b² + a₁² + a₂²)` for the norms `b, a₁, a₂` of `w, Dw, D²w` in `L²` of the
annulus. -/
private theorem exists_abs_pow_four_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℝ^3 → ℝ, ContDiff ℝ 2 w → ∀ y ∈ unitAnnulus (ℝ^3),
      |w y| ^ 4 ≤ K * ((lpNorm w 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2 +
          lpNorm (fderiv ℝ w) 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2) *
        (lpNorm w 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2 +
          lpNorm (fderiv ℝ w) 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2 +
          lpNorm (fderiv ℝ (fderiv ℝ w)) 2 (volume.restrict (unitAnnulus (ℝ^3))) ^ 2)) := by
  obtain ⟨CE, hCE, hE⟩ := exists_lpNorm_annulusExtension_sq_le (E := ℝ^3) (F := ℝ)
  refine ⟨CE * CE, by positivity, fun w hw y hy ↦ ?_⟩
  obtain ⟨-, hw1, hw2⟩ := hE w hw
  have hF3 : w y ^ 2 ≤ lpNorm (fderiv ℝ (annulusExtension w)) 2 volume *
      lpNorm (fderiv ℝ (fderiv ℝ (annulusExtension w))) 2 volume := by
    have h := Fourier.norm_sq_le_of_contDiff_two (contDiff_annulusExtension hw)
      (hasCompactSupport_annulusExtension w) y
    rwa [annulusExtension_eq w hy.1.le hy.2.le, Real.norm_eq_abs, sq_abs] at h
  have h4 : |w y| ^ 4 = (w y ^ 2) ^ 2 := by
    rw [← sq_abs (w y)]
    ring
  rw [h4]
  calc (w y ^ 2) ^ 2 ≤ (lpNorm (fderiv ℝ (annulusExtension w)) 2 volume *
        lpNorm (fderiv ℝ (fderiv ℝ (annulusExtension w))) 2 volume) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) hF3 2
    _ = lpNorm (fderiv ℝ (annulusExtension w)) 2 volume ^ 2 *
        lpNorm (fderiv ℝ (fderiv ℝ (annulusExtension w))) 2 volume ^ 2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul hw1 hw2 (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- Agmon's inequality on the annulus for real functions. -/
private theorem exists_abs_le_unitAnnulus :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ^3 → ℝ, ContDiff ℝ 2 v → ∀ y ∈ unitAnnulus (ℝ^3),
      |v y| ≤ C * (lpNorm v 2 (volume.restrict (unitAnnulus (ℝ^3))) +
        √(lpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus (ℝ^3)))) *
          √(lpNorm (fderiv ℝ (fderiv ℝ v)) 2 (volume.restrict (unitAnnulus (ℝ^3))))) := by
  obtain ⟨cA, hcA0, hmean⟩ := exists_abs_setAverage_le
  obtain ⟨CP, hCP0, hP⟩ := exists_lpNorm_sub_setAverage_le
  obtain ⟨M, hM0, hI⟩ := exists_lpNorm_fderiv_pow_four_le
  obtain ⟨K, hK0, hG⟩ := exists_abs_pow_four_le
  set L : ℝ := 2 * K * (CP ^ 2 + 1) ^ 2 * (1 + 2 * M + 4 * M ^ 2) with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨cA + (L + 1), by positivity, fun v hv y hy ↦ ?_⟩
  set m : ℝ := ⨍ x in unitAnnulus (ℝ^3), v x with hm
  have hw : ContDiff ℝ 2 (fun x ↦ v x - m) := hv.sub contDiff_const
  have hDw : fderiv ℝ (fun x ↦ v x - m) = fderiv ℝ v :=
    funext fun x ↦ fderiv_sub_const (f := v) (x := x) m
  have hF1 := hP v (hv.of_le (by norm_num))
  have hF5 := hmean v hv.continuous
  have hF4 := hI v hv
  have hS := hG (fun x ↦ v x - m) hw y hy
  rw [hDw] at hS
  rw [← hm] at hF1 hF5
  set a₀ := lpNorm v 2 (volume.restrict (unitAnnulus (ℝ^3))) with ha₀
  set a₁ := lpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus (ℝ^3))) with ha₁
  set a₂ := lpNorm (fderiv ℝ (fderiv ℝ v)) 2 (volume.restrict (unitAnnulus (ℝ^3))) with ha₂
  set b := lpNorm (fun x ↦ v x - m) 2 (volume.restrict (unitAnnulus (ℝ^3))) with hb
  have ha₀0 : 0 ≤ a₀ := lpNorm_nonneg
  have ha₁0 : 0 ≤ a₁ := lpNorm_nonneg
  have ha₂0 : 0 ≤ a₂ := lpNorm_nonneg
  have hb0 : 0 ≤ b := lpNorm_nonneg
  have hb2 : b ^ 2 ≤ CP ^ 2 * a₁ ^ 2 := by
    have h := pow_le_pow_left₀ hb0 hF1 2
    rwa [mul_pow] at h
  have halg := annulus_algebra (sq_nonneg a₀) (sq_nonneg a₁) (sq_nonneg a₂) (sq_nonneg b) hM0
    (sq_nonneg CP) hK0 hF4 hb2 hS
  rw [← hL] at halg
  set t := √a₁ * √a₂ with ht
  have ht0 : 0 ≤ t := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have ht2 : t ^ 2 = a₁ * a₂ := by
    rw [ht, mul_pow, Real.sq_sqrt ha₁0, Real.sq_sqrt ha₂0]
  have hpoly : (a₀ ^ 2) ^ 2 + a₁ ^ 2 * a₂ ^ 2 ≤ (a₀ + t) ^ 4 := by
    have h : a₁ ^ 2 * a₂ ^ 2 = (t ^ 2) ^ 2 := by
      rw [ht2]
      ring
    have e : (a₀ + t) ^ 4 = (a₀ ^ 2) ^ 2 + (t ^ 2) ^ 2 +
        (4 * (a₀ ^ 3 * t) + 6 * (a₀ ^ 2 * t ^ 2) + 4 * (a₀ * t ^ 3)) := by ring
    rw [h, e]
    have h1 := mul_nonneg (pow_nonneg ha₀0 3) ht0
    have h2 := mul_nonneg (pow_nonneg ha₀0 2) (pow_nonneg ht0 2)
    have h3 := mul_nonneg ha₀0 (pow_nonneg ht0 3)
    linarith
  have hsw : |v y - m| ≤ (L + 1) * (a₀ + t) := by
    refine (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity)
      (by norm_num : (4 : ℕ) ≠ 0)).1 ?_
    calc |v y - m| ^ 4 ≤ L * ((a₀ ^ 2) ^ 2 + a₁ ^ 2 * a₂ ^ 2) := halg
      _ ≤ L * (a₀ + t) ^ 4 := mul_le_mul_of_nonneg_left hpoly hL0
      _ ≤ (L + 1) ^ 4 * (a₀ + t) ^ 4 :=
          mul_le_mul_of_nonneg_right
            ((lt_add_one L).le.trans (le_self_pow₀ (by linarith) (by norm_num)))
            (by positivity)
      _ = ((L + 1) * (a₀ + t)) ^ 4 := (mul_pow _ _ _).symm
  have hvy : v y = (v y - m) + m := by ring
  have hcross := mul_nonneg hcA0 ht0
  calc |v y| = |(v y - m) + m| := by rw [← hvy]
    _ ≤ |v y - m| + |m| := abs_add_le _ _
    _ ≤ (L + 1) * (a₀ + t) + cA * a₀ := add_le_add hsw hF5
    _ ≤ (cA + (L + 1)) * (a₀ + t) := by linarith

/-- **Agmon's inequality on the annulus `A = {1 < |y| < 2}` of `ℝ³`.** There is a constant `C`
such that every `C²` function `v : ℝ³ → F` satisfies, at every point `y` of `A`,
`|v(y)| ≤ C (‖v‖_{L²(A)} + ‖Dv‖_{L²(A)}^{1/2} ‖D²v‖_{L²(A)}^{1/2})`.
All three norms are taken over the annulus only, with the operator norms of the Fréchet
derivatives. This is the form that a dyadic decay argument needs: after rescaling, the first
term carries the size of the function on a dyadic shell and the second the sizes of its
derivatives there. The proof extends `v` minus its mean to the whole space, applies the
whole-space inequality, and removes the term `‖Dv‖²` by interpolation. -/
theorem exists_norm_le_unitAnnulus {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ^3 → F, ContDiff ℝ 2 v → ∀ y ∈ unitAnnulus (ℝ^3),
      ‖v y‖ ≤ C * (lpNorm v 2 (volume.restrict (unitAnnulus (ℝ^3))) +
        √(lpNorm (fderiv ℝ v) 2 (volume.restrict (unitAnnulus (ℝ^3)))) *
          √(lpNorm (fderiv ℝ (fderiv ℝ v)) 2 (volume.restrict (unitAnnulus (ℝ^3))))) := by
  obtain ⟨C, hC, h⟩ := exists_abs_le_unitAnnulus
  refine ⟨C, hC, fun v hv y hy ↦ ?_⟩
  obtain ⟨φ, hφ, hφy⟩ := exists_dual_vector'' ℝ (v y)
  have hv1 : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
  obtain ⟨h0, h1, h2⟩ := Fourier.lpNorm_comp_le_of_norm_le_one
    (ν := volume.restrict (unitAnnulus (ℝ^3))) hφ hv
    (memLp_restrict_unitAnnulus hv.continuous 2) (memLp_restrict_unitAnnulus hv1.continuous 2)
    (memLp_restrict_unitAnnulus (hv1.continuous_fderiv one_ne_zero) 2)
  have hreal := h (φ ∘ v) (φ.contDiff.comp hv) y hy
  have hval : (φ ∘ v) y = ‖v y‖ := by simpa using hφy
  rw [hval, abs_of_nonneg (norm_nonneg _)] at hreal
  refine hreal.trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact add_le_add h0 (mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end Three

end PDE.Analysis
