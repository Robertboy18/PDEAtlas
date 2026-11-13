/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.LinearInterpolation

/-!
# Bilinear interpolation errors

Successive endpoint interpolation in the two coordinates has error bounded by
`Mx (b-a)^2 / 8 + My (d-c)^2 / 8`, with separate pure second-derivative bounds.
Mixed derivatives are unnecessary. The proof first interpolates one coordinate,
then takes a convex combination of the two errors in the other coordinate.
This is the cell estimate (7.1) of Hou, Wang and Yang (`abs_sub_bilinearInterpolant_le`); the
pointwise envelope `abs_sub_bilinearInterpolant_le_envelope` is the bound (4.13) in the proof of
Chen and Hou's trapezoidal rule (Part II, Lemma 4.2).
A common upper bound of the four vertex values bounds the interpolant
(`bilinearInterpolant_le`), and the interpolant is linear in the interpolated function
(`bilinearInterpolant_linear_combination`); together they bound a quadratic form with
interpolated entries by its bound at the vertices.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 7.3, (7.1).
  <https://arxiv.org/abs/2509.25116v2>
* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Section 4.1.3, (4.13)
  in the proof of Lemma 4.2. <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Approximation

/-- Endpoint interpolation preserves a common absolute bound on its two values. -/
theorem abs_linearInterpolant_le {a b x fa fb B : ℝ}
    (hab : a < b) (hx : x ∈ Set.Icc a b) (hfa : |fa| ≤ B) (hfb : |fb| ≤ B) :
    |linearInterpolant a b fa fb x| ≤ B := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hw₀ : 0 ≤ (b - x) / (b - a) :=
    div_nonneg (sub_nonneg.mpr hx.2) hden.le
  have hw₁ : 0 ≤ (x - a) / (b - a) :=
    div_nonneg (sub_nonneg.mpr hx.1) hden.le
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp [hden.ne']
    ring
  unfold linearInterpolant
  calc
    _ ≤ |(b - x) / (b - a) * fa| + |(x - a) / (b - a) * fb| := abs_add_le _ _
    _ = (b - x) / (b - a) * |fa| + (x - a) / (b - a) * |fb| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw₀, abs_of_nonneg hw₁]
    _ ≤ (b - x) / (b - a) * B + (x - a) / (b - a) * B :=
      add_le_add (mul_le_mul_of_nonneg_left hfa hw₀) (mul_le_mul_of_nonneg_left hfb hw₁)
    _ = B := by rw [← add_mul, hsum, one_mul]

/-- The interpolant through the four values on a rectangular cell. -/
def bilinearInterpolant (f : ℝ → ℝ → ℝ) (a b c d x y : ℝ) : ℝ :=
  linearInterpolant a b
    (linearInterpolant c d (f a c) (f a d) y)
    (linearInterpolant c d (f b c) (f b d) y) x

/-- Bounds `Mx` and `My` on the pure second derivatives give the error bound
`Mx (b - a)² / 8 + My (d - c)² / 8` for the bilinear cell interpolant.
The derivative fields are proved classical derivatives on the interiors of their slices. -/
theorem abs_sub_bilinearInterpolant_le
    {f fx fxx fy fyy : ℝ → ℝ → ℝ} {a b c d x y Mx My : ℝ}
    (hab : a < b) (hcd : c < d)
    (hcontX : ∀ v ∈ Set.Icc c d, ContinuousOn (fun u ↦ f u v) (Set.Icc a b))
    (hderivX : ∀ v ∈ Set.Icc c d, ∀ u ∈ Set.Ioo a b,
      HasDerivAt (fun z ↦ f z v) (fx u v) u)
    (hderivXX : ∀ v ∈ Set.Icc c d, ∀ u ∈ Set.Ioo a b,
      HasDerivAt (fun z ↦ fx z v) (fxx u v) u)
    (hboundX : ∀ v ∈ Set.Icc c d, ∀ u ∈ Set.Ioo a b, |fxx u v| ≤ Mx)
    (hcontY : ∀ u ∈ Set.Icc a b, ContinuousOn (f u) (Set.Icc c d))
    (hderivY : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Ioo c d, HasDerivAt (f u) (fy u v) v)
    (hderivYY : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Ioo c d,
      HasDerivAt (fy u) (fyy u v) v)
    (hboundY : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Ioo c d, |fyy u v| ≤ My)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    |f x y - bilinearInterpolant f a b c d x y| ≤
      Mx * (b - a) ^ 2 / 8 + My * (d - c) ^ 2 / 8 := by
  have hrow : |f x y - linearInterpolant a b (f a y) (f b y) x| ≤
      Mx * (b - a) ^ 2 / 8 :=
    abs_sub_linearInterpolant_le_uniform hab (hcontX y hy)
      (hderivX y hy) (hderivXX y hy) (hboundX y hy) hx
  have hcolumn (u : ℝ) (hu : u ∈ Set.Icc a b) :
      |f u y - linearInterpolant c d (f u c) (f u d) y| ≤ My * (d - c) ^ 2 / 8 :=
    abs_sub_linearInterpolant_le_uniform hcd (hcontY u hu)
      (hderivY u hu) (hderivYY u hu) (hboundY u hu) hy
  have hcombination := abs_linearInterpolant_le hab hx
    (hcolumn a ⟨le_rfl, hab.le⟩) (hcolumn b ⟨hab.le, le_rfl⟩)
  have hid : f x y - bilinearInterpolant f a b c d x y =
      (f x y - linearInterpolant a b (f a y) (f b y) x) +
        linearInterpolant a b
          (f a y - linearInterpolant c d (f a c) (f a d) y)
          (f b y - linearInterpolant c d (f b c) (f b d) y) x := by
    unfold bilinearInterpolant linearInterpolant
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hrow hcombination)

/-- The pointwise error envelope of bilinear interpolation:
`|f - If| ≤ Mx (x - a) (b - x) / 2 + My (y - c) (d - y) / 2`. Integrating it over the cell gives
the trapezoid bound for `∫ |f|` (Chen and Hou, Part II, (4.13) in the proof of Lemma 4.2). -/
theorem abs_sub_bilinearInterpolant_le_envelope
    {f fx fxx fy fyy : ℝ → ℝ → ℝ} {a b c d x y Mx My : ℝ}
    (hab : a < b) (hcd : c < d)
    (hcontX : ∀ v ∈ Set.Icc c d, ContinuousOn (fun u ↦ f u v) (Set.Icc a b))
    (hderivX : ∀ v ∈ Set.Icc c d, ∀ u ∈ Set.Ioo a b,
      HasDerivAt (fun z ↦ f z v) (fx u v) u)
    (hderivXX : ∀ v ∈ Set.Icc c d, ∀ u ∈ Set.Ioo a b,
      HasDerivAt (fun z ↦ fx z v) (fxx u v) u)
    (hboundX : ∀ v ∈ Set.Icc c d, ∀ u ∈ Set.Ioo a b, |fxx u v| ≤ Mx)
    (hcontY : ∀ u ∈ Set.Icc a b, ContinuousOn (f u) (Set.Icc c d))
    (hderivY : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Ioo c d, HasDerivAt (f u) (fy u v) v)
    (hderivYY : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Ioo c d,
      HasDerivAt (fy u) (fyy u v) v)
    (hboundY : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Ioo c d, |fyy u v| ≤ My)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    |f x y - bilinearInterpolant f a b c d x y| ≤
      Mx * (x - a) * (b - x) / 2 + My * (y - c) * (d - y) / 2 := by
  have hrow := abs_sub_linearInterpolant_le hab (hcontX y hy) (hderivX y hy) (hderivXX y hy)
    (hboundX y hy) hx
  have hcolumn (u : ℝ) (hu : u ∈ Set.Icc a b) :
      |f u y - linearInterpolant c d (f u c) (f u d) y| ≤ My * (y - c) * (d - y) / 2 :=
    abs_sub_linearInterpolant_le hcd (hcontY u hu) (hderivY u hu) (hderivYY u hu)
      (hboundY u hu) hy
  have hcombination := abs_linearInterpolant_le hab hx
    (hcolumn a ⟨le_rfl, hab.le⟩) (hcolumn b ⟨hab.le, le_rfl⟩)
  have hid : f x y - bilinearInterpolant f a b c d x y =
      (f x y - linearInterpolant a b (f a y) (f b y) x) +
        linearInterpolant a b
          (f a y - linearInterpolant c d (f a c) (f a d) y)
          (f b y - linearInterpolant c d (f b c) (f b d) y) x := by
    unfold bilinearInterpolant linearInterpolant
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hrow hcombination)

/-- A common bound on all four vertex values bounds the bilinear interpolant. -/
theorem abs_bilinearInterpolant_le {f : ℝ → ℝ → ℝ} {a b c d x y B : ℝ}
    (hab : a < b) (hcd : c < d) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d)
    (hac : |f a c| ≤ B) (had : |f a d| ≤ B)
    (hbc : |f b c| ≤ B) (hbd : |f b d| ≤ B) :
    |bilinearInterpolant f a b c d x y| ≤ B :=
  abs_linearInterpolant_le hab hx
    (abs_linearInterpolant_le hcd hy hac had) (abs_linearInterpolant_le hcd hy hbc hbd)

/-- A common upper bound of the four vertex values bounds the bilinear interpolant. -/
theorem bilinearInterpolant_le {f : ℝ → ℝ → ℝ} {a b c d x y B : ℝ}
    (hab : a < b) (hcd : c < d) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d)
    (hac : f a c ≤ B) (had : f a d ≤ B) (hbc : f b c ≤ B) (hbd : f b d ≤ B) :
    bilinearInterpolant f a b c d x y ≤ B :=
  linearInterpolant_le hab hx (linearInterpolant_le hcd hy hac had)
    (linearInterpolant_le hcd hy hbc hbd)

/-- The bilinear interpolant is linear in the interpolated function. -/
theorem bilinearInterpolant_linear_combination {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (f : ι → ℝ → ℝ → ℝ) (a b c d x y : ℝ) :
    ∑ k ∈ s, w k * bilinearInterpolant (f k) a b c d x y =
      bilinearInterpolant (fun u v ↦ ∑ k ∈ s, w k * f k u v) a b c d x y := by
  unfold bilinearInterpolant linearInterpolant
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end PDE.Analysis.Approximation
