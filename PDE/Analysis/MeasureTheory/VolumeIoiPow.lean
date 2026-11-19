/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Dilation of polynomially weighted radial measure

Multiplication by `a > 0` sends the measure `r^n dr` on the positive ray to
`a^(-(n+1)) r^n dr`. On the positive meridian, `(r,z) ↦ (a*r, a*(z-b))`
therefore gives the factor `a^(-(n+2))`; axial translation preserves volume.
The proof uses Mathlib's interval formula for `volumeIoiPow`.
-/

@[expose] public section

noncomputable section

open Set

namespace MeasureTheory.Measure

/-- The pushforward of `r^n dr` under multiplication by a positive constant. -/
theorem map_volumeIoiPow_mul (n : ℕ) {a : ℝ} (ha : 0 < a) :
    map (fun r : Ioi (0 : ℝ) ↦
      (⟨a * r.1, mul_pos ha r.2⟩ : Ioi (0 : ℝ))) (volumeIoiPow n) =
      ENNReal.ofReal (a⁻¹ ^ (n + 1)) • volumeIoiPow n := by
  let d : Ioi (0 : ℝ) → Ioi (0 : ℝ) :=
    fun r ↦ ⟨a * r.1, mul_pos ha r.2⟩
  have hd : Measurable d := by
    dsimp [d]
    fun_prop
  have hIio (x : Ioi (0 : ℝ)) :
      map d (volumeIoiPow n) (Iio x) =
        (ENNReal.ofReal (a⁻¹ ^ (n + 1)) • volumeIoiPow n) (Iio x) := by
    have hpre : d ⁻¹' Iio x = Iio (⟨x.1 / a, div_pos x.2 ha⟩ : Ioi (0 : ℝ)) := by
      ext r
      change a * r.1 < x.1 ↔ r.1 < x.1 / a
      rw [lt_div_iff₀ ha, mul_comm]
    rw [map_apply hd measurableSet_Iio, hpre, volumeIoiPow_apply_Iio,
      smul_apply, smul_eq_mul, volumeIoiPow_apply_Iio,
      ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr ha.le) _)]
    congr 1
    simp only [div_eq_mul_inv, mul_pow]
    ring
  let fs := finiteSpanningSetsIn_volumeIoiPow_range_Iio n
  let cover : (map d (volumeIoiPow n)).FiniteSpanningSetsIn (range Iio) :=
    { set := fs.set
      set_mem := fs.set_mem
      spanning := fs.spanning
      finite := fun k ↦ by
        obtain ⟨x, hx⟩ := fs.set_mem k
        rw [← hx, hIio, smul_apply, smul_eq_mul, volumeIoiPow_apply_Iio]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top }
  exact cover.ext
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iio _))
    isPiSystem_Iio (by rintro s ⟨x, rfl⟩; exact hIio x)

/-- Scaling both meridian coordinates multiplies the pushforward of `r^n dr dz`
by `a^(-(n+2))`, independently of the axial translation. -/
theorem map_volumeIoiPow_prod_mul_sub (n : ℕ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    map (Prod.map
      (fun r : Ioi (0 : ℝ) ↦ (⟨a * r.1, mul_pos ha r.2⟩ : Ioi (0 : ℝ)))
      (fun z : ℝ ↦ a * (z - b))) ((volumeIoiPow n).prod volume) =
      ENNReal.ofReal (a⁻¹ ^ (n + 2)) • (volumeIoiPow n).prod volume := by
  have hd : Measurable
      (fun r : Ioi (0 : ℝ) ↦ (⟨a * r.1, mul_pos ha r.2⟩ : Ioi (0 : ℝ))) := by
    fun_prop
  have hz : Measurable (fun z : ℝ ↦ a * (z - b)) := by fun_prop
  have hzmap : map (fun z : ℝ ↦ a * (z - b)) volume =
      ENNReal.ofReal a⁻¹ • volume := by
    calc
      _ = map (a * ·) (map (· - b) volume) :=
        (map_map (measurable_const_mul a) (measurable_id.sub_const b)).symm
      _ = _ := by
        rw [map_sub_right_eq_self, Real.map_volume_mul_left ha.ne',
          abs_of_pos (inv_pos.mpr ha)]
  rw [← map_prod_map (volumeIoiPow n) volume hd hz,
    map_volumeIoiPow_mul n ha, hzmap, prod_smul_left, prod_smul_right,
    smul_smul, ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr ha.le) _),
    ← pow_succ]

end MeasureTheory.Measure

namespace MeasureTheory

/-- Change of variables for an integrable density under a positive meridian
dilation and axial translation, with weight `r^n dr dz`. -/
theorem integral_volumeIoiPow_prod_mul_sub
    (n : ℕ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    {g : Ioi (0 : ℝ) × ℝ → ℝ}
    (hg : Integrable g ((Measure.volumeIoiPow n).prod volume)) :
    (∫ q : Ioi (0 : ℝ) × ℝ,
      g (⟨a * q.1.1, mul_pos ha q.1.2⟩, a * (q.2 - b))
        ∂(Measure.volumeIoiPow n).prod volume) =
      a⁻¹ ^ (n + 2) * ∫ q, g q ∂(Measure.volumeIoiPow n).prod volume := by
  let φ := Prod.map
    (fun r : Ioi (0 : ℝ) ↦ (⟨a * r.1, mul_pos ha r.2⟩ : Ioi (0 : ℝ)))
    (fun z : ℝ ↦ a * (z - b))
  have hφ : Measurable φ := by
    dsimp [φ]
    fun_prop
  have hm : Measure.map φ ((Measure.volumeIoiPow n).prod volume) =
      ENNReal.ofReal (a⁻¹ ^ (n + 2)) • (Measure.volumeIoiPow n).prod volume :=
    Measure.map_volumeIoiPow_prod_mul_sub n ha b
  have hgmap : Integrable g (Measure.map φ ((Measure.volumeIoiPow n).prod volume)) := by
    rw [hm]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  change (∫ q, g (φ q) ∂(Measure.volumeIoiPow n).prod volume) = _
  rw [← integral_map hφ.aemeasurable hgmap.aestronglyMeasurable, hm,
    integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg (inv_nonneg.mpr ha.le) _),
    smul_eq_mul]

end MeasureTheory
