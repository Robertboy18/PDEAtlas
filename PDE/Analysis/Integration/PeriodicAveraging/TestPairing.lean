/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.Unfolding
public import PDE.Analysis.Integration.PeriodicAveraging.LocalLp

/-!
# Unfolding periodic L² pairings

A periodic square integrable field pairs integrably with a continuous compactly
supported Euclidean test. Periodizing the test turns this pairing into its
single-cell integral, without requiring continuity of the periodic field.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped ENNReal Topology InnerProductSpace

namespace PDE.Analysis.PeriodicAveraging

/-- Integer translations do not change the image in the unit torus. -/
theorem toTorus_add_integerVector {n : ℕ} (x : ℝ^n) (k : Fin n → ℤ) :
    toTorus n (x + integerVector n k) = toTorus n x := by
  ext i
  change ((x i + (k i : ℝ) : ℝ) : UnitAddCircle) = (x i : UnitAddCircle)
  rw [AddCircle.coe_add]
  have hz : ((k i : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k i, by simp⟩
  rw [hz, add_zero]

/-- Bounded linear maps commute with locally finite periodization. -/
theorem map_periodize {n : ℕ} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {f : ℝ^n → E} (hf : HasCompactSupport f) (x : ℝ^n) :
    L (periodize f x) = periodize (fun y ↦ L (f y)) x :=
  L.toLinearMap.toAddMonoidHom.map_finsum ((locallyFinite_integer_translates hf).point_finite x)

/-- A periodic L² field can be paired integrably with a continuous compact test. -/
theorem integrable_inner_toTorus {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : Lp E 2 (cellMeasure n)) {g : ℝ^n → E}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x ↦ ⟪v (toTorus n x), g x⟫_ℝ) := by
  have hv : MemLp (fun x ↦ v (toTorus n x)) 2 (volume.restrict (tsupport g)) := by
    simpa only [inv_one, one_smul] using memLp_rescale hgc.isBounded
      (1 : ℝ) zero_lt_one le_rfl v
  have hgm : MemLp g 2 (volume.restrict (tsupport g)) :=
    hg.memLp_of_hasCompactSupport hgc
  have hi := L2.integrable_inner (𝕜 := ℝ) (hv.toLp _) (hgm.toLp _)
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    (hi.congr ?_)
  · intro x hx
    apply subset_tsupport g
    intro hxg
    exact hx (by simp only [hxg, inner_zero_right])
  · filter_upwards [hv.coeFn_toLp, hgm.coeFn_toLp] with x hx hy
    rw [hx, hy]

/-- A cell pairing with a periodized test unfolds to the Euclidean compact-test pairing. -/
theorem integral_inner_periodizeTorus {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : Lp E 2 (cellMeasure n)) {g : ℝ^n → E}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    (∫ y, ⟪v y, periodizeTorus g hg hgc y⟫_ℝ ∂cellMeasure n) =
      ∫ x, ⟪v (toTorus n x), g x⟫_ℝ := by
  let G := periodizeTorus g hg hgc
  let f := fun x : ℝ^n ↦ ⟪v (toTorus n x), g x⟫_ℝ
  have hfc : HasCompactSupport f := hgc.mono' (fun x hx ↦
    subset_tsupport g (fun hxg ↦ hx (by simp only [f, hxg, inner_zero_right])))
  have hperiod (x : ℝ^n) : periodize f x = ⟪v (toTorus n x), periodize g x⟫_ℝ := by
    change periodize f x = (innerSL ℝ (v (toTorus n x))) (periodize g x)
    rw [map_periodize (innerSL ℝ (v (toTorus n x))) hgc]
    change (∑ᶠ k : Fin n → ℤ, f (x + integerVector n k)) =
      ∑ᶠ k : Fin n → ℤ, ⟪v (toTorus n x), g (x + integerVector n k)⟫_ℝ
    simp only [f, toTorus_add_integerVector]
  have hp := measurePreserving_toTorus (fun _ : Fin n ↦ (0 : ℝ))
  have hm : AEStronglyMeasurable (fun y ↦ ⟪v y, G y⟫_ℝ) (cellMeasure n) :=
    (Lp.aestronglyMeasurable v).inner G.continuous.aestronglyMeasurable
  have hmm : AEStronglyMeasurable (fun y ↦ ⟪v y, G y⟫_ℝ)
      (Measure.map (toTorus n) (volume.restrict (unitCell (fun _ ↦ 0)))) := by
    rw [hp.map_eq]
    exact hm
  have he := integral_map hp.measurable.aemeasurable hmm
  rw [hp.map_eq] at he
  calc
    _ = ∫ x in unitCell (fun _ : Fin n ↦ (0 : ℝ)), ⟪v (toTorus n x), G (toTorus n x)⟫_ℝ := he
    _ = ∫ x in unitCell (fun _ : Fin n ↦ (0 : ℝ)), periodize f x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by
        change ⟪v (toTorus n x), periodizeTorus g hg hgc (toTorus n x)⟫_ℝ = _
        rw [hperiod, periodizeTorus_toTorus]
    _ = ∫ x, f x := integral_periodize_unitCell (integrable_inner_toTorus v hg hgc) hfc

end PDE.Analysis.PeriodicAveraging
