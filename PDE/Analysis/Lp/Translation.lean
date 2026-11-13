/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Translation on L²

`translateL2 𝕜 y` is the linear isometry represented by `u (x - y)`.
The scalar field is explicit, so the same operator supports real and complex
linearity for arbitrary normed codomains. In particular, positive increments
`u (x + h)` are represented by `translateL2 𝕜 (-h)`.

The translation orbit of every L² vector is continuous in its displacement.
Translations compose by addition, commute with bounded postcomposition, and
have the opposite translation as adjoint on Hilbert-valued L².
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace PDE.Analysis

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Translation of an L² vector by `y`, represented by `x ↦ u (x - y)`. -/
def translateL2 (y : ℝ^n) :
    Lp E 2 (volume : Measure (ℝ^n)) →ₗᵢ[𝕜] Lp E 2 (volume : Measure (ℝ^n)) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (fun x : ℝ^n ↦ -y + x)
    (measurePreserving_add_left volume (-y))

/-- Translation preserves the L² norm. -/
theorem norm_translateL2 (y : ℝ^n) (u : Lp E 2 (volume : Measure (ℝ^n))) :
    ‖translateL2 𝕜 y u‖ = ‖u‖ :=
  (translateL2 𝕜 y).norm_map u

/-- Each translation orbit is continuous in L², including for nonsmooth inputs. -/
theorem continuous_translateL2 (u : Lp E 2 (volume : Measure (ℝ^n))) :
    Continuous (fun y : ℝ^n ↦ translateL2 𝕜 y u) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  change Continuous (fun y : ℝ^n ↦ DomAddAct.mk (-y) +ᵥ u)
  exact (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const

/-- The translation operator agrees almost everywhere with translation of a representative. -/
theorem translateL2_ae_eq (y : ℝ^n) (u : Lp E 2 (volume : Measure (ℝ^n))) :
    translateL2 𝕜 y u =ᵐ[volume] fun x ↦ u (x - y) := by
  change Lp.compMeasurePreserving (fun x : ℝ^n ↦ -y + x)
    (measurePreserving_add_left volume (-y)) u =ᵐ[volume] fun x ↦ u (x - y)
  filter_upwards [Lp.coeFn_compMeasurePreserving u
    (measurePreserving_add_left volume (-y))] with x hx
  simpa only [Function.comp_apply, sub_eq_add_neg, add_comm] using hx

/-- Translation by zero fixes every L² vector. -/
@[simp]
theorem translateL2_zero (u : Lp E 2 (volume : Measure (ℝ^n))) :
    translateL2 𝕜 (0 : ℝ^n) u = u := by
  apply Lp.ext
  filter_upwards [translateL2_ae_eq 𝕜 (0 : ℝ^n) u] with x hx
  simpa only [sub_zero] using hx

/-- Successive translations add their displacement vectors. -/
theorem translateL2_add (a b : ℝ^n) (u : Lp E 2 (volume : Measure (ℝ^n))) :
    translateL2 𝕜 a (translateL2 𝕜 b u) = translateL2 𝕜 (a + b) u := by
  apply Lp.ext
  have hb : (fun x ↦ translateL2 𝕜 b u (x - a)) =ᵐ[volume]
      fun x ↦ u ((x - a) - b) := by
    simpa only [Function.comp_def, sub_eq_add_neg, add_comm] using
      (measurePreserving_add_left volume (-a)).quasiMeasurePreserving.ae_eq_comp
        (translateL2_ae_eq 𝕜 b u)
  filter_upwards [translateL2_ae_eq 𝕜 a (translateL2 𝕜 b u),
    translateL2_ae_eq 𝕜 (a + b) u, hb] with x ha hab hb
  rw [ha, hab, hb, sub_sub]

/-- Bounded postcomposition commutes with spatial translation on L². -/
theorem compLp_translateL2 {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (L : E →L[𝕜] F) (y : ℝ^n) (u : Lp E 2 (volume : Measure (ℝ^n))) :
    L.compLp (translateL2 𝕜 y u) = translateL2 𝕜 y (L.compLp u) := by
  apply Lp.ext
  have hpost : (fun x ↦ L.compLp u (x - y)) =ᵐ[volume]
      fun x ↦ L (u (x - y)) := by
    simpa only [Function.comp_def, sub_eq_add_neg, add_comm] using
      (measurePreserving_add_left volume (-y)).quasiMeasurePreserving.ae_eq_comp
        (L.coeFn_compLp u)
  filter_upwards [L.coeFn_compLp (translateL2 𝕜 y u), translateL2_ae_eq 𝕜 y u,
    translateL2_ae_eq 𝕜 y (L.compLp u), hpost] with x hL hu hT hpost
  rw [hL, hu, hT, hpost]

end PDE.Analysis

namespace PDE.Analysis

variable (𝕜 : Type*) [RCLike 𝕜]
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Translation is adjoint to translation by the opposite displacement. -/
theorem inner_translateL2_left (y : ℝ^n)
    (u v : Lp E 2 (volume : Measure (ℝ^n))) :
    inner 𝕜 (translateL2 𝕜 y u) v = inner 𝕜 u (translateL2 𝕜 (-y) v) := by
  have hv : translateL2 𝕜 y (translateL2 𝕜 (-y) v) = v := by
    rw [translateL2_add, add_neg_cancel, translateL2_zero]
  calc
    inner 𝕜 (translateL2 𝕜 y u) v =
        inner 𝕜 (translateL2 𝕜 y u)
          (translateL2 𝕜 y (translateL2 𝕜 (-y) v)) := by rw [hv]
    _ = inner 𝕜 u (translateL2 𝕜 (-y) v) :=
      (translateL2 𝕜 y).inner_map_map u (translateL2 𝕜 (-y) v)

end PDE.Analysis
