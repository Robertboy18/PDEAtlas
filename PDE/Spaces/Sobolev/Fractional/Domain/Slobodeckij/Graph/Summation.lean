/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Notation
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Physical representatives of sums in the Gagliardo graph

An absolutely summable family in the Gagliardo graph has the expected pointwise sum of
base representatives almost everywhere. The result applies to every real order and every
exponent at least one, including infinity. The domain need not be open or have finite measure.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [Countable ι]

/-- Absolute summability in the graph norm identifies the base representative of the sum
with the pointwise series almost everywhere on the domain. -/
theorem toLp_tsum_ae (u : ι → W^{s,p}(Ω; F))
    (hu : Summable (fun i ↦ ‖u i‖)) :
    (toLp n s Ω (∑' i, u i) : ℝ^n → F) =ᵐ[(volume : Measure (ℝ^n)).restrict Ω]
      fun x ↦ ∑' i, toLp n s Ω (u i) x := by
  let B := toLp n s Ω (p := p) (F := F)
  have hB : Summable (fun i ↦ ‖B (u i)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun i ↦ B.le_opNorm (u i)) (hu.mul_left ‖B‖)
  have he : (∑' i, ‖B (u i)‖ₑ) ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hB
  change (fun x ↦ B (∑' i, u i) x) =ᵐ[(volume : Measure (ℝ^n)).restrict Ω] _
  rw [B.map_tsum hu.of_norm]
  exact Lp.coeFn_tsum he

/-- Chosen representatives of an absolutely summable graph family may be summed pointwise.
In particular, this applies to prescribed representatives of local approximation errors. -/
theorem toLp_tsum_ae_of_representatives
    (u : ι → W^{s,p}(Ω; F))
    (hu : Summable (fun i ↦ ‖u i‖)) (f : ι → ℝ^n → F)
    (hf : ∀ i, (toLp n s Ω (u i) : ℝ^n → F)
      =ᵐ[(volume : Measure (ℝ^n)).restrict Ω] f i) :
    (toLp n s Ω (∑' i, u i) : ℝ^n → F) =ᵐ[(volume : Measure (ℝ^n)).restrict Ω]
      fun x ↦ ∑' i, f i x := by
  filter_upwards [toLp_tsum_ae u hu, ae_all_iff.mpr hf] with x hsum hx
  exact hsum.trans (tsum_congr hx)

end SobolevSpace.Fractional.GagliardoSpace
