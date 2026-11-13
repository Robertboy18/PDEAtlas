/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Notation

/-!
# Function representatives of the Gagliardo graph

These identities connect the bundled graph space to the functions used in
approximation estimates. Rebuilding an element from its `Lᵖ` representative
preserves both coordinates.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The representative of a sum is the pointwise sum almost everywhere. -/
theorem toLp_add_apply_ae (u v : W^{s,p}(Ω; F)) :
    (toLp n s Ω (u + v) : ℝ^n → F) =ᵐ[volume.restrict Ω]
      fun x ↦ toLp n s Ω u x + toLp n s Ω v x := by
  rw [map_add]
  filter_upwards [Lp.coeFn_add (toLp n s Ω u) (toLp n s Ω v)] with x hx
  exact hx

/-- The representative of a difference is the pointwise difference almost everywhere. -/
theorem toLp_sub_apply_ae (u v : W^{s,p}(Ω; F)) :
    (toLp n s Ω (u - v) : ℝ^n → F) =ᵐ[volume.restrict Ω]
      fun x ↦ toLp n s Ω u x - toLp n s Ω v x := by
  rw [map_sub]
  filter_upwards [Lp.coeFn_sub (toLp n s Ω u) (toLp n s Ω v)] with x hx
  exact hx

/-- A graph element built from a function has its physical weighted difference
as its second `Lᵖ` coordinate. -/
@[simp]
theorem differenceQuotient_ofFunction (u : ℝ^n → F)
    (hu : MemGagliardo n s Ω u (p := p)) :
    differenceQuotient n s Ω (ofFunction u hu) =
      hu.2.toLp (diffQuot n s u (p := p)) := by
  apply Lp.ext
  exact ((differenceQuotient_apply_ae (ofFunction u hu)).trans
    (diffQuot_congr_ae (toLp_ofFunction_apply_ae u hu))).trans hu.2.coeFn_toLp.symm

/-- The `Lᵖ` representative of a graph element has finite fractional energy. -/
theorem memGagliardo_toLp (u : W^{s,p}(Ω; F)) :
    MemGagliardo n s Ω (toLp n s Ω u) (p := p) :=
  ⟨Lp.memLp _, toLp_mem_domain u⟩

/-- Rebuilding a graph element from its function representative gives it back. -/
@[simp]
theorem ofFunction_toLp (u : W^{s,p}(Ω; F))
    (hu : MemGagliardo n s Ω (toLp n s Ω u) (p := p)) :
    ofFunction (toLp n s Ω u) hu = u :=
  toLp_injective (Lp.ext (toLp_ofFunction_apply_ae _ hu))

end SobolevSpace.Fractional.GagliardoSpace
