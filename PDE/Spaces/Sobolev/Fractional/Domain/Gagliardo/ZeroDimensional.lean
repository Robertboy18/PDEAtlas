/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Graph

/-!
# The Gagliardo space in dimension zero

There are no distinct points in `ℝ^0`, so every difference quotient vanishes.
The graph norm is therefore exactly the `L^p` norm, for any subset, any
real order, and every `1 ≤ p ≤ ∞`. The codomain can be any real normed space.
This identifies the intrinsic graph with its base function space.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.Fractional

variable {s : ℝ} {Ω : Set (ℝ^0)}
  {p : ℝ≥0∞} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- On a zero-dimensional Euclidean space every difference quotient is zero. -/
theorem diffQuot_zero_dimensional (u : ℝ^0 → F) :
    (fun z ↦ diffQuot 0 s u z (p := p)) = 0 := by
  funext z
  simp only [diffQuot, Subsingleton.elim z.1 z.2, sub_self, smul_zero, Pi.zero_apply]

/-- In dimension zero the Gagliardo condition is just `L^p` membership. -/
@[simp]
theorem memGagliardo_zero_dimensional_iff (u : ℝ^0 → F) :
    MemGagliardo 0 s Ω u (p := p) ↔ MemLp u p (volume.restrict Ω) := by
  simp only [MemGagliardo, diffQuot_zero_dimensional, MemLp.zero, and_true]

variable [Fact (1 ≤ p)]

namespace GagliardoSpace

/-- The second graph coordinate vanishes in dimension zero. -/
@[simp]
theorem differenceQuotient_zero_dimensional
    (u : GagliardoSpace 0 s Ω (p := p) (F := F)) :
    differenceQuotient 0 s Ω u = 0 := by
  apply Lp.ext
  filter_upwards [differenceQuotient_apply_ae u,
    Lp.coeFn_zero F p (gagliardoProductMeasure 0 Ω)] with z hz hz₀
  rw [hz, hz₀]
  exact congrFun (diffQuot_zero_dimensional (p := p) (s := s) (toLp 0 s Ω u)) z

/-- With no difference-quotient contribution, the graph norm equals the base norm. -/
theorem norm_toLp_zero_dimensional
    (u : GagliardoSpace 0 s Ω (p := p) (F := F)) :
    ‖toLp 0 s Ω u‖ = ‖u‖ := by
  calc
    ‖toLp 0 s Ω u‖ =
        ‖WithLp.toLp p (toLp 0 s Ω u, (0 : Lp F p (gagliardoProductMeasure 0 Ω)))‖ :=
      (WithLp.norm_toLp_fst p _ _ _).symm
    _ = ‖u‖ := by
      change ‖WithLp.toLp p (u.1.fst, 0)‖ = ‖u.1‖
      rw [← show u.1.snd = 0 from differenceQuotient_zero_dimensional u]
      rfl

/-- Every `L^p` class on a subset of `ℝ^0` has zero difference quotient. -/
theorem toLp_surjective_zero_dimensional :
    Function.Surjective (toLp 0 s Ω (p := p) (F := F)) := by
  intro u
  have hu : u ∈ gagliardoDomain 0 s Ω (p := p) (F := F) := by
    change MemLp (fun z ↦ diffQuot 0 s u z (p := p)) p (gagliardoProductMeasure 0 Ω)
    rw [diffQuot_zero_dimensional]
    exact MemLp.zero
  exact ⟨ofLp u hu, toLp_ofLp u hu⟩

/-- The zero-dimensional Gagliardo graph is isometrically `L^p` on the same domain. -/
def equivLpZeroDimensional (s : ℝ) (Ω : Set (ℝ^0)) :
    GagliardoSpace 0 s Ω (p := p) (F := F) ≃ₗᵢ[ℝ] Lp F p (volume.restrict Ω) :=
  LinearIsometryEquiv.ofSurjective
    { (toLp 0 s Ω).toLinearMap with
      norm_map' := norm_toLp_zero_dimensional }
    toLp_surjective_zero_dimensional

/-- The isometry preserves the physical `L^p` class. -/
@[simp]
theorem equivLpZeroDimensional_apply (u : GagliardoSpace 0 s Ω (p := p) (F := F)) :
    equivLpZeroDimensional s Ω u = toLp 0 s Ω u :=
  rfl

/-- The inverse isometry reconstructs the graph element with the prescribed `L^p` class. -/
@[simp]
theorem toLp_equivLpZeroDimensional_symm (u : Lp F p (volume.restrict Ω)) :
    toLp 0 s Ω ((equivLpZeroDimensional s Ω).symm u) = u :=
  (equivLpZeroDimensional s Ω).apply_symm_apply u

end GagliardoSpace
end SobolevSpace.Fractional
