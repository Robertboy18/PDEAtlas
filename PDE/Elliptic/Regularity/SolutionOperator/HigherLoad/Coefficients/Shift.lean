/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical

/-!
# Constant potential shifts of full coefficients

Adding a constant to the potential realizes the usual mass shift in the
variational form and the same constant multiple in the classical
operator. Principal and drift coefficients are preserved.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Add a real constant to the potential of the full operator. -/
def shiftPotential (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω) (t : ℝ) :
    SmoothFullCoefficients n Ω where
  principal := P.principal
  drift := P.drift
  potential := fun x ↦ P.potential x + t
  principal_smooth := P.principal_smooth
  drift_smooth := P.drift_smooth
  potential_smooth k := (P.potential_smooth k).add (ContDiffUpToBoundary.const t) hopen

/-- A constant potential shift adds exactly the corresponding mass term. -/
theorem form_shiftPotential
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (t : ℝ) (u v : H¹₀(Ω)) :
    (P.shiftPotential hopen t).form hopen hbounded u v =
      P.form hopen hbounded u v + t * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ := by
  let Q := P.shiftPotential hopen t
  have hmul (f : DerivLp n 2 Ω) :
      mulLpLeft ((Q.potential_smooth 0).toLp hopen hbounded ∞) f =
        mulLpLeft ((P.potential_smooth 0).toLp hopen hbounded ∞) f + t • f := by
    apply Lp.ext
    filter_upwards [
      mulLpLeft_apply_ae ((Q.potential_smooth 0).toLp hopen hbounded ∞) f,
      mulLpLeft_apply_ae ((P.potential_smooth 0).toLp hopen hbounded ∞) f,
      (Q.potential_smooth 0).toLp_coeFn hopen hbounded ∞,
      (P.potential_smooth 0).toLp_coeFn hopen hbounded ∞,
      Lp.coeFn_add (mulLpLeft ((P.potential_smooth 0).toLp hopen hbounded ∞) f) (t • f),
      Lp.coeFn_smul t f] with x hQ hP hq hp hadd hsmul
    rw [hQ, hadd, Pi.add_apply, hP, hsmul, hq, hp]
    change (P.potential x + t) * f x = P.potential x * f x + t * f x
    ring
  change Q.form hopen hbounded u v = _
  simp only [form, fullDivergenceForm_apply]
  rw [hmul, inner_add_left, real_inner_smul_left]
  dsimp only [Q, shiftPotential]
  ring

/-- The classical differential expression has the identical constant shift. -/
theorem classicalLoad_shiftPotential
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω) (t : ℝ)
    (u : ℝ^n → ℝ) (x : ℝ^n) :
    (P.shiftPotential hopen t).classicalLoad u x =
      P.classicalLoad u x + t * u x := by
  simp only [classicalLoad, shiftPotential]
  ring

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
