/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Quasilinear.Diagonal.Gradient.Weight
public import PDE.Analysis.Calculus.Transport.Differentiation
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The weighted spatial slope along a characteristic

Differentiating the diagonal PDE creates a mixed quadratic term. The signed
spatial integrating factor cancels that term, leaving a scalar Riccati equation.
Both derivatives used here come from the PDE and the candidate's C² jet.
-/

@[expose] public noncomputable section

open Set
open PDE.Analysis PDE.Analysis.Transport

namespace PDE.Hyperbolic.Quasilinear.Diagonal

variable {B : Fin 2 → (Fin 2 → ℝ) → ℝ}
  {v : ℝ × ℝ → Fin 2 → ℝ} {s : Set (ℝ × ℝ)}

/-- Holding one component fixed reconstructs a two-component state by updating
the other component. -/
theorem update_rev_eq_of_apply_eq {z w : Fin 2 → ℝ} (i : Fin 2) (h : z i = w i) :
    Function.update z i.rev (w i.rev) = w := by
  ext j
  fin_cases i <;> fin_cases j <;> simp_all

/-- The negative spatial slope weighted along the other invariant. -/
def weightedSlope (B : Fin 2 → (Fin 2 → ℝ) → ℝ)
    (hv : ContinuousSecondJetOn v s) (i : Fin 2) (z : Fin 2 → ℝ)
    (α : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(spatialWeight B i z (v (t, α t) i.rev) * hv.first (t, α t) (0, 1) i)

/-- The weighted slope satisfies a scalar Riccati equation. The
characteristic and fixed-coordinate hypotheses are intermediate facts; the
lifespan theorem constructs the curve and proves its constancy from data. -/
theorem hasDerivAt_weightedSlope (hB : ∀ i, ContDiff ℝ 1 (B i)) (hgap : ∀ i z, B i z ≠ B i.rev z)
    (hv : ContinuousSecondJetOn v s) (hs : IsOpen s)
    (hpde : ∀ p ∈ s, ∀ j, fderiv ℝ v p (1, B j (v p)) j = 0) (i : Fin 2) (z : Fin 2 → ℝ) {α : ℝ → ℝ}
    {t : ℝ} (ht : (t, α t) ∈ s) (hconst : z i = v (t, α t) i)
    (hα : HasDerivAt α (B i (v (t, α t))) t) :
    HasDerivAt (weightedSlope B hv i z α) ((fderiv ℝ (B i) (v (t, α t)) (Pi.single i 1) /
      spatialWeight B i z (v (t, α t) i.rev)) * weightedSlope B hv i z α t ^ 2) t := by
  let p := (t, α t)
  let A := hv.first p (0, 1)
  have ha := hasDerivAt_spatial_slope_along_characteristic hv hs
    (fun j ↦ (hB j).differentiable (by simp)) hpde ht i hα
  have hq := hasDerivAt_value_along_characteristic hv hs hpde ht i i.rev hα
  have hw : HasDerivAt (fun r ↦ spatialWeight B i z (v (r, α r) i.rev))
      ((transverseRatio B i (v p) * spatialWeight B i z (v p i.rev)) *
        ((B i (v p) - B i.rev (v p)) * A i.rev)) t := by
    have hu : Function.update z i.rev (v p i.rev) = v p := update_rev_eq_of_apply_eq i hconst
    simpa only [Function.comp_def, hu] using
      (hasDerivAt_spatialWeight hB hgap i z (v p i.rev)).comp t hq
  have hdecomp : A = A i • Pi.single i 1 + A i.rev • Pi.single i.rev 1 := by
    ext j
    fin_cases i <;> fin_cases j <;> simp
  have hvalue : fderiv ℝ (B i) (v p) A = A i * fderiv ℝ (B i) (v p) (Pi.single i 1) +
        A i.rev * fderiv ℝ (B i) (v p) (Pi.single i.rev 1) := by
    conv_lhs => rw [hdecomp]
    simp only [map_add, map_smul, smul_eq_mul]
  have hne : B i (v p) - B i.rev (v p) ≠ 0 := sub_ne_zero.mpr (hgap i (v p))
  have hwne : spatialWeight B i z (v p i.rev) ≠ 0 := (spatialWeight_pos i z (v p i.rev)).ne'
  change HasDerivAt (fun r ↦ -(spatialWeight B i z (v (r, α r) i.rev) *
    hv.first (r, α r) (0, 1) i)) _ t
  refine (hw.mul ha).neg.congr_deriv ?_
  change -((fderiv ℝ (B i) (v p) (Pi.single i.rev 1) /
    (B i (v p) - B i.rev (v p)) * spatialWeight B i z (v p i.rev) *
      ((B i (v p) - B i.rev (v p)) * A i.rev)) * A i +
    spatialWeight B i z (v p i.rev) * (-(fderiv ℝ (B i) (v p) A) * A i)) =
      (fderiv ℝ (B i) (v p) (Pi.single i 1) / spatialWeight B i z (v p i.rev)) *
        (-(spatialWeight B i z (v p i.rev) * A i)) ^ 2
  rw [hvalue]
  field_simp
  ring

end PDE.Hyperbolic.Quasilinear.Diagonal
