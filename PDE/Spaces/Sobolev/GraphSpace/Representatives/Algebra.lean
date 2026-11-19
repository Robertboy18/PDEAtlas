/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation
public import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra

/-!
# Linear weak-derivative identities for stored Lp representatives

The algebra of `Lp` elements agrees almost everywhere with pointwise algebra.
These lemmas move the weak-derivative identities across that agreement, so sums
and differences can be used directly in Sobolev constructions.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}
  {α : List (Fin n)} {f df g dg : DerivLp n p Ω}

/-- Addition of two stored weak-derivative pairs. -/
theorem hasWeakDerivativeOn_lp_add
    (hf : HasWeakDerivativeOn Ω α (f : ℝ^n → ℝ) (df : ℝ^n → ℝ))
    (hg : HasWeakDerivativeOn Ω α (g : ℝ^n → ℝ) (dg : ℝ^n → ℝ)) :
    HasWeakDerivativeOn Ω α (f + g : DerivLp n p Ω) (df + dg : DerivLp n p Ω) := by
  exact (hasWeakDerivativeOn_add hf hg).congr_ae
    (Lp.coeFn_add f g).symm (Lp.coeFn_add df dg).symm

/-- Subtraction of two stored weak-derivative pairs. -/
theorem hasWeakDerivativeOn_lp_sub
    (hf : HasWeakDerivativeOn Ω α (f : ℝ^n → ℝ) (df : ℝ^n → ℝ))
    (hg : HasWeakDerivativeOn Ω α (g : ℝ^n → ℝ) (dg : ℝ^n → ℝ)) :
    HasWeakDerivativeOn Ω α (f - g : DerivLp n p Ω) (df - dg : DerivLp n p Ω) := by
  exact (hasWeakDerivativeOn_sub α hf hg).congr_ae
    (Lp.coeFn_sub f g).symm (Lp.coeFn_sub df dg).symm

/-- One weak mixed derivative supplies the derivative with the two directions
interchanged, once the first derivatives of the common source are known. -/
theorem hasWeakDerivativeOn_mixed_of_first
    (U : W^{1,p}(Ω)) (i j : Fin n) (v : DerivLp n p Ω)
    (hv : HasWeakDerivativeOn Ω [i]
      (U.val (singleDerivIndex n j) : ℝ^n → ℝ) (v : ℝ^n → ℝ)) :
    HasWeakDerivativeOn Ω [j]
      (U.val (singleDerivIndex n i) : ℝ^n → ℝ) (v : ℝ^n → ℝ) := by
  have hfirst (k : Fin n) : HasWeakDerivativeOn Ω [k]
      (U.val (baseIndex n 1) : ℝ^n → ℝ) (U.val (singleDerivIndex n k) : ℝ^n → ℝ) := by
    simpa only [singleDerivIndex_toList] using U.property (singleDerivIndex n k)
  have hsecond := (hfirst j).append_single i hv
  have hswap : HasWeakDerivativeOn Ω [i, j]
      (U.val (baseIndex n 1) : ℝ^n → ℝ) (v : ℝ^n → ℝ) :=
    hsecond.perm (List.Perm.swap _ _ [])
  exact (hfirst i).cancel_prefix_append_single j hswap

end SobolevSpace.GraphSpace
