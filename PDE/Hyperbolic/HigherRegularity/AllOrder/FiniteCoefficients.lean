/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Compatibility.Classical

/-!
# Spatial wave loads from finite classical regularity

Coefficients of class `C^k` up to the boundary define the full spatial load
`H^{r+2} → H^r` for `r < k`. The load agrees with the original variational
operator, including drift and potential. Its extension by zero to unused
orders matches the recursive wave compatibility condition.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal

variable {n k : ℕ} {Ω : Set (ℝ^n)}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  {A : ℝ^n → Fin n → Fin n → ℝ} {B : Fin n → ℝ^n → ℝ} {C : ℝ^n → ℝ}
  (hA : ∀ i j, ContDiffUpToBoundary k (fun x ↦ A x i j) Ω)
  (hB : ∀ i, ContDiffUpToBoundary k (B i) Ω)
  (hC : ContDiffUpToBoundary k C Ω)

/-- The full classical wave load at each order below the coefficient regularity.
The value is zero at higher orders, which are unused by finite compatibility. -/
def classicalWaveLoadUpTo (r : ℕ) : W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω) :=
  if hr : r < k then
    higherFullLoadCLM r hopen
      (fun i j ↦ ((hA i j).of_le (Nat.succ_le_of_lt hr)).toWkpSpaceOn hopen hbounded ∞)
      (fun i ↦ ((hB i).of_le (Nat.succ_le_of_lt hr)).toWkpSpaceOn hopen hbounded ∞)
      ((hC.of_le (Nat.succ_le_of_lt hr)).toWkpSpaceOn hopen hbounded ∞)
  else 0

/-- At every available order, the finite classical load represents the original
weak wave form on zero-boundary data. -/
theorem classicalWaveForm_eq_loadUpTo (hk : 1 ≤ k) (r : ℕ) (hr : r < k) (G : W^{(r + 2),2}(Ω))
    (g : H¹₀(Ω)) (hbase : wkpBaseCoordinateCLM G = baseCoordCLM g) :
    classicalAutonomousWaveForm hopen hbounded (fun i j ↦ (hA i j).of_le hk)
      (fun i ↦ (hB i).of_le hk) (hC.of_le (Nat.zero_le k)) g = loadFunctional
      (wkpBaseCoordinateCLM (classicalWaveLoadUpTo hopen hbounded hA hB hC r G)) := by
  ext v
  have hb (b : Fin n → DerivLp n ∞ Ω) :
      multiplicationFirstOrderOperator b = fun i ↦ mulLpLeft (b i) := by
    funext i
    rfl
  simpa only [classicalAutonomousWaveForm, classicalWaveLoadUpTo, dite_eq_left hr,
    ContDiffUpToBoundary.toWkpSpaceOn_base_eq_toLp, ContDiffUpToBoundary.toLp,
    hb, multiplicationZeroOrderOperator,
    loadFunctional_apply] using fullDivergenceForm_eq_higherFullLoad r hopen
      (fun i j ↦ ((hA i j).of_le (Nat.succ_le_of_lt hr)).toWkpSpaceOn hopen hbounded ∞)
      (fun i ↦ ((hB i).of_le (Nat.succ_le_of_lt hr)).toWkpSpaceOn hopen hbounded ∞)
      ((hC.of_le (Nat.succ_le_of_lt hr)).toWkpSpaceOn hopen hbounded ∞) G g hbase v

/-- For smooth coefficients, finite and all-order loads agree at every order
where the finite load is used. -/
theorem classicalWaveLoadUpTo_eq_classicalWaveLoad
    (hA : ∀ j : ℕ, ∀ i l, ContDiffUpToBoundary j (fun x ↦ A x i l) Ω)
    (hB : ∀ j : ℕ, ∀ i, ContDiffUpToBoundary j (B i) Ω)
    (hC : ∀ j : ℕ, ContDiffUpToBoundary j C Ω) (r : ℕ) (hr : r < k) :
    classicalWaveLoadUpTo hopen hbounded (hA k) (hB k) (hC k) r =
      classicalWaveLoad hopen hbounded hA hB hC r := by
  simp only [classicalWaveLoadUpTo, dite_eq_left hr, classicalWaveLoad]

end Hyperbolic.HigherRegularity
