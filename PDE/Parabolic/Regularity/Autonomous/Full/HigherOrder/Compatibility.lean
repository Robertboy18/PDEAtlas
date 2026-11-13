/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Forcing
public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad

/-!
# Derived initial data and parabolic compatibility

The initial derivative is constructed as `f(a) - Lg` in the required odd
Sobolev order. Repeating this operation with the tail forcing tuple constructs
all subsequent initial derivatives. Compatibility asks only that these derived
fields have zero boundary trace, through the final initial datum of order one. These
are the compatibility conditions of Evans's §7.1.3, Theorem 6; by the remark after that
theorem they say that each derived datum vanishes on the boundary in the trace sense.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, Theorem 6 (Higher regularity) and the remark after
  it, p. 386, and (57), p. 387.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {a b : ℝ}

/-- The next initial datum, derived from the forcing trace and spatial load.
The datum `g ∈ H^{2m+3}` enters `L` at its own order `2m+3`. -/
def initialDerivative
    (L : ∀ r : ℕ, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω))
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b)
    {m : ℕ} (F : ForcingJet n Ω a b (m + 1)) (hF : F.HasWeakDerivatives)
    (g : W^{(2 * (m + 1) + 1),2}(Ω)) :
    W^{(2 * m + 1),2}(Ω) :=
  F.trace hopen hbounded hgraph hab hF a -
    L (2 * m + 1) (lowerOrderCLM (show 2 * m + 1 + 2 ≤ 2 * (m + 1) + 1 by omega) g)

/-- The derived datum and remaining forcing are bounded by the original
data. The coefficient depends only on the spatial load and trace operator. -/
theorem initialDerivative_norm_add_tail_le
    (L : ∀ r : ℕ, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω))
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b)
    {m : ℕ} (F : ForcingJet n Ω a b (m + 1)) (hF : F.HasWeakDerivatives)
    (g : W^{(2 * (m + 1) + 1),2}(Ω)) :
    ‖initialDerivative L hopen hbounded hgraph hab F hF g‖ + F.2.normSum ≤
      (ForcingJet.traceConstant m hopen hbounded hgraph hab + ‖L (2 * m + 1)‖ + 1) *
        (‖g‖ + F.normSum) := by
  let C := ForcingJet.traceConstant m hopen hbounded hgraph hab
  have hC : 0 ≤ C := ForcingJet.traceConstant_nonneg m hopen hbounded hgraph hab
  have htrace := (F.trace_spec hopen hbounded hgraph hab hF).2.2 a ⟨le_rfl, hab.le⟩
  have hload :
      ‖L (2 * m + 1)
        (lowerOrderCLM (show 2 * m + 1 + 2 ≤ 2 * (m + 1) + 1 by omega) g)‖ ≤
        ‖L (2 * m + 1)‖ * ‖g‖ :=
    ((L (2 * m + 1)).le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (norm_lowerOrderCLM_apply_le _ g) (L (2 * m + 1)).opNorm_nonneg)
  have htail := F.2.norm_head_le_normSum
  have htailNonneg := F.2.normSum_nonneg
  have hdata : F.normSum = ‖F.1‖ + F.2.normSum := rfl
  have hnorm := norm_sub_le (F.trace hopen hbounded hgraph hab hF a)
    (L (2 * m + 1)
      (lowerOrderCLM (show 2 * m + 1 + 2 ≤ 2 * (m + 1) + 1 by omega) g))
  change ‖F.trace hopen hbounded hgraph hab hF a -
    L (2 * m + 1)
      (lowerOrderCLM (show 2 * m + 1 + 2 ≤ 2 * (m + 1) + 1 by omega) g)‖ +
        F.2.normSum ≤ _
  dsimp only [C] at hC
  rw [hdata]
  nlinarith only [hnorm, htrace, hload, htail, htailNonneg, hC,
    norm_nonneg g, norm_nonneg F.1, (L (2 * m + 1)).opNorm_nonneg]

/-- The compatibility conditions of Evans's §7.1.3, Theorem 6, with every higher initial
datum derived recursively. At order zero the only condition is `g ∈ H¹₀`. -/
def Compatible
    (L : ∀ r : ℕ, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω))
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b) :
    {m : ℕ} → (F : ForcingJet n Ω a b m) → F.HasWeakDerivatives →
      W^{(2 * m + 1),2}(Ω) → Prop
  | 0, _, _, g => ∃ g₀ : H¹₀(Ω), wkpBaseCoordinateCLM g = baseCoordCLM g₀
  | _ + 1, F, hF, g =>
      (∃ g₀ : H¹₀(Ω), wkpBaseCoordinateCLM g = baseCoordCLM g₀) ∧
        Compatible L hopen hbounded hgraph hab F.2 hF.2
          (initialDerivative L hopen hbounded hgraph hab F hF g)

/-- Every compatible initial datum has zero boundary trace. -/
theorem Compatible.zeroBoundary
    {L : ∀ r : ℕ, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω)}
    {hopen : IsOpen Ω} {hbounded : Bornology.IsBounded Ω}
    {hgraph : Boundary.HasContDiffGraphBoundary 2 Ω} {hab : a < b}
    {m : ℕ} {F : ForcingJet n Ω a b m} {hF : F.HasWeakDerivatives}
    {g : W^{(2 * m + 1),2}(Ω)}
    (h : Compatible L hopen hbounded hgraph hab F hF g) :
    ∃ g₀ : H¹₀(Ω), wkpBaseCoordinateCLM g = baseCoordCLM g₀ := by
  cases m with
  | zero => exact h
  | succ m => exact h.1

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder
