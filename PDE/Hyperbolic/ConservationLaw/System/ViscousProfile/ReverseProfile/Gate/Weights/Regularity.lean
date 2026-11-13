/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.Derivatives

/-!
# Second-order regularity of the integral shooting weights

On an open gate, the first-derivative formulas identify the passage
and moment derivatives with quotients involving only the clock. A `C¹` clock
therefore makes these primitives `C²`. A `C²` clock also makes their rational
prefactors `C²`, giving `C²` regularity of the weights `R` and `Q`.

The lower cutoff remains inside the downward integrals. Its continuity and vanishing on the gate
suffice through the imported FTC formulas.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace Gate.Weights
namespace GateRegularity

variable {D : PassageData} {I : Set ℝ} (h : GateRegularity D I)

include h

/-- The upward passage time gains one derivative from its gate integrand. -/
theorem contDiffOn_tPlus (hg : ContDiffOn ℝ 1 D.g I) :
    ContDiffOn ℝ 2 D.tPlus I := by
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) h.isOpen).2
    ⟨fun y hy ↦ (h.hasDerivAt_tPlus hy).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
  have hquot : ContDiffOn ℝ 1 (fun y ↦ 1 / (D.g y + 1)) I :=
    contDiffOn_const.div (hg.add contDiffOn_const) (fun y hy ↦ h.up_ne hy)
  exact hquot.congr fun y hy ↦ (h.hasDerivAt_tPlus hy).deriv

/-- The downward passage time gains one derivative on the gate, at every finite
order and at infinite order. The lower cutoff need only be continuous. -/
theorem contDiffOn_tMinus {n : ℕ∞} (hg : ContDiffOn ℝ n D.g I) :
    ContDiffOn ℝ ((n : ℕ∞ω) + 1) D.tMinus I := by
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := (n : ℕ∞ω)) h.isOpen).2
    ⟨fun y hy ↦ (h.hasDerivAt_tMinus hy).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
  have hquot : ContDiffOn ℝ n (fun y ↦ -(1 / (4 - D.g y))) I :=
    (contDiffOn_const.div (contDiffOn_const.sub hg) (fun y hy ↦ h.down_ne hy)).neg
  exact hquot.congr fun y hy ↦ (h.hasDerivAt_tMinus hy).deriv

/-- The downward moment gains one derivative using its gate derivative formula. -/
theorem contDiffOn_downMoment (hg : ContDiffOn ℝ 1 D.g I) :
    ContDiffOn ℝ 2 D.downMoment I := by
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) h.isOpen).2
    ⟨fun y hy ↦ (h.hasDerivAt_downMoment hy).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
  have hquot : ContDiffOn ℝ 1 (fun y ↦ y / (4 - D.g y) ^ 2) I :=
    contDiffOn_id.div ((contDiffOn_const.sub hg).pow 2) (fun y hy ↦ pow_ne_zero 2 (h.down_ne hy))
  exact hquot.congr fun y hy ↦ (h.hasDerivAt_downMoment hy).deriv

/-- The anchored upward moment is `C²` on the gate. -/
theorem contDiffOn_upMoment (hg : ContDiffOn ℝ 1 D.g I) :
    ContDiffOn ℝ 2 D.upMoment I := by
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) h.isOpen).2
    ⟨fun y hy ↦ (h.hasDerivAt_upMoment hy).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
  have hquot : ContDiffOn ℝ 1 (fun y ↦ y / (D.g y + 1) ^ 2) I :=
    contDiffOn_id.div ((hg.add contDiffOn_const).pow 2) (fun y hy ↦ pow_ne_zero 2 (h.up_ne hy))
  exact hquot.congr fun y hy ↦ (h.hasDerivAt_upMoment hy).deriv

/-- The downward logarithmic speed weight inherits `C²` regularity from the clock. -/
theorem contDiffOn_qMinus (hg : ContDiffOn ℝ 2 D.g I) :
    ContDiffOn ℝ 2 D.qMinus I := by
  have hm := h.contDiffOn_downMoment (hg.of_le (by decide : (1 : ℕ∞ω) ≤ 2))
  unfold PassageData.qMinus
  exact (contDiffOn_const.mul hm).sub
    (contDiffOn_id.div (contDiffOn_const.sub hg) (fun y hy ↦ h.down_ne hy))

/-- The upward logarithmic speed weight retains its anchor constant and is `C²`. -/
theorem contDiffOn_qPlus (hg : ContDiffOn ℝ 2 D.g I) :
    ContDiffOn ℝ 2 D.qPlus I := by
  have hm := h.contDiffOn_upMoment (hg.of_le (by decide : (1 : ℕ∞ω) ≤ 2))
  unfold PassageData.qPlus
  exact (contDiffOn_const.add (contDiffOn_const.mul hm)).add
    (contDiffOn_id.div (hg.add contDiffOn_const) (fun y hy ↦ h.up_ne hy))

/-- The value-weight ratio is `C²` on the gate. -/
theorem contDiffOn_R (hg : ContDiffOn ℝ 2 D.g I) :
    ContDiffOn ℝ 2 D.R I := by
  have hg1 : ContDiffOn ℝ 1 D.g I := hg.of_le (by decide : (1 : ℕ∞ω) ≤ 2)
  have htime : ContDiffOn ℝ 2 (fun y ↦ Real.exp (-4 * (D.tMinus y - D.tPlus y))) I :=
    (contDiffOn_const.mul ((h.contDiffOn_tMinus (n := 1) hg1).sub (h.contDiffOn_tPlus hg1))).exp
  unfold PassageData.R
  exact ((contDiffOn_const.sub hg).div (hg.add contDiffOn_const) (fun y hy ↦ h.up_ne hy)).mul htime

/-- The normalized speed weight is `C²` on the gate. -/
theorem contDiffOn_Q (hg : ContDiffOn ℝ 2 D.g I) :
    ContDiffOn ℝ 2 D.Q I := by
  unfold PassageData.Q
  exact (h.contDiffOn_qMinus hg).add ((h.contDiffOn_R hg).mul (h.contDiffOn_qPlus hg))

end GateRegularity
end Gate.Weights
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
