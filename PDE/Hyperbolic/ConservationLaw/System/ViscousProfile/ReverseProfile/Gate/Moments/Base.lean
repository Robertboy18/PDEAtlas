/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.Concrete

import PDE.Analysis.Calculus.LocalExtension.Zero
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.Regularity
import CAS.ExactTactic

/-!
# One fixed gate from the supplied clock moments

The bump family and signed coefficients are inputs. Their sum is divided by
one fixed positive weight on the open gate and extended by zero. The
local extension theorem gives smoothness; the closed support stays inside the
same finite union of bump supports.

For the clock, the downward integral derivative gives smoothness of
`wMinus` on the gate. Identities for `R` and `Q` then transfer the
supplied moments to the three unnormalized integral weights.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

open Gate.Weights

/-- The local three-moment calculation used by the concrete clock application.
The indicator is explicit, and the supplied coefficients need not be positive. -/
private theorem fixed_base_gate_moments (β : Fin 3 → ℝ → ℝ) (c v : Fin 3 → ℝ) (W : ℝ → Fin 3 → ℝ)
    {U : Set ℝ} {w : ℝ → ℝ} (hU : IsOpen U) (hβsmooth : ∀ j, ContDiff ℝ ∞ (β j))
    (hβcompact : ∀ j, HasCompactSupport (β j)) (hβU : ∀ j, tsupport (β j) ⊆ U)
    (hβint : ∀ j i, Integrable (fun x ↦ β j x * W x i)) (hw : ContDiffOn ℝ ∞ w U)
    (hwpos : ∀ x ∈ U, 0 < w x) (hc : (fun i : Fin 3 ↦ ∫ x, (∑ j, c j * β j x) * W x i) = v) :
    let b : ℝ → ℝ := U.indicator (fun x ↦ (∑ j, c j * β j x) / w x)
    ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ (⋃ j, tsupport (β j)) ∧ tsupport b ⊆ U ∧
      (∀ x ∈ U, b x = (∑ j, c j * β j x) / w x) ∧
      (∀ x ∉ U, b x = 0) ∧
      (∀ x, w x * b x = ∑ j, c j * β j x) ∧
      ∀ i, Integrable (fun x ↦ b x * (w x * W x i)) ∧
        (∫ x, b x * (w x * W x i)) = v i := by
  classical
  let f : ℝ → ℝ := fun x ↦ ∑ j, c j * β j x
  let b : ℝ → ℝ := U.indicator (fun x ↦ f x / w x)
  let K : Set ℝ := ⋃ j, tsupport (β j)
  have hf : ContDiff ℝ ∞ f := ContDiff.sum (fun j _ ↦ contDiff_const.mul (hβsmooth j))
  have hterm (j : Fin 3) : HasCompactSupport (fun x ↦ c j * β j x) := (hβcompact j).mul_left
  have hfc : HasCompactSupport f := by
    have heq : (∑ j, fun x ↦ c j * β j x) = f := by
      funext x
      simp only [Finset.sum_apply, f]
    rw [← heq]
    exact HasCompactSupport.finset_sum (fun j _ ↦ hterm j)
  have hKclosed : IsClosed K := isClosed_iUnion_of_finite (fun j ↦ isClosed_tsupport (β j))
  have hfK : tsupport f ⊆ K := by
    refine closure_minimal ?_ hKclosed
    intro x hx
    by_contra hxK
    have hzero : ∀ j, β j x = 0 :=
      fun j ↦ image_eq_zero_of_notMem_tsupport (fun hj ↦ hxK (Set.mem_iUnion.mpr ⟨j, hj⟩))
    change f x ≠ 0 at hx
    exact hx (by simp only [f, hzero, mul_zero, Finset.sum_const_zero])
  have hfU : tsupport f ⊆ U := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hfK hx)
    exact hβU j hj
  have hs : Function.support b ⊆ Function.support f := by
    simpa only [b, Set.support_indicator, Function.support_div] using
      (Set.inter_subset_right.trans Set.inter_subset_left :
        U ∩ (Function.support f ∩ Function.support w) ⊆ Function.support f)
  have hts : tsupport b ⊆ tsupport f := closure_mono hs
  have hbc : HasCompactSupport b := hfc.mono hs
  have hquot : ContDiffOn ℝ ∞ (fun x ↦ f x / w x) U :=
    hf.contDiffOn.div hw (fun x hx ↦ ne_of_gt (hwpos x hx))
  have hb : ContDiff ℝ ∞ b := hquot.indicator_of_tsupport_subset hU (hts.trans hfU)
  have hon (x : ℝ) (hx : x ∈ U) : b x = f x / w x := Set.indicator_of_mem hx _
  have hoff (x : ℝ) (hx : x ∉ U) : b x = 0 := Set.indicator_of_notMem hx _
  have hwb (x : ℝ) : w x * b x = f x := by
    by_cases hx : x ∈ U
    · rw [hon x hx]
      exact mul_div_cancel₀ (f x) (ne_of_gt (hwpos x hx))
    · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hfU h))
      rw [hoff x hx, mul_zero, hfx]
  have hfint (i : Fin 3) : Integrable (fun x ↦ f x * W x i) := by
    simpa only [f, Finset.sum_mul, mul_assoc] using
      (integrable_finsetSum Finset.univ (fun j _ ↦ (hβint j i).const_mul (c j)))
  have heq (i : Fin 3) : (fun x ↦ b x * (w x * W x i)) = (fun x ↦ f x * W x i) := by
    funext x
    rw [← mul_assoc, mul_comm (b x) (w x), hwb x]
  refine ⟨hb, hbc, hts.trans hfK, hts.trans hfU, hon, hoff, hwb, fun i ↦ ?_⟩
  constructor
  · rw [heq i]
    exact hfint i
  · calc
      (∫ x, b x * (w x * W x i)) = ∫ x, f x * W x i := congrArg (fun F : ℝ → ℝ ↦ ∫ x, F x) (heq i)
      _ = v i := congrFun hc i

/-- The same supplied bumps and coefficients give one smooth compactly supported
gate with the prescribed moments against the integral weights. The small
support interval and the entire upward contribution to the third weight are
retained. This statement identifies integrals, not shooting derivatives. -/
theorem fixed_base_clock_gate_of_selected_moments (base upTime terminalTime speedConstant : ℝ)
    (β : Fin 3 → ℝ → ℝ) (c v : Fin 3 → ℝ) (hβsmooth : ∀ j, ContDiff ℝ ∞ (β j))
    (hβcompact : ∀ j, HasCompactSupport (β j))
    (hβsupport : ∀ j, tsupport (β j) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100))
    (hβint : let D := clockPassageData base upTime terminalTime speedConstant; ∀ j i,
      Integrable (fun y ↦ β j y * (![1, D.R y, D.Q y] : Fin 3 → ℝ) i))
    (hc : let D := clockPassageData base upTime terminalTime speedConstant;
      (fun i : Fin 3 ↦ ∫ y, (∑ j, c j * β j y) * (![1, D.R y, D.Q y] : Fin 3 → ℝ) i) = v) :
    let D := clockPassageData base upTime terminalTime speedConstant
    let b : ℝ → ℝ := (Ioo (205 : ℝ) (2051 / 10)).indicator
      (fun y ↦ (∑ j, c j * β j y) / D.wMinus y)
    ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ (⋃ j, tsupport (β j)) ∧
      tsupport b ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100) ∧
      (∀ y, D.wMinus y * b y = ∑ j, c j * β j y) ∧
      ∀ i : Fin 3,
        Integrable (fun y ↦ b y * (![D.wMinus y, D.wPlus y,
          D.wPlus y * D.qPlus y + D.wMinus y * D.qMinus y] : Fin 3 → ℝ) i) ∧
        (∫ y, b y * (![D.wMinus y, D.wPlus y,
          D.wPlus y * D.qPlus y + D.wMinus y * D.qMinus y] : Fin 3 → ℝ) i) =
          v i := by
  classical
  let D := clockPassageData base upTime terminalTime speedConstant
  let U : Set ℝ := Ioo (205 : ℝ) (2051 / 10)
  let W : ℝ → Fin 3 → ℝ := fun y ↦ ![1, D.R y, D.Q y]
  let P : ℝ → Fin 3 → ℝ := fun y ↦ ![D.wMinus y, D.wPlus y,
    D.wPlus y * D.qPlus y + D.wMinus y * D.qMinus y]
  let b : ℝ → ℝ := U.indicator (fun y ↦ (∑ j, c j * β j y) / D.wMinus y)
  have hreg : GateRegularity D U :=
    gateRegularity_clockPassageData base upTime terminalTime speedConstant
  have hg : ContDiffOn ℝ ∞ D.g U := MiddleClock.contDiff_g.contDiffOn
  -- The imported FTC formula still comes from the full cutoff integral.
  have htime : ContDiffOn ℝ ∞ D.tMinus U := by
    simpa using hreg.contDiffOn_tMinus (n := (⊤ : ℕ∞)) hg
  have hw : ContDiffOn ℝ ∞ D.wMinus U := by
    unfold PassageData.wMinus
    exact (contDiffOn_const.mul (contDiffOn_const.sub htime)).exp.div
      (contDiffOn_const.sub hg) (fun y hy ↦ hreg.down_ne hy)
  have hwpos : ∀ y ∈ U, 0 < D.wMinus y := by
    intro y hy
    have hbound := MiddleClock.g_mem_Icc_gate ⟨hy.1.le, hy.2.le⟩
    have hd : 0 < 4 - D.g y := by
      change 0 < 4 - MiddleClock.g y
      linarith only [hbound.2]
    exact div_pos (Real.exp_pos _) hd
  have hsubset : Ioo (20501 / 100 : ℝ) (20509 / 100) ⊆ U :=
    fun y hy ↦ ⟨(by cas : (205 : ℝ) < 20501 / 100).trans hy.1,
      hy.2.trans (by cas : (20509 / 100 : ℝ) < 2051 / 10)⟩
  obtain ⟨hb, hbc, hbK, _, _, hoff, hwb, hmoment⟩ :=
    fixed_base_gate_moments β c v W (U := U) (w := D.wMinus)
      hreg.isOpen hβsmooth hβcompact (fun j ↦ (hβsupport j).trans hsubset) hβint hw hwpos hc
  have hbsmall : tsupport b ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100) := by
    intro y hy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hbK hy)
    exact hβsupport j hj
  -- Only gate identities are used; the indicator supplies the equality off U.
  have hP (y : ℝ) (hy : y ∈ U) (i : Fin 3) : P y i = D.wMinus y * W y i := by
    fin_cases i
    · change D.wMinus y = D.wMinus y * 1
      exact (mul_one _).symm
    · change D.wPlus y = D.wMinus y * D.R y
      rw [hreg.R_eq_weight_ratio hy, mul_div_cancel₀ _ (hreg.wMinus_ne hy)]
    · change D.wPlus y * D.qPlus y + D.wMinus y * D.qMinus y = D.wMinus y * D.Q y
      rw [hreg.Q_eq_normalized_weight hy, mul_div_cancel₀ _ (hreg.wMinus_ne hy)]
  have heq (i : Fin 3) : (fun y ↦ b y * P y i) = (fun y ↦ b y * (D.wMinus y * W y i)) := by
    funext y
    by_cases hy : y ∈ U
    · rw [hP y hy i]
    · have hby : b y = 0 := hoff y hy
      rw [hby, zero_mul, zero_mul]
  refine ⟨hb, hbc, hbK, hbsmall, hwb, fun i ↦ ?_⟩
  change Integrable (fun y ↦ b y * P y i) ∧ (∫ y, b y * P y i) = v i
  rw [heq i]
  exact hmoment i

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
