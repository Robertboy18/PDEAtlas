/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearHolderTails

/-!
# The walk over heights of the horizontal estimate of `u_y`

By `shearConstant_le_iSup_envelope`, `C₂(τ)` is at most the supremum over `A > 0` of the envelope
`(X(A) + τ (U(A) + 2 (2A)^{1/2} W(A)))/√2` (`shearHolderEnvelope`). For `A` in a slab `(t₀, t₁]`,
`X(A) ≤ X(t₀)`, `U(A) ≤ U(t₁)`, `W(A) ≤ W(t₀)` and `(2A)^{1/2} ≤ (2t₁)^{1/2}`, which the slab
check `shearHolderSlabCheck` compares with the bound `c √2 π`.

The walk `shearHolderWalk` runs over slabs of heights and carries two numbers: an upper bound `U`
of the upper envelope below the current height and an upper bound `M` of the outer mass above it.
On each slab the transport cost (`shearSlabCost`) is added to `U`, the mass (`shearSlabMass`) is
removed from `M`, and the slab check is evaluated. At the end of the walk `U` and `M` are compared
with the bounds at the end height. By `shearHolderWalk_spec` the bound of `U` passes upwards, the
bound of `W` downwards, and the checks hold on every slab. `shearHolderSegment` is the walk of the
paper's values `τ = 0.582` and `c = 1.55` on the mesh `shearHolderNext`.

## Main definitions

* `shearHolderWalk`: the walk over heights from `t` to `e` with slab costs, slab masses, a mesh
  and a slab check.
* `shearHolderNext`: the mesh of heights, finest around the maximum of the envelope near
  `A = 0.85`.
* `shearMassEnvelopeHigh`: an upper bound of `X(t₀) = √2 π / (√(1 + t₀²) + t₀)^{1/2}`.
* `shearHolderSlabCheck`: the check of a slab `[t₀, t₁]` against the bound `c √2 π`.
* `shearHolderSegment`: the walk with `τ = 0.582` and the bound `1.55 √2 π`.

## Main results

* `shearHolderWalk_spec`: the walk carries the bound of `U` upwards, the bound of an antitone mass
  `W` downwards, and the slab checks hold on every slab.
* `shearMassEnvelope_le_high`: `X(A) ≤ X(t₀)` for `0 ≤ t₀ ≤ A`, `A > 0`.
* `shearHolderSlabCheck_spec`: a slab that passes the check has envelope at most `c √2 π` for
  every `A ∈ (t₀, t₁]`.
* `shearHolderSegment_spec`: a segment `(t, e]` that passes the walk has envelope at most
  `1.55 √2 π` at every height, given the bounds of `U` at `t` and of `W` at `e`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped ENNReal

namespace IncompressibleFlow.SharpHolder

/-- The walk over heights from `t` to `e` with the slab costs `cost`, the slab masses `mass`, the
next height `next`, the slab check `ok` and the end values `Ue`, `Me`. -/
def shearHolderWalk (cost mass : ℚ → ℚ → Option ℤ) (next : ℚ → ℚ)
    (ok : ℚ → ℚ → ℚ → ℚ → Bool) (Ue Me : ℚ) : ℕ → ℚ → ℚ → ℚ → ℚ → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, t, e, U, M =>
    if e ≤ t then decide (U ≤ Ue) && decide (Me ≤ M)
    else
      let t' := min (next t) e
      if t < t' then
        match cost t t', mass t t' with
        | some c, some m =>
          if 0 ≤ c ∧ 0 ≤ m then
            ok t t' (U + 4 * (c / 2 ^ 64)) M &&
              shearHolderWalk cost mass next ok Ue Me fuel t' e (U + 4 * (c / 2 ^ 64))
                (M - m / 2 ^ 64)
          else false
        | _, _ => false
      else false

/-- **Soundness of the walk over heights.** The bound of `U` is carried upwards from `t` to `e`,
the bound of a mass `W` (antitone, and split by the slab masses) downwards from `e` to `t`, and
the slab checks give `P A` for `A ∈ (t, e]`. -/
theorem shearHolderWalk_spec {cost mass : ℚ → ℚ → Option ℤ} {next : ℚ → ℚ}
    {ok : ℚ → ℚ → ℚ → ℚ → Bool} {Ue Me : ℚ} {e : ℚ} {P : ℝ → Prop} {W : ℝ → ℝ≥0∞}
    (hWa : ∀ a b : ℝ, a ≤ b → W b ≤ W a)
    (hWs : ∀ a b : ℝ, a ≤ b →
      W a ≤ (∫⁻ t in Ioc a b, ∫⁻ p in Ioi (0 : ℝ), ‖shearDifference p t‖ₑ) + W b)
    (hcost : ∀ t₀ t₁ : ℚ, ∀ c : ℤ, cost t₀ t₁ = some c →
      ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioi (0 : ℝ), shearColumnDensity p t ≤
        ENNReal.ofReal (c / 2 ^ 64))
    (hmass : ∀ t₀ t₁ : ℚ, ∀ m : ℤ, mass t₀ t₁ = some m →
      ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioi (0 : ℝ), ‖shearDifference p t‖ₑ ≤
        ENNReal.ofReal (m / 2 ^ 64))
    (hok : ∀ t₀ t₁ U M : ℚ, 0 ≤ t₀ → t₀ < t₁ → ok t₀ t₁ U M = true →
      shearUpperEnvelope t₁ ≤ ENNReal.ofReal U → W t₀ ≤ ENNReal.ofReal M →
        ∀ A ∈ Ioc (t₀ : ℝ) t₁, P A)
    (hMe0 : 0 ≤ Me) (fuel : ℕ) {t U M : ℚ} (ht : 0 ≤ t) (hU0 : 0 ≤ U)
    (h : shearHolderWalk cost mass next ok Ue Me fuel t e U M = true) :
    0 ≤ M ∧ (shearUpperEnvelope t ≤ ENNReal.ofReal U → shearUpperEnvelope e ≤ ENNReal.ofReal Ue) ∧
      (W e ≤ ENNReal.ofReal Me → W t ≤ ENNReal.ofReal M) ∧
      (shearUpperEnvelope t ≤ ENNReal.ofReal U → W e ≤ ENNReal.ofReal Me →
        ∀ A ∈ Ioc (t : ℝ) e, P A) := by
  induction fuel generalizing t U M with
  | zero =>
    simp only [shearHolderWalk, Bool.false_eq_true] at h
  | succ n ih =>
    simp only [shearHolderWalk] at h
    split_ifs at h with het hlt
    · -- the end of the walk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have het' : (e : ℝ) ≤ t := by exact_mod_cast het
      refine ⟨hMe0.trans h.2, fun hU ↦ (shearUpperEnvelope_mono het').trans
        (hU.trans (ENNReal.ofReal_le_ofReal (by exact_mod_cast h.1))), fun hMe ↦
        (hWa _ _ het').trans (hMe.trans (ENNReal.ofReal_le_ofReal
        (by exact_mod_cast h.2))), fun _ _ A hA ↦ ?_⟩
      exact absurd (hA.1.trans_le hA.2) (not_lt.2 het')
    · split at h
      · rename_i c m hc hm
        split_ifs at h with hcm
        simp only [Bool.and_eq_true] at h
        obtain ⟨hok', hrest⟩ := h
        set t' := min (next t) e
        have ht' : 0 ≤ t' := ht.trans hlt.le
        have htt' : (t : ℝ) ≤ t' := by exact_mod_cast hlt.le
        have hc' : (0 : ℝ) ≤ c / 2 ^ 64 := div_nonneg (by exact_mod_cast hcm.1) (by positivity)
        have hm' : (0 : ℝ) ≤ m / 2 ^ 64 := div_nonneg (by exact_mod_cast hcm.2) (by positivity)
        have hU0' : (0 : ℚ) ≤ U + 4 * (c / 2 ^ 64) := by
          have : (0 : ℚ) ≤ c / 2 ^ 64 := div_nonneg (by exact_mod_cast hcm.1) (by positivity)
          linarith
        obtain ⟨hM0, hUe, hWe, hP⟩ := ih ht' hU0' hrest
        -- the upper envelope at the top of the slab
        have hU' : shearUpperEnvelope t ≤ ENNReal.ofReal U →
            shearUpperEnvelope t' ≤ ENNReal.ofReal ((U + 4 * (c / 2 ^ 64) : ℚ) : ℝ) := by
          intro hU
          refine (shearUpperEnvelope_le_add (a := (t : ℝ))).trans ?_
          have hs := hcost _ _ _ hc
          calc shearUpperEnvelope t + 4 * ∫⁻ s in Ioc (t : ℝ) t', ∫⁻ p in Ioi (0 : ℝ),
                shearColumnDensity p s
              ≤ ENNReal.ofReal U + 4 * ENNReal.ofReal (c / 2 ^ 64) := by gcongr
            _ = ENNReal.ofReal ((U + 4 * (c / 2 ^ 64) : ℚ) : ℝ) := by
                rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
                  ← ENNReal.ofReal_add (by exact_mod_cast hU0) (by positivity)]
                push_cast
                ring_nf
        -- the outer mass at the bottom of the slab
        have hW : W e ≤ ENNReal.ofReal Me → W t ≤ ENNReal.ofReal M := by
          intro hMe
          refine (hWs _ _ htt').trans ?_
          have hs := hmass _ _ _ hm
          calc (∫⁻ s in Ioc (t : ℝ) t', ∫⁻ p in Ioi (0 : ℝ), ‖shearDifference p s‖ₑ) +
                W t'
              ≤ ENNReal.ofReal (m / 2 ^ 64) + ENNReal.ofReal ((M - m / 2 ^ 64 : ℚ) : ℝ) :=
                add_le_add hs (hWe hMe)
            _ = ENNReal.ofReal M := by
                rw [← ENNReal.ofReal_add hm' (by exact_mod_cast hM0)]
                push_cast
                ring_nf
        have hM0' : 0 ≤ M := by
          have : (0 : ℚ) ≤ m / 2 ^ 64 := div_nonneg (by exact_mod_cast hcm.2) (by positivity)
          linarith
        refine ⟨hM0', fun hU ↦ hUe (hU' hU), hW, fun hU hMe A hA ↦ ?_⟩
        rcases le_or_gt A t' with h' | h'
        · exact hok t t' _ M ht hlt hok' (hU' hU) (hW hMe) A ⟨hA.1, h'⟩
        · exact hP (hU' hU) hMe A ⟨h', hA.2⟩
      · simp at h

/-! ### The slab check of `u_y` -/

/-- The mesh of heights: the ratio `1/256` on `[1/4, 4]`, around the maximum of the envelope near
`A = 0.85`, the ratio `1/64` on `[4, 64]`, and `1/16` elsewhere. -/
def shearHolderNext (t : ℚ) : ℚ :=
  shearNextHeight (if t < 1 / 4 then 1 / 16 else if t < 4 then 1 / 256 else if t < 64 then 1 / 64
    else 1 / 16) t

/-- An upper bound of `X(t₀) = √2 π / (√(1 + t₀²) + t₀)^{1/2}`. -/
def shearMassEnvelopeHigh (t₀ : ℚ) : ℚ :=
  sqrtHigh 2 * (3141593 / 10 ^ 6) / sqrtLow (sqrtLow (1 + t₀ ^ 2) + t₀)

/-- For `t₀ ≥ 0` the upper bound of `X(t₀)` is positive. -/
theorem shearMassEnvelopeHigh_pos {t₀ : ℚ} (ht₀ : 0 ≤ t₀) : 0 < shearMassEnvelopeHigh t₀ := by
  have h₁ : (0 : ℚ) < 1 + t₀ ^ 2 := by positivity
  have h₂ : (0 : ℚ) < sqrtLow (1 + t₀ ^ 2) + t₀ := by linarith [sqrtLow_pos h₁]
  exact div_pos (mul_pos (sqrtHigh_pos (by norm_num)) (by norm_num)) (sqrtLow_pos h₂)

/-- `X` decreases: `X(A) ≤ X(t₀)` for `0 ≤ t₀ ≤ A`, `A > 0`. -/
theorem shearMassEnvelope_le_high {t₀ : ℚ} (ht₀ : 0 ≤ t₀) {A : ℝ} (hA : (t₀ : ℝ) ≤ A)
    (hA0 : 0 < A) : shearMassEnvelope A ≤ ENNReal.ofReal (shearMassEnvelopeHigh t₀) := by
  rw [shearMassEnvelope_eq hA0]
  refine ENNReal.ofReal_le_ofReal ?_
  have h₁ : (0 : ℚ) < 1 + t₀ ^ 2 := by positivity
  have hs : (sqrtLow (1 + t₀ ^ 2) : ℝ) ≤ Real.sqrt (1 + A ^ 2) := by
    refine (sqrtLow_le_sqrt h₁.le).trans (Real.sqrt_le_sqrt ?_)
    have : (0 : ℝ) ≤ t₀ := by exact_mod_cast ht₀
    push_cast
    nlinarith
  have h₂ : (0 : ℚ) < sqrtLow (1 + t₀ ^ 2) + t₀ := by linarith [sqrtLow_pos h₁]
  have hr0 : (0 : ℝ) < sqrtLow (sqrtLow (1 + t₀ ^ 2) + t₀) := by exact_mod_cast sqrtLow_pos h₂
  have hr : (sqrtLow (sqrtLow (1 + t₀ ^ 2) + t₀) : ℝ) ≤
      Real.sqrt (Real.sqrt (1 + A ^ 2) + A) := by
    refine (sqrtLow_le_sqrt h₂.le).trans (Real.sqrt_le_sqrt ?_)
    push_cast
    linarith
  have h2 := sqrt_le_sqrtHigh (q := 2) (by norm_num)
  have hh : (0 : ℝ) < sqrtHigh 2 := by exact_mod_cast sqrtHigh_pos (q := 2) (by norm_num)
  push_cast at h2
  have hn : Real.sqrt 2 * Real.pi ≤ (sqrtHigh 2 : ℝ) * (3141593 / 10 ^ 6) := by
    have hπ := Real.pi_lt_d6
    exact mul_le_mul h2 (by norm_num at hπ ⊢; linarith) Real.pi_pos.le hh.le
  unfold shearMassEnvelopeHigh
  push_cast
  exact div_le_div₀ (by positivity) hn hr0 hr

/-- The check of the slab `[t₀, t₁]` with the weight `τ` and the bound `c √2 π`, from the bounds
`U` of `U(t₁)` and `M` of `W(t₀)`. -/
def shearHolderSlabCheck (τ c t₀ t₁ U M : ℚ) : Bool :=
  decide (0 ≤ U ∧ 0 ≤ M ∧ shearMassEnvelopeHigh t₀ + τ * (U + 2 * sqrtHigh (2 * t₁) * M) ≤
    c * sqrtLow 2 * (3141592 / 10 ^ 6))

/-- **Soundness of the slab check.** -/
theorem shearHolderSlabCheck_spec {τ c t₀ t₁ U M : ℚ} (hτ : 0 ≤ τ) (hc : 0 ≤ c) (ht₀ : 0 ≤ t₀)
    (h : shearHolderSlabCheck τ c t₀ t₁ U M = true)
    (hU : shearUpperEnvelope t₁ ≤ ENNReal.ofReal U) (hW : shearOuterMass t₀ ≤ ENNReal.ofReal M)
    {A : ℝ} (hA : A ∈ Ioc (t₀ : ℝ) t₁) :
    shearHolderEnvelope τ A ≤ ENNReal.ofReal (c * Real.sqrt 2 * Real.pi) := by
  simp only [shearHolderSlabCheck, decide_eq_true_eq] at h
  obtain ⟨hU0, hM0, hle⟩ := h
  have ht₀' : (0 : ℝ) ≤ t₀ := by exact_mod_cast ht₀
  have hA0 : 0 < A := ht₀'.trans_lt hA.1
  have ht₁ : (0 : ℚ) ≤ 2 * t₁ := by
    have : (0 : ℝ) ≤ t₁ := hA0.le.trans hA.2
    have : (0 : ℚ) ≤ t₁ := by exact_mod_cast this
    linarith
  have hs : 2 * (2 * A) ^ (1 / 2 : ℝ) ≤ 2 * (sqrtHigh (2 * t₁) : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have h₁ := sqrt_le_sqrtHigh ht₁
    push_cast at h₁
    have h₂ : Real.sqrt (2 * A) ≤ Real.sqrt (2 * t₁) := Real.sqrt_le_sqrt (by linarith [hA.2])
    linarith
  have hS : (0 : ℝ) ≤ sqrtHigh (2 * t₁) := by exact_mod_cast (sqrtHigh_pos ht₁).le
  have hX0 : (0 : ℝ) ≤ shearMassEnvelopeHigh t₀ := by
    exact_mod_cast (shearMassEnvelopeHigh_pos ht₀).le
  have hU0' : (0 : ℝ) ≤ U := by exact_mod_cast hU0
  have hM0' : (0 : ℝ) ≤ M := by exact_mod_cast hM0
  have hτ' : (0 : ℝ) ≤ τ := by exact_mod_cast hτ
  calc shearHolderEnvelope τ A
      ≤ ENNReal.ofReal (shearMassEnvelopeHigh t₀) + ENNReal.ofReal τ *
          (ENNReal.ofReal U + ENNReal.ofReal (2 * (sqrtHigh (2 * t₁) : ℝ)) * ENNReal.ofReal M) := by
        unfold shearHolderEnvelope
        gcongr
        · exact shearMassEnvelope_le_high ht₀ hA.1.le hA0
        · exact (shearUpperEnvelope_mono hA.2).trans hU
        · exact (shearOuterMass_anti hA.1.le).trans hW
    _ = ENNReal.ofReal (shearMassEnvelopeHigh t₀ + τ * (U + 2 * sqrtHigh (2 * t₁) * M)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hU0' (by positivity),
          ← ENNReal.ofReal_mul hτ', ← ENNReal.ofReal_add hX0 (by positivity)]
    _ ≤ ENNReal.ofReal (c * Real.sqrt 2 * Real.pi) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hle' : ((shearMassEnvelopeHigh t₀ + τ * (U + 2 * sqrtHigh (2 * t₁) * M) : ℚ) : ℝ) ≤
            ((c * sqrtLow 2 * (3141592 / 10 ^ 6) : ℚ) : ℝ) := by exact_mod_cast hle
        have h2 := sqrtLow_le_sqrt (q := 2) (by norm_num)
        have h20 : (0 : ℝ) ≤ sqrtLow 2 := by exact_mod_cast (sqrtLow_pos (q := 2) (by norm_num)).le
        have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
        have hπ := Real.pi_gt_d6
        push_cast at hle' h2
        refine hle'.trans ?_
        have : (3141592 / 10 ^ 6 : ℝ) ≤ Real.pi := by norm_num at hπ ⊢; linarith
        have h3 : (sqrtLow 2 : ℝ) * (3141592 / 10 ^ 6) ≤ Real.sqrt 2 * Real.pi :=
          mul_le_mul h2 this (by norm_num) (h20.trans h2)
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left h3 hc'

/-! ### The segments of the walk of `u_y` -/

/-- The walk of the estimate of `u_y` with `τ = 0.582` and the bound `1.55 √2 π`, over the heights
from `t` to `e`, from the bounds `U` of `U(t)` and `M` of `W(t)` to the bounds `Ue` of `U(e)` and
`Me` of `W(e)`. -/
def shearHolderSegment (t e U M Ue Me : ℚ) : Bool :=
  shearHolderWalk (shearSlabCost (1 / 16)) shearSlabMass shearHolderNext
    (shearHolderSlabCheck (582 / 1000) (155 / 100)) Ue Me 100000 t e U M

/-- **Soundness of a segment.** -/
theorem shearHolderSegment_spec {t e U M Ue Me : ℚ} (ht : 0 ≤ t) (hU0 : 0 ≤ U) (hMe0 : 0 ≤ Me)
    (h : shearHolderSegment t e U M Ue Me = true) :
    (shearUpperEnvelope t ≤ ENNReal.ofReal U → shearUpperEnvelope e ≤ ENNReal.ofReal Ue) ∧
      (shearOuterMass e ≤ ENNReal.ofReal Me → shearOuterMass t ≤ ENNReal.ofReal M) ∧
      (shearUpperEnvelope t ≤ ENNReal.ofReal U → shearOuterMass e ≤ ENNReal.ofReal Me →
        ∀ A ∈ Ioc (t : ℝ) e, shearHolderEnvelope (582 / 1000) A ≤
          ENNReal.ofReal (155 / 100 * Real.sqrt 2 * Real.pi)) := by
  have := shearHolderWalk_spec (P := fun A ↦ shearHolderEnvelope (582 / 1000) A ≤
      ENNReal.ofReal (155 / 100 * Real.sqrt 2 * Real.pi))
    (fun _ _ h ↦ shearOuterMass_anti h) (fun _ _ _ ↦ shearOuterMass_le_add)
    (fun _ _ _ hc ↦ lintegral_le_shearSlabCost hc) (fun _ _ _ hm ↦ lintegral_le_shearSlabMass hm)
    (fun _ _ _ _ ht₀ _ hok hU hW _ hA ↦ by
      have := shearHolderSlabCheck_spec (by norm_num) (by norm_num) ht₀ hok hU hW hA
      push_cast at this
      exact this) hMe0 100000 ht hU0 h
  exact this.2

end IncompressibleFlow.SharpHolder
