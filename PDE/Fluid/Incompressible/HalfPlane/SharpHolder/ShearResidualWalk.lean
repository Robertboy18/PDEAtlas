/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearDefectCells
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearHolderWalk
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearLowerCells

/-!
# The walk over heights of the horizontal estimate of `v_x`

For `B ≥ 4`, `h > 0` and `A = min(h, B)`, the residual of `C₁(τ)` is at most the envelope
`(√2 π + X(A)) - D_κ(A) + τ (U(A) + L(A) + E + 2 (2A)^{1/2} W(A))` (`shearResidualEnvelope`),
with the line defect `D_κ` up to `κ ≤ min(9, B - 1)`, the lower cost `L(A) = S_low(10, A)`, an
edge bound `E ≥ E(B)` and an outer mass `W ≥ W_B` (`shearResidual_le_envelope`).

The walk over slabs of heights is `shearHolderWalk` with the slab check
`shearResidualSlabCheck`: for `A ∈ (t₀, t₁]`, `X(A) ≤ X(t₀)`, `D_κ(A) ≥ (t₀/t₁)³ D_κ(t₀)`,
`U(A) ≤ U(t₁)`, `W(A) ≤ W(t₀)`, and `L(A)` is bounded through a table of slab values
(`shearLowerLookup`) whose entries the checks `shearLowerTableOk`, `shearLowerTableBottomOk` and
`shearLowerTableTopOk` compare with the cell walk of the lower cost and with
`S_low(10, A) ≤ 6π √A`. `shearResidualSegment_spec` is the soundness of a segment of the walk.

## Main definitions

* `shearResidualEnvelope`: the envelope of the residual of `C₁(τ)` at the height `A`.
* `shearLowerLookup`: the table value of the lower cost on a slab `[t₀, t₁]`.
* `shearLowerTableOk`, `shearLowerTableBottomOk`, `shearLowerTableTopOk`: the checks of a table
  of lower costs by the cell walk, by `S_low(10, A) ≤ 6π √A` near the axis, and for all `A ≥ ℓ`.
* `shearResidualSlabCheck`: the check of the envelope on a slab of heights.
* `shearResidualSegment`: the walk of the estimate of `v_x` with `τ = 0.582` and the bound
  `2.53 √2 π`.

## Main results

* `shearResidual_le_envelope`: the reduction of the residual of `C₁(τ)` to the envelope
  (Chen and Hou, Part I, (B.39)).
* `shearLowerTableOk_spec`, `shearLowerTableBottomOk_spec`: if a table passes its check, every
  entry `(ℓ, u, v)` gives `S_low(10, A) ≤ v` for `ℓ ≤ A ≤ u`.
* `shearLowerTableTopOk_spec`: if a table passes its check, every entry `(ℓ, u, v)` gives
  `S_low(10, A) ≤ v` for all `A ≥ ℓ`.
* `shearResidualSlabCheck_spec`: a slab that passes the check has envelope at most `c √2 π` for
  every `A ∈ (t₀, t₁]`.
* `shearResidualSegment_spec`: a segment `(t, e]` that passes the walk has envelope at most
  `2.53 √2 π` at every height, given the bounds of `U` at `t` and of `W` at `e`.
* `shearEdgeCost_eq_zero`, `shearEdgeCost_four_le`, `shearEdgeCost_six_le`,
  `shearEdgeCost_eight_le`: the edge costs; `shearResidualEnvelope_le`: the envelope of `v_x`
  without the line defect.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Appendix B.1, (B.39) and (B.40),
  p. 136.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped ENNReal

namespace IncompressibleFlow.SharpHolder

/-! ### The table of lower costs -/

/-- The value of the last entry `(ℓ, u, v)` of the table with `ℓ ≤ t₀` and `t₁ ≤ u`. -/
def shearLowerLookup : List (ℚ × ℚ × ℚ) → ℚ → ℚ → Option ℚ
  | [], _, _ => none
  | x :: xs, t₀, t₁ =>
    match shearLowerLookup xs t₀ t₁ with
    | some v => some v
    | none => if x.1 ≤ t₀ ∧ t₁ ≤ x.2.1 then some x.2.2 else none

/-- A value returned by the lookup is the value of an entry `(ℓ, u, v)` of the table with
`ℓ ≤ t₀` and `t₁ ≤ u`. -/
theorem shearLowerLookup_spec {tab : List (ℚ × ℚ × ℚ)} {t₀ t₁ v : ℚ}
    (h : shearLowerLookup tab t₀ t₁ = some v) :
    ∃ x ∈ tab, x.1 ≤ t₀ ∧ t₁ ≤ x.2.1 ∧ x.2.2 = v := by
  induction tab with
  | nil => simp [shearLowerLookup] at h
  | cons x xs ih =>
    simp only [shearLowerLookup] at h
    split at h
    · rename_i w hw
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨y, hy, h'⟩ := ih hw
      exact ⟨y, List.mem_cons_of_mem _ hy, h'⟩
    · split_ifs at h with hx
      simp only [Option.some.injEq] at h
      exact ⟨x, List.mem_cons_self, hx.1, hx.2, h⟩

/-- The check of a table: every entry `(ℓ, u, v)` bounds the lower cost on `[ℓ, u]`. -/
def shearLowerTableOk (tab : List (ℚ × ℚ × ℚ)) : Bool :=
  tab.all fun x ↦ match shearLowerSlab x.1 x.2.1 with
    | some N => decide ((N : ℚ) / 2 ^ 64 ≤ x.2.2)
    | none => false

/-- If the table passes `shearLowerTableOk`, every entry `(ℓ, u, v)` gives
`S_low(10, A) ≤ v` for `ℓ ≤ A ≤ u`. -/
theorem shearLowerTableOk_spec {tab : List (ℚ × ℚ × ℚ)} (h : shearLowerTableOk tab = true)
    {x : ℚ × ℚ × ℚ} (hx : x ∈ tab) {A : ℝ} (h₁ : (x.1 : ℝ) ≤ A) (h₂ : A ≤ x.2.1) :
    shearLowerCost 10 A ≤ ENNReal.ofReal x.2.2 := by
  have := List.all_eq_true.1 h x hx
  split at this
  · rename_i N hN
    have hv : ((N : ℚ) / 2 ^ 64 : ℚ) ≤ x.2.2 := by simpa using this
    refine (shearLowerCost_le_shearLowerSlab hN h₁ h₂).trans (ENNReal.ofReal_le_ofReal ?_)
    exact_mod_cast hv
  · simp at this

/-- The nodes `a, a r, a r², …` up to `e`, rounded up to about fifty bits. -/
def shearLowerNodes (r a e : ℚ) : ℕ → List ℚ
  | 0 => []
  | n + 1 => if e ≤ a then [e] else a :: shearLowerNodes r (roundUpRel (a * r)) e n

/-- The table with the entries `(a, b ov, v/10⁶)` over consecutive nodes `a, b` and the values
`v`. -/
def shearLowerTableOf (ov : ℚ) (l : List ℚ) (vs : List ℕ) : List (ℚ × ℚ × ℚ) :=
  ((l.zip l.tail).zip vs).map fun x ↦ (x.1.1, x.1.2 * ov, (x.2 : ℚ) / 10 ^ 6)

/-- The table with the entries `(a, 2^64, v/10⁶)` over the nodes `a`; checked by
`shearLowerTableTopOk`, each entry bounds the lower cost for all `A ≥ a`. -/
def shearLowerTableTopOf (l : List ℚ) (vs : List ℕ) : List (ℚ × ℚ × ℚ) :=
  (l.zip vs).map fun x ↦ (x.1, 2 ^ 64, (x.2 : ℚ) / 10 ^ 6)

/-- The check of a table near the axis by `S_low(10, A) ≤ 6π √A` (`shearLowerCost_le_bottom`). -/
def shearLowerTableBottomOk (tab : List (ℚ × ℚ × ℚ)) : Bool :=
  tab.all fun x ↦ decide (0 < x.1 ∧ 0 ≤ x.2.1 ∧ 6 * (3141593 / 10 ^ 6) * sqrtHigh x.2.1 ≤ x.2.2)

/-- If the table passes `shearLowerTableBottomOk`, every entry `(ℓ, u, v)` gives
`S_low(10, A) ≤ v` for `ℓ ≤ A ≤ u`. -/
theorem shearLowerTableBottomOk_spec {tab : List (ℚ × ℚ × ℚ)}
    (h : shearLowerTableBottomOk tab = true) {x : ℚ × ℚ × ℚ} (hx : x ∈ tab) {A : ℝ}
    (h₁ : (x.1 : ℝ) ≤ A) (h₂ : A ≤ x.2.1) :
    shearLowerCost 10 A ≤ ENNReal.ofReal x.2.2 := by
  have := List.all_eq_true.1 h x hx
  simp only [decide_eq_true_eq] at this
  obtain ⟨h0, hu, hv⟩ := this
  have hA : 0 < A := (by exact_mod_cast h0 : (0 : ℝ) < x.1).trans_le h₁
  refine (shearLowerCost_le_bottom hA).trans (ENNReal.ofReal_le_ofReal ?_)
  have hs := sqrt_le_sqrtHigh hu
  have hπ := Real.pi_lt_d6
  have hv' : ((6 * (3141593 / 10 ^ 6) * sqrtHigh x.2.1 : ℚ) : ℝ) ≤ x.2.2 := by exact_mod_cast hv
  push_cast at hv'
  have h1 : Real.sqrt A ≤ Real.sqrt x.2.1 := Real.sqrt_le_sqrt h₂
  have h2 : Real.pi ≤ 3141593 / 10 ^ 6 := by norm_num at hπ ⊢; linarith
  have h3 : (0 : ℝ) ≤ Real.sqrt A := Real.sqrt_nonneg _
  nlinarith [mul_le_mul h2 (h1.trans hs) h3 (by norm_num)]

/-- The check of a table of entries valid for all `A ≥ ℓ`, by the slab bound with `u = 8`
(`shearLowerCost_le_shearLowerSlab_top`). -/
def shearLowerTableTopOk (tab : List (ℚ × ℚ × ℚ)) : Bool :=
  tab.all fun x ↦ match shearLowerSlab x.1 8 with
    | some N => decide ((N : ℚ) / 2 ^ 64 ≤ x.2.2)
    | none => false

/-- If the table passes `shearLowerTableTopOk`, every entry `(ℓ, u, v)` gives
`S_low(10, A) ≤ v` for all `A ≥ ℓ`. -/
theorem shearLowerTableTopOk_spec {tab : List (ℚ × ℚ × ℚ)} (h : shearLowerTableTopOk tab = true)
    {x : ℚ × ℚ × ℚ} (hx : x ∈ tab) {A : ℝ} (h₁ : (x.1 : ℝ) ≤ A) :
    shearLowerCost 10 A ≤ ENNReal.ofReal x.2.2 := by
  have := List.all_eq_true.1 h x hx
  split at this
  · rename_i N hN
    have hv : ((N : ℚ) / 2 ^ 64 : ℚ) ≤ x.2.2 := by simpa using this
    refine (shearLowerCost_le_shearLowerSlab_top (by norm_num) hN h₁).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact_mod_cast hv
  · simp at this

/-- The check of a bound `v` of the lower cost for all `A ≥ ℓ`. -/
def shearLowerTopOk (ℓ v : ℚ) : Bool :=
  match shearLowerSlab ℓ 8 with
  | some N => decide ((N : ℚ) / 2 ^ 64 ≤ v)
  | none => false

/-- If `shearLowerTopOk ℓ v` holds, then `S_low(10, A) ≤ v` for all `A ≥ ℓ`. -/
theorem shearLowerTopOk_spec {ℓ v : ℚ} (h : shearLowerTopOk ℓ v = true) {A : ℝ}
    (hA : (ℓ : ℝ) ≤ A) : shearLowerCost 10 A ≤ ENNReal.ofReal v := by
  unfold shearLowerTopOk at h
  split at h
  · rename_i N hN
    have hv : ((N : ℚ) / 2 ^ 64 : ℚ) ≤ v := by simpa using h
    refine (shearLowerCost_le_shearLowerSlab_top (by norm_num) hN hA).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact_mod_cast hv
  · simp at h

/-! ### The envelope -/

/-- The envelope `(√2 π + X(A)) - D_κ(A) + τ (U(A) + L(A) + E + 2 (2A)^{1/2} W(A))` of the residual
of `C₁(τ)` at the height `A`. -/
def shearResidualEnvelope (τ κ E : ℝ) (W : ℝ → ℝ≥0∞) (A : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.sqrt 2 * Real.pi) + shearMassEnvelope A) - shearLineDefect κ A +
    ENNReal.ofReal τ * (shearUpperEnvelope A + shearLowerCost 10 A + ENNReal.ofReal E +
      ENNReal.ofReal (2 * (2 * A) ^ (1 / 2 : ℝ)) * W A)

/-- The line defect is finite. -/
theorem shearLineDefect_ne_top {κ A : ℝ} (hκ : κ ≤ 9) (hA : 0 < A) : shearLineDefect κ A ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _ in Ioc (1 / 9 : ℝ) κ, ENNReal.ofReal (6 / A)) ?_ ?_
  · rw [setLIntegral_const, Real.volume_Ioc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · refine setLIntegral_mono' measurableSet_Ioc fun p hp ↦ ENNReal.ofReal_le_ofReal ?_
    have hp0 : 0 ≤ p := by linarith [hp.1]
    have hμ0 := shearMassDensity_nonneg hA hp0
    have hμ : shearMassDensity A p ≤ 1 / A := by
      unfold shearMassDensity
      have h₁ : A / ((p - 1) ^ 2 + A ^ 2) ≤ 1 / A := by
        rw [div_le_div_iff₀ (by positivity) hA]
        nlinarith [sq_nonneg (p - 1)]
      have h₂ : 0 ≤ A / ((p + 1) ^ 2 + A ^ 2) := by positivity
      linarith
    have hd : shearLineWeight p ≤ 6 := by
      rw [shearLineWeight_eq]
      have h₁ : Real.sqrt (2 * p) ≤ 9 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]
        nlinarith [hp.2]
      have h₂ : Real.sqrt 2 ≤ 3 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num
      have h₃ := Real.sqrt_nonneg |p - 1|
      linarith
    calc shearLineWeight p * shearMassDensity A p ≤ 6 * shearMassDensity A p :=
          mul_le_mul_of_nonneg_right hd hμ0
      _ ≤ 6 * (1 / A) := by gcongr
      _ = 6 / A := by ring

/-- **The reduction to the envelope** (Chen and Hou, Part I, (B.39)): for `B ≥ 4`, `h > 0`,
`A = min(h, B)`, `κ ≤ min(9, B - 1)`, `E(B) ≤ E` and a mass `W` above the mass of `|Δ|` over
`(A, B]`, the residual of `C₁(τ)` is at most the envelope. -/
theorem shearResidual_le_envelope {τ κ E B h : ℝ} {W : ℝ → ℝ≥0∞} (hB : 4 ≤ B)
    (hh : 0 < h) (hκ : κ ≤ 9) (hκB : κ ≤ B - 1) (hE : shearEdgeCost B ≤ E)
    (hW : shearOuterMassBelow (min h B) B ≤ W (min h B)) :
    shearInnerMassCost B (min h B) + shearLineCost B (min h B) + ENNReal.ofReal τ *
      (shearUpperCost B (min h B) + shearLowerCost B (min h B) + shearOuterCost B h) ≤
        shearResidualEnvelope τ κ E W (min h B) := by
  set A := min h B
  have hA : 0 < A := lt_min hh (by linarith)
  have hD := shearInnerMassCost_add_shearLineCost_le hB hA hκ hκB
  have hD' : shearInnerMassCost B A + shearLineCost B A ≤
      (ENNReal.ofReal (Real.sqrt 2 * Real.pi) + shearMassEnvelope A) - shearLineDefect κ A :=
    ENNReal.le_sub_of_add_le_right (shearLineDefect_ne_top hκ hA) hD
  have hout : shearOuterCost B h ≤ ENNReal.ofReal (2 * (2 * A) ^ (1 / 2 : ℝ)) * W A := by
    rcases lt_or_ge h B with hhB | hhB
    · have hAh : A = h := min_eq_left hhB.le
      refine (shearOuterCost_le_mass_below hB hh).trans ?_
      rw [hAh] at hW ⊢
      gcongr
    · have h0 : shearOuterCost B h = 0 := by
        rw [shearOuterCost, Ioc_eq_empty (not_lt.2 hhB)]
        simp
      rw [h0]
      exact zero_le
  have hlow : shearLowerCost B A ≤ shearLowerCost 10 A + ENNReal.ofReal E :=
    (shearLowerCost_le_add hB hA).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hE))
  unfold shearResidualEnvelope
  calc shearInnerMassCost B A + shearLineCost B A + ENNReal.ofReal τ *
        (shearUpperCost B A + shearLowerCost B A + shearOuterCost B h)
      ≤ ((ENNReal.ofReal (Real.sqrt 2 * Real.pi) + shearMassEnvelope A) - shearLineDefect κ A) +
          ENNReal.ofReal τ * (shearUpperEnvelope A + (shearLowerCost 10 A + ENNReal.ofReal E) +
            ENNReal.ofReal (2 * (2 * A) ^ (1 / 2 : ℝ)) * W A) := by
        gcongr
        exact shearUpperCost_le_envelope hB (min_le_right _ _)
    _ = _ := by ring

/-! ### The slab check -/

/-- `√2 π ≤ sqrtHigh 2 · 3.141593`. -/
theorem sqrt_two_mul_pi_le_high :
    Real.sqrt 2 * Real.pi ≤ (sqrtHigh 2 : ℝ) * (3141593 / 10 ^ 6) := by
  have h2 := sqrt_le_sqrtHigh (q := 2) (by norm_num)
  have hh : (0 : ℝ) < sqrtHigh 2 := by exact_mod_cast sqrtHigh_pos (q := 2) (by norm_num)
  have hπ := Real.pi_lt_d6
  push_cast at h2
  exact mul_le_mul h2 (by norm_num at hπ ⊢; linarith) Real.pi_pos.le hh.le

/-- `sqrtLow 2 · 3.141592 ≤ √2 π`. -/
theorem sqrtLow_two_mul_pi_le : (sqrtLow 2 : ℝ) * (3141592 / 10 ^ 6) ≤ Real.sqrt 2 * Real.pi := by
  have h2 := sqrtLow_le_sqrt (q := 2) (by norm_num)
  have h20 : (0 : ℝ) ≤ sqrtLow 2 := by exact_mod_cast (sqrtLow_pos (q := 2) (by norm_num)).le
  have hπ := Real.pi_gt_d6
  push_cast at h2
  exact mul_le_mul h2 (by norm_num at hπ ⊢; linarith) (by norm_num) (h20.trans h2)

/-- The check of the slab `[t₀, t₁]` with the weight `τ`, the bound `c √2 π`, the line defect up
to `κ`, the edge bound `E` and the table `tab`, from the bounds `U` of `U(t₁)` and `M` of
`W(t₀)`. -/
def shearResidualSlabCheck (τ c κ E : ℚ) (tab : List (ℚ × ℚ × ℚ)) (t₀ t₁ U M : ℚ) : Bool :=
  match shearLowerLookup tab t₀ t₁ with
  | some v =>
    let S := sqrtHigh 2 * (3141593 / 10 ^ 6) + shearMassEnvelopeHigh t₀
    let d := (t₀ / t₁) ^ 3 * max 0 (shearDefectLow κ t₀)
    decide (0 < t₀ ∧ 0 ≤ U ∧ 0 ≤ M ∧ 0 ≤ v ∧ 0 ≤ E ∧ d ≤ S ∧
      S - d + τ * (U + v + E + 2 * sqrtHigh (2 * t₁) * M) ≤ c * sqrtLow 2 * (3141592 / 10 ^ 6))
  | none => false

/-- **Soundness of the slab check.** -/
theorem shearResidualSlabCheck_spec {τ c κ E t₀ t₁ U M : ℚ} {tab : List (ℚ × ℚ × ℚ)}
    {W : ℝ → ℝ≥0∞} (hWa : ∀ a b : ℝ, a ≤ b → W b ≤ W a) (hτ : 0 ≤ τ) (hc : 0 ≤ c) (hκ : κ ≤ 9)
    (htab : ∀ x ∈ tab, ∀ A : ℝ, (x.1 : ℝ) ≤ A → A ≤ x.2.1 →
      shearLowerCost 10 A ≤ ENNReal.ofReal x.2.2)
    (h : shearResidualSlabCheck τ c κ E tab t₀ t₁ U M = true)
    (hU : shearUpperEnvelope t₁ ≤ ENNReal.ofReal U) (hWM : W t₀ ≤ ENNReal.ofReal M)
    {A : ℝ} (hA : A ∈ Ioc (t₀ : ℝ) t₁) :
    shearResidualEnvelope τ κ E W A ≤ ENNReal.ofReal (c * Real.sqrt 2 * Real.pi) := by
  unfold shearResidualSlabCheck at h
  split at h
  · rename_i v hv
    simp only [decide_eq_true_eq] at h
    obtain ⟨ht₀, hU0, hM0, hv0, hE0, hdS, hle⟩ := h
    obtain ⟨x, hx, hx₁, hx₂, hxv⟩ := shearLowerLookup_spec hv
    have ht₀' : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
    have hA0 : 0 < A := ht₀'.trans hA.1
    have ht₁ : (0 : ℚ) < t₁ := by exact_mod_cast hA0.trans_le hA.2
    -- the pieces
    have hX := shearMassEnvelope_le_high ht₀.le hA.1.le hA0
    have hL : shearLowerCost 10 A ≤ ENNReal.ofReal v := hxv ▸ htab x hx A
      ((by exact_mod_cast hx₁ : (x.1 : ℝ) ≤ t₀).trans hA.1.le) (hA.2.trans (by exact_mod_cast hx₂))
    have hUA := (shearUpperEnvelope_mono hA.2).trans hU
    have hWA := (hWa _ _ hA.1.le).trans hWM
    have hs : 2 * (2 * A) ^ (1 / 2 : ℝ) ≤ 2 * (sqrtHigh (2 * t₁) : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      have h₁ := sqrt_le_sqrtHigh (q := 2 * t₁) (by linarith)
      push_cast at h₁
      have h₂ : Real.sqrt (2 * A) ≤ Real.sqrt (2 * t₁) := Real.sqrt_le_sqrt (by linarith [hA.2])
      linarith
    -- the line defect
    set d := (t₀ / t₁) ^ 3 * max 0 (shearDefectLow κ t₀)
    have hd0 : (0 : ℚ) ≤ d := by positivity
    have hD : ENNReal.ofReal (d : ℝ) ≤ shearLineDefect κ A := by
      have h₁ := ofReal_shearDefectLow_le (c := κ) ht₀
      have h₂ := shearLineDefect_le (c := (κ : ℝ)) (by exact_mod_cast hκ) ht₀' hA.1.le
      refine le_trans ?_ h₂
      have hr : ((t₀ : ℝ) / t₁) ^ 3 ≤ ((t₀ : ℝ) / A) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left ht₀'.le hA0 hA.2) 3
      rcases le_total 0 (shearDefectLow κ t₀) with hl | hl
      · simp only [d, max_eq_right hl]
        push_cast
        rw [ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal hr) h₁
      · simp only [d, max_eq_left hl, mul_zero, Rat.cast_zero, ENNReal.ofReal_zero]
        exact zero_le
    -- the bound
    set S := sqrtHigh 2 * (3141593 / 10 ^ 6) + shearMassEnvelopeHigh t₀
    have hS : ENNReal.ofReal (Real.sqrt 2 * Real.pi) + shearMassEnvelope A ≤ ENNReal.ofReal S := by
      have h₁ := sqrtHigh_pos (q := 2) (by norm_num)
      have h₂ : (0 : ℝ) ≤ shearMassEnvelopeHigh t₀ := by
        exact_mod_cast (shearMassEnvelopeHigh_pos ht₀.le).le
      simp only [S]
      push_cast
      rw [ENNReal.ofReal_add (by positivity) h₂]
      exact add_le_add (ENNReal.ofReal_le_ofReal sqrt_two_mul_pi_le_high) hX
    have hSq : (0 : ℝ) ≤ sqrtHigh (2 * t₁) := by exact_mod_cast (sqrtHigh_pos (by linarith)).le
    have hU0' : (0 : ℝ) ≤ U := by exact_mod_cast hU0
    have hM0' : (0 : ℝ) ≤ M := by exact_mod_cast hM0
    have hv0' : (0 : ℝ) ≤ v := by exact_mod_cast hv0
    have hE0' : (0 : ℝ) ≤ E := by exact_mod_cast hE0
    have hτ' : (0 : ℝ) ≤ τ := by exact_mod_cast hτ
    have hdS' : (d : ℝ) ≤ S := by exact_mod_cast hdS
    unfold shearResidualEnvelope
    calc (ENNReal.ofReal (Real.sqrt 2 * Real.pi) + shearMassEnvelope A) - shearLineDefect κ A +
          ENNReal.ofReal τ * (shearUpperEnvelope A + shearLowerCost 10 A + ENNReal.ofReal E +
            ENNReal.ofReal (2 * (2 * A) ^ (1 / 2 : ℝ)) * W A)
        ≤ (ENNReal.ofReal S - ENNReal.ofReal d) + ENNReal.ofReal τ * (ENNReal.ofReal U +
            ENNReal.ofReal v + ENNReal.ofReal E +
              ENNReal.ofReal (2 * (sqrtHigh (2 * t₁) : ℝ)) * ENNReal.ofReal M) := by
          gcongr
      _ = ENNReal.ofReal (S - d + τ * (U + v + E + 2 * sqrtHigh (2 * t₁) * M)) := by
          rw [← ENNReal.ofReal_sub _ (by exact_mod_cast hd0), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add hU0' hv0', ← ENNReal.ofReal_add (by positivity) hE0',
            ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hτ',
            ← ENNReal.ofReal_add (by linarith) (by positivity)]
      _ ≤ ENNReal.ofReal (c * Real.sqrt 2 * Real.pi) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hle' : ((S - d + τ * (U + v + E + 2 * sqrtHigh (2 * t₁) * M) : ℚ) : ℝ) ≤
              ((c * sqrtLow 2 * (3141592 / 10 ^ 6) : ℚ) : ℝ) := by exact_mod_cast hle
          push_cast at hle'
          refine hle'.trans ?_
          have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_left sqrtLow_two_mul_pi_le hc'
  · simp at h

/-! ### The segments of the walk of `v_x` -/

/-- The mesh of heights of `v_x`: the ratio `ρ` on `[2, 64]`, around the maximum of the envelope
near `A = 7`, and `1/16` elsewhere. -/
def shearResidualNext (ρ t : ℚ) : ℚ :=
  shearNextHeight (if 2 ≤ t ∧ t < 64 then ρ else 1 / 16) t

/-- The walk of the estimate of `v_x` with `τ = 0.582` and the bound `2.53 √2 π`, the mesh ratio
`ρ` on `[2, 64]`, the line defect up to `κ`, the edge bound `E` and the table `tab`. -/
def shearResidualSegment (ρ κ E : ℚ) (tab : List (ℚ × ℚ × ℚ)) (t e U M Ue Me : ℚ) : Bool :=
  shearHolderWalk (shearSlabCost (1 / 16)) shearSlabMass (shearResidualNext ρ)
    (shearResidualSlabCheck (582 / 1000) (253 / 100) κ E tab) Ue Me 100000 t e U M

/-- **Soundness of a segment of `v_x`.** -/
theorem shearResidualSegment_spec {ρ κ E : ℚ} {tab : List (ℚ × ℚ × ℚ)} {W : ℝ → ℝ≥0∞}
    (hWa : ∀ a b : ℝ, a ≤ b → W b ≤ W a)
    (hWs : ∀ a b : ℝ, a ≤ b →
      W a ≤ (∫⁻ t in Ioc a b, ∫⁻ p in Ioi (0 : ℝ), ‖shearDifference p t‖ₑ) + W b)
    (hκ : κ ≤ 9) (htab : ∀ x ∈ tab, ∀ A : ℝ, (x.1 : ℝ) ≤ A → A ≤ x.2.1 →
      shearLowerCost 10 A ≤ ENNReal.ofReal x.2.2) {t e U M Ue Me : ℚ} (ht : 0 ≤ t)
    (hU0 : 0 ≤ U) (hMe0 : 0 ≤ Me) (h : shearResidualSegment ρ κ E tab t e U M Ue Me = true) :
    (shearUpperEnvelope t ≤ ENNReal.ofReal U → shearUpperEnvelope e ≤ ENNReal.ofReal Ue) ∧
      (W e ≤ ENNReal.ofReal Me → W t ≤ ENNReal.ofReal M) ∧
      (shearUpperEnvelope t ≤ ENNReal.ofReal U → W e ≤ ENNReal.ofReal Me →
        ∀ A ∈ Ioc (t : ℝ) e, shearResidualEnvelope (582 / 1000) κ E W A ≤
          ENNReal.ofReal (253 / 100 * Real.sqrt 2 * Real.pi)) := by
  have := shearHolderWalk_spec (P := fun A ↦ shearResidualEnvelope (582 / 1000) κ E W A ≤
      ENNReal.ofReal (253 / 100 * Real.sqrt 2 * Real.pi)) hWa hWs
    (fun _ _ _ hc ↦ lintegral_le_shearSlabCost hc) (fun _ _ _ hm ↦ lintegral_le_shearSlabMass hm)
    (fun _ _ _ _ _ _ hok hU hWM _ hA ↦ by
      have := shearResidualSlabCheck_spec hWa (by norm_num) (by norm_num) hκ htab hok hU hWM hA
      push_cast at this
      exact this) hMe0 100000 ht hU0 h
  exact this.2

/-- The edge cost vanishes from `B = 10` on, where no edge column is left. -/
theorem shearEdgeCost_eq_zero {B : ℝ} (hB : 10 ≤ B) : shearEdgeCost B = 0 := by
  simp [shearEdgeCost, not_lt.2 hB]

/-- `E(4) ≤ 0.6695`. -/
theorem shearEdgeCost_four_le : shearEdgeCost 4 ≤ 6695 / 10 ^ 4 := by
  have h : (14141875 / 10 ^ 7 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [shearEdgeCost, show (4 : ℝ) < 10 by norm_num, ↓reduceIte, show min (4 : ℝ) 8 = 4 by
    norm_num, show (4 : ℝ) - 2 = 2 by norm_num, h4]
  linarith

/-- `E(6) ≤ 0.5138`. -/
theorem shearEdgeCost_six_le : shearEdgeCost 6 ≤ 5138 / 10 ^ 4 := by
  have h : Real.sqrt 6 < 2449575 / 10 ^ 6 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [shearEdgeCost, show (6 : ℝ) < 10 by norm_num, ↓reduceIte, show min (6 : ℝ) 8 = 6 by
    norm_num, show (6 : ℝ) - 2 = 4 by norm_num, h4]
  linarith

/-- `E(8) ≤ 0.4331`. -/
theorem shearEdgeCost_eight_le : shearEdgeCost 8 ≤ 4331 / 10 ^ 4 := by
  have h₁ : Real.sqrt 8 < 2828428 / 10 ^ 6 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h₂ : (2449489 / 10 ^ 6 : ℝ) < Real.sqrt 6 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  simp only [shearEdgeCost, show (8 : ℝ) < 10 by norm_num, ↓reduceIte, show min (8 : ℝ) 8 = 8 by
    norm_num, show (8 : ℝ) - 2 = 6 by norm_num]
  linarith

/-- The mass of `|Δ|` over `(h, B]` decreases as the lower height `h` increases. -/
theorem shearOuterMassBelow_anti (B : ℝ) {a b : ℝ} (h : a ≤ b) :
    shearOuterMassBelow b B ≤ shearOuterMassBelow a B :=
  lintegral_mono_set (Ioc_subset_Ioc_left h)

/-- Splitting `(a, B]` at `b`: the mass over `(a, B]` is at most the mass over `(a, b]` plus the
mass over `(b, B]`. -/
theorem shearOuterMassBelow_le_add (B : ℝ) {a b : ℝ} (_ : a ≤ b) :
    shearOuterMassBelow a B ≤
      (∫⁻ t in Ioc a b, ∫⁻ p in Ioi (0 : ℝ), ‖shearDifference p t‖ₑ) + shearOuterMassBelow b B := by
  have hsub : Ioc a B ⊆ Ioc a b ∪ Ioc b B := by
    intro x hx
    rcases le_or_gt x b with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2⟩
  exact (lintegral_mono_set hsub).trans (lintegral_union_le _ _ _)

/-- The mass over the empty range `(B, B]` is zero. -/
theorem shearOuterMassBelow_self (B : ℝ) : shearOuterMassBelow B B = 0 := by
  simp [shearOuterMassBelow]

/-- The envelope of `v_x` without the line defect: the envelope of `u_y` plus `√2 π` and
`τ (L(A) + E)`. -/
theorem shearResidualEnvelope_le {τ κ E A : ℝ} {W : ℝ → ℝ≥0∞}
    (hW : W A ≤ shearOuterMass A) :
    shearResidualEnvelope τ κ E W A ≤ ENNReal.ofReal (Real.sqrt 2 * Real.pi) +
      shearHolderEnvelope τ A + ENNReal.ofReal τ * (shearLowerCost 10 A + ENNReal.ofReal E) := by
  unfold shearResidualEnvelope shearHolderEnvelope
  calc (ENNReal.ofReal (Real.sqrt 2 * Real.pi) + shearMassEnvelope A) - shearLineDefect κ A +
        ENNReal.ofReal τ * (shearUpperEnvelope A + shearLowerCost 10 A + ENNReal.ofReal E +
          ENNReal.ofReal (2 * (2 * A) ^ (1 / 2 : ℝ)) * W A)
      ≤ (ENNReal.ofReal (Real.sqrt 2 * Real.pi) + shearMassEnvelope A) +
        ENNReal.ofReal τ * (shearUpperEnvelope A + shearLowerCost 10 A + ENNReal.ofReal E +
          ENNReal.ofReal (2 * (2 * A) ^ (1 / 2 : ℝ)) * shearOuterMass A) := by
        gcongr
        exact tsub_le_self
    _ = _ := by ring

end IncompressibleFlow.SharpHolder
