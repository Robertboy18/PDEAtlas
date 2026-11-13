/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Upper bounds of integrals by sums over a generated partition

A certificate that bounds an interval quantity such as `∫⁻ x in Ioc a b, F x` walks from `a` to
`b` through nodes produced by a rule `next`. Each cell `(l, u)` returns either `none` (the cell
check failed) or `some n` with an integer `n ≥ 0`, read as the bound `n / 2 ^ K`. A successful
walk gives the bound on the quantity, for any interval function `Φ` that is subadditive and
vanishes on empty intervals, given a cell lemma: whenever the cell returns `some n`,
`Φ (g l) (g u) ≤ n / 2 ^ K`. The nodes are rationals mapped to the real line by a map `g` that is
monotone on `[0, ∞)`, such as `w ↦ w ^ 2`.

## Main definitions

* `cellWalk`: the walk from `w` to `e` through `min (next w) e`, accumulating the integer cell
  bounds.
* `ceilScaled`: `ceilScaled K q = ⌈q 2^K⌉`, the upward rounding of a rational cell bound to the
  grid `2 ^ -K`.

## Main results

* `le_ceilScaled`: `q ≤ ⌈q 2^K⌉ / 2^K`.
* `le_of_cellWalk_of_subadditive`: a successful walk bounds a subadditive interval function `Φ`
  by the accumulated sum.
* `lintegral_le_of_cellWalk`: the case `Φ a b = ∫⁻ x in Ioc a b, F x`.
* `lintegral_lintegral_ofReal_eq`: an iterated lower integral of a nonnegative function that is
  continuous on a closed rectangle is the real iterated integral.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis

/-- The cell walk: from `w` to `e` through `min (next w) e`, accumulating the integer cell bounds
in `acc`; `none` if the fuel runs out, the nodes fail to increase, or a cell fails. -/
def cellWalk (next : ℚ → ℚ) (cell : ℚ → ℚ → Option ℤ) : ℕ → ℚ → ℚ → ℤ → Option ℤ
  | 0, _, _, _ => none
  | fuel + 1, w, e, acc =>
    if e ≤ w then some acc
    else
      let w' := min (next w) e
      if w < w' then
        match cell w w' with
        | some n => if 0 ≤ n then cellWalk next cell fuel w' e (acc + n) else none
        | none => none
      else none

/-- `⌈q 2^K⌉`, the upward rounding of `q` to the grid `2 ^ -K`. -/
def ceilScaled (K : ℕ) (q : ℚ) : ℤ := ⌈q * 2 ^ K⌉

/-- The upward grid rounding bounds `q` from above: `q ≤ ⌈q 2^K⌉ / 2^K`. -/
theorem le_ceilScaled (K : ℕ) (q : ℚ) : q ≤ (ceilScaled K q : ℚ) / 2 ^ K := by
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

/-- The bound `q ≤ ⌈q 2^K⌉ / 2^K` read in `ℝ`. -/
theorem le_ceilScaled_real (K : ℕ) (q : ℚ) : (q : ℝ) ≤ (ceilScaled K q : ℝ) / 2 ^ K := by
  have h := le_ceilScaled K q
  exact_mod_cast h

variable {next : ℚ → ℚ} {cell : ℚ → ℚ → Option ℤ}

/-- A successful walk accumulates: `acc ≤ acc'`. -/
theorem le_of_cellWalk {fuel : ℕ} {w e : ℚ} {acc acc' : ℤ}
    (h : cellWalk next cell fuel w e acc = some acc') : acc ≤ acc' := by
  induction fuel generalizing w acc with
  | zero => simp [cellWalk] at h
  | succ n ih =>
    simp only [cellWalk] at h
    split_ifs at h with he hc
    · simp only [Option.some.injEq] at h
      exact h.le
    · split at h
      · split_ifs at h with hn
        have := ih h
        linarith
      · simp at h

/-- **Soundness of the cell walk** for a subadditive interval function `Φ` that vanishes on empty
intervals: if every cell returning `some n` satisfies `Φ (g l) (g u) ≤ n / 2^K`, and the walk from
`w ≥ 0` to `e ≥ 0` returns `acc'` from `acc`, then `Φ (g w) (g e) ≤ (acc' - acc) / 2^K`. -/
theorem le_of_cellWalk_of_subadditive {Φ : ℝ → ℝ → ℝ≥0∞} {g : ℚ → ℝ}
    (hg : MonotoneOn g (Ici 0)) {K : ℕ}
    (hsub : ∀ a b c : ℝ, a ≤ b → b ≤ c → Φ a c ≤ Φ a b + Φ b c)
    (hempty : ∀ a b : ℝ, b ≤ a → Φ a b = 0)
    (hcell : ∀ l u : ℚ, ∀ n : ℤ, 0 ≤ l → l < u → cell l u = some n →
      Φ (g l) (g u) ≤ ENNReal.ofReal (n / 2 ^ K))
    {fuel : ℕ} {w e : ℚ} {acc acc' : ℤ} (hw : 0 ≤ w) (he0 : 0 ≤ e)
    (h : cellWalk next cell fuel w e acc = some acc') :
    Φ (g w) (g e) ≤ ENNReal.ofReal ((acc' - acc) / 2 ^ K) := by
  induction fuel generalizing w acc with
  | zero => simp [cellWalk] at h
  | succ m ih =>
    simp only [cellWalk] at h
    split_ifs at h with he hlt
    · rw [hempty _ _ (hg he0 hw he)]
      exact zero_le
    · split at h
      · rename_i n hn
        split_ifs at h with hn0
        set w' := min (next w) e
        have hw' : 0 ≤ w' := hw.trans hlt.le
        have he' : w' ≤ e := min_le_right _ _
        have hrest := ih hw' h
        have hacc := le_of_cellWalk h
        calc Φ (g w) (g e) ≤ Φ (g w) (g w') + Φ (g w') (g e) :=
              hsub _ _ _ (hg hw hw' hlt.le) (hg hw' he0 he')
          _ ≤ ENNReal.ofReal (n / 2 ^ K) +
                ENNReal.ofReal ((acc' - ((acc + n : ℤ) : ℝ)) / 2 ^ K) :=
              add_le_add (hcell w w' n hw hlt hn) hrest
          _ = ENNReal.ofReal ((acc' - acc) / 2 ^ K) := by
              have hn0' : (0 : ℝ) ≤ n := by exact_mod_cast hn0
              rw [← ENNReal.ofReal_add (by positivity) (div_nonneg (by
                have : ((acc + n : ℤ) : ℝ) ≤ acc' := by exact_mod_cast hacc
                linarith) (by positivity))]
              congr 1
              push_cast
              ring
      · simp at h

/-- Lower integrals over intervals are subadditive, for any splitting point `b`, not
necessarily between `a` and `c`. -/
theorem lintegral_Ioc_le_add (F : ℝ → ℝ≥0∞) {a b c : ℝ} :
    ∫⁻ x in Ioc a c, F x ≤ (∫⁻ x in Ioc a b, F x) + ∫⁻ x in Ioc b c, F x :=
  (lintegral_mono_set Ioc_subset_Ioc_union_Ioc).trans (lintegral_union_le _ _ _)

/-- **Soundness of the cell walk** for `∫⁻ x in Ioc a b, F x`. -/
theorem lintegral_le_of_cellWalk {F : ℝ → ℝ≥0∞} {g : ℚ → ℝ} (hg : MonotoneOn g (Ici 0))
    {K : ℕ}
    (hcell : ∀ l u : ℚ, ∀ n : ℤ, 0 ≤ l → l < u → cell l u = some n →
      ∫⁻ x in Ioc (g l) (g u), F x ≤ ENNReal.ofReal (n / 2 ^ K))
    {fuel : ℕ} {w e : ℚ} {acc acc' : ℤ} (hw : 0 ≤ w) (he0 : 0 ≤ e)
    (h : cellWalk next cell fuel w e acc = some acc') :
    ∫⁻ x in Ioc (g w) (g e), F x ≤ ENNReal.ofReal ((acc' - acc) / 2 ^ K) :=
  le_of_cellWalk_of_subadditive (Φ := fun a b ↦ ∫⁻ x in Ioc a b, F x) hg
    (fun _ _ _ _ _ ↦ lintegral_Ioc_le_add F)
    (fun a b hba ↦ by simp [Ioc_eq_empty (not_lt.2 hba)]) hcell hw he0 h

/-- An iterated lower integral over `Ioc z₀ z₁ × Ioc x₀ x₁` of `ofReal (h s₁ s₂)`, for `h`
continuous and nonnegative on the closed rectangle, is the real iterated integral. -/
theorem lintegral_lintegral_ofReal_eq {h : ℝ → ℝ → ℝ} {x₀ x₁ z₀ z₁ : ℝ} (hx : x₀ ≤ x₁)
    (hz : z₀ ≤ z₁) (hc : ContinuousOn (fun p : ℝ × ℝ ↦ h p.1 p.2) (Icc x₀ x₁ ×ˢ Icc z₀ z₁))
    (h0 : ∀ s₁ ∈ Icc x₀ x₁, ∀ s₂ ∈ Icc z₀ z₁, 0 ≤ h s₁ s₂) :
    ∫⁻ s₂ in Ioc z₀ z₁, ∫⁻ s₁ in Ioc x₀ x₁, ENNReal.ofReal (h s₁ s₂) =
      ENNReal.ofReal (∫ s₂ in z₀..z₁, ∫ s₁ in x₀..x₁, h s₁ s₂) := by
  set H : ℝ → ℝ → ℝ := fun s₁ s₂ ↦ h (projIcc x₀ x₁ hx s₁) (projIcc z₀ z₁ hz s₂)
  have hH : Continuous fun p : ℝ × ℝ ↦ H p.1 p.2 := by
    have hp : Continuous fun p : ℝ × ℝ ↦
        ((projIcc x₀ x₁ hx p.1 : ℝ), (projIcc z₀ z₁ hz p.2 : ℝ)) :=
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
    exact hc.comp_continuous hp fun p ↦ ⟨(projIcc x₀ x₁ hx p.1).2, (projIcc z₀ z₁ hz p.2).2⟩
  have hHeq : ∀ s₁ ∈ Icc x₀ x₁, ∀ s₂ ∈ Icc z₀ z₁, H s₁ s₂ = h s₁ s₂ := by
    intro s₁ hs₁ s₂ hs₂
    simp only [H, projIcc_of_mem hx hs₁, projIcc_of_mem hz hs₂]
  have hH0 : ∀ s₁ s₂, 0 ≤ H s₁ s₂ := fun s₁ s₂ ↦
    h0 _ (projIcc x₀ x₁ hx s₁).2 _ (projIcc z₀ z₁ hz s₂).2
  have hinner : ∀ s₂ ∈ Ioc z₀ z₁, ∫⁻ s₁ in Ioc x₀ x₁, ENNReal.ofReal (h s₁ s₂) =
      ENNReal.ofReal (∫ s₁ in x₀..x₁, H s₁ s₂) := by
    intro s₂ hs₂
    have hs₂' : s₂ ∈ Icc z₀ z₁ := Ioc_subset_Icc_self hs₂
    have hint : IntegrableOn (fun s₁ ↦ H s₁ s₂) (Ioc x₀ x₁) :=
      (hH.comp (continuous_id.prodMk continuous_const)).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    rw [intervalIntegral.integral_of_le hx, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun s₁ ↦ hH0 _ _)]
    refine setLIntegral_congr_fun measurableSet_Ioc fun s₁ hs₁ ↦ ?_
    rw [hHeq s₁ (Ioc_subset_Icc_self hs₁) s₂ hs₂']
  have hcont : Continuous fun s₂ ↦ ∫ s₁ in x₀..x₁, H s₁ s₂ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun s₂ s₁ ↦ H s₁ s₂) (hH.comp continuous_swap) x₀ x₁
  rw [setLIntegral_congr_fun measurableSet_Ioc hinner, intervalIntegral.integral_of_le hz,
    ← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (Filter.Eventually.of_forall fun s₂ ↦
        intervalIntegral.integral_nonneg hx fun s₁ _ ↦ hH0 _ _)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun s₂ hs₂ ↦ ?_
  refine intervalIntegral.integral_congr fun s₁ hs₁ ↦ ?_
  rw [uIcc_of_le hx] at hs₁
  exact hHeq s₁ hs₁ s₂ (Ioc_subset_Icc_self hs₂)

end PDE.Analysis
