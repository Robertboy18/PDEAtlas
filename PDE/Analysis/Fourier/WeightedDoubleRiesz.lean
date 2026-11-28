/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.MeasureTheory.LpNorm.Convergence
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Closure
public import PDE.Analysis.Fourier.Agmon
public import PDE.Spaces.Sobolev.Inequalities.Hardy.WholeSpace
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The double Riesz transforms on `L²` with the weight `|x|²`

The double Riesz transform `RᵢRⱼ` is a contraction of `L²(ℝⁿ)` (`norm_doubleRiesz_apply_le`).
This module shows that it stays bounded when both sides carry the weight `|x|²`: in dimension
`n ≥ 3`, `∫ |x|² |RᵢRⱼ f|² ≤ (2 + 128 n) ∫ |x|² |f|²`. The weight `|x|²` is an `A₂` weight on
`ℝ³`, so the bound also follows from the theory of Calderón–Zygmund operators on weighted
spaces, and Hou, Wang and Yang quote it from there for their pressure estimate. The proof here
does not use that theory. It is a computation on the Fourier side with Hardy's inequality, and
it gives an explicit constant. The other powers `|x|^α`, `-n < α < n`, and general `A₂` weights
are not treated.

## Main results

* `integrable_norm_sq_mul_doubleRiesz`: for `n ≥ 3` and every `f ∈ L²(ℝⁿ; ℂ)` with
  `|x| f ∈ L²`, also `|x| RᵢRⱼ f ∈ L²`, and `∫ |x|² |RᵢRⱼ f|² ≤ (2 + 128 n) ∫ |x|² |f|²`.
* `hasWeakDerivativeOn_regRieszSymbol_zero_mul`: for `n ≥ 3` and every real `f ∈ L²` with weak
  gradient in `L²`, the product rule `∂_l (m f) = m ∂_l f + (∂_l m) f` on the whole space, with
  `m(k) = -kᵢkⱼ/|k|²` the symbol of `RᵢRⱼ`. `hasComplexWeakDerivativeOn_doubleRieszSymbol_mul`
  is the same rule for complex `L²` classes.
* `exists_hasComplexWeakDerivativeOn_fourier_of_moment` and
  `integrable_moment_of_hasComplexWeakDerivativeOn_fourier`: for every `u ∈ L²`, the moment
  `x_l u` is in `L²` exactly when `∂_l û` is, and `‖∂_l û‖² = (2π)² ∫ x_l² |u|²`.

## How it works

On the Fourier side multiplication by `x_l` is a derivative, `x_l f ↦ (i/2π) ∂_l f̂`, and `RᵢRⱼ`
is multiplication by the symbol `m`. So `x_l RᵢRⱼ f` corresponds to
`(i/2π) ∂_l (m f̂) = (i/2π) (m ∂_l f̂ + (∂_l m) f̂)`. The first term is at most `|∂_l f̂|`, because
`|m| ≤ 1`. The symbol is homogeneous of degree zero, so `|∂_l m| ≤ 4/|k|`, and Hardy's inequality
`‖f̂/|k|‖₂ ≤ 2 ‖∇f̂‖₂ = 4π ‖ |x| f ‖₂` bounds the second term. The product rule has to be
justified across `k = 0`, where `m` is discontinuous. It holds for the smooth symbols
`-kᵢkⱼ/(|k|² + e)`, `e > 0`, and we let `e → 0` by dominated convergence, with Hardy's
inequality as the dominating bound.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Appendix F, step 2 of the
  proof of Proposition 4: the pressure estimate after (F.15), where `|ξ|^α` is an `A₂` weight
  for `-3 < α < 3`, p. 70. <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Set Filter Real
open scoped Topology ENNReal

namespace PDE.Analysis.Fourier

variable {n : ℕ}

/-! ## The regularized symbols -/

/-- The symbol `-kᵢkⱼ/(|k|² + e)`. For `e = 0` it is the symbol of `RᵢRⱼ`, and for `e > 0` it is
smooth. -/
def regRieszSymbol (i j : Fin n) (e : ℝ) (k : ℝ^n) : ℝ :=
  -(k i * k j) / (‖k‖ ^ 2 + e)

/-- The derivative of `regRieszSymbol i j e` in the direction `l`. -/
def regRieszSymbolDeriv (i j l : Fin n) (e : ℝ) (k : ℝ^n) : ℝ :=
  -((if j = l then 1 else 0) * k i + (if i = l then 1 else 0) * k j) / (‖k‖ ^ 2 + e) +
    2 * (k i * k j * k l) / (‖k‖ ^ 2 + e) ^ 2

/-- At `e = 0` the regularized symbol is the symbol of the double Riesz transform. -/
theorem ofReal_regRieszSymbol_zero (i j : Fin n) (k : ℝ^n) :
    (regRieszSymbol i j 0 k : ℂ) = doubleRieszSymbol i j k := by
  simp [regRieszSymbol, doubleRieszSymbol]

/-- The regularized symbol is measurable. -/
theorem measurable_regRieszSymbol (i j : Fin n) (e : ℝ) : Measurable (regRieszSymbol i j e) := by
  unfold regRieszSymbol
  fun_prop

/-- The derivative of the regularized symbol is measurable. -/
theorem measurable_regRieszSymbolDeriv (i j l : Fin n) (e : ℝ) :
    Measurable (regRieszSymbolDeriv i j l e) := by
  unfold regRieszSymbolDeriv
  fun_prop

/-- The regularized symbols are bounded by one. -/
theorem abs_regRieszSymbol_le (i j : Fin n) {e : ℝ} (he : 0 ≤ e) (k : ℝ^n) :
    |regRieszSymbol i j e k| ≤ 1 := by
  unfold regRieszSymbol
  have hnum : |k i * k j| ≤ ‖k‖ ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul (EuclideanSpace.abs_apply_le_norm k i) (EuclideanSpace.abs_apply_le_norm k j)
      (abs_nonneg _) (norm_nonneg _)
  rcases (add_nonneg (sq_nonneg ‖k‖) he).eq_or_lt with h | h
  · rw [← h, div_zero, abs_zero]
    exact zero_le_one
  · rw [abs_div, abs_neg, abs_of_pos h, div_le_one h]
    linarith

/-- The derivatives of the regularized symbols are bounded by `4/|k|`, uniformly in `e ≥ 0`. -/
theorem abs_regRieszSymbolDeriv_le (i j l : Fin n) {e : ℝ} (he : 0 ≤ e) {k : ℝ^n} (hk : k ≠ 0) :
    |regRieszSymbolDeriv i j l e k| ≤ 4 / ‖k‖ := by
  have hN : 0 < ‖k‖ := norm_pos_iff.2 hk
  have hD : ‖k‖ ^ 2 ≤ ‖k‖ ^ 2 + e := le_add_of_nonneg_right he
  have hDpos : 0 < ‖k‖ ^ 2 + e := lt_of_lt_of_le (by positivity) hD
  have hi := EuclideanSpace.abs_apply_le_norm k i
  have hj := EuclideanSpace.abs_apply_le_norm k j
  have hl := EuclideanSpace.abs_apply_le_norm k l
  have h1 : |(if j = l then 1 else 0) * k i + (if i = l then 1 else 0) * k j| ≤ 2 * ‖k‖ := by
    refine (abs_add_le _ _).trans ?_
    have ha : |(if j = l then (1 : ℝ) else 0) * k i| ≤ ‖k‖ := by
      split_ifs <;> simp [hi]
    have hb : |(if i = l then (1 : ℝ) else 0) * k j| ≤ ‖k‖ := by
      split_ifs <;> simp [hj]
    linarith
  have h2 : |k i * k j * k l| ≤ ‖k‖ ^ 3 := by
    rw [abs_mul, abs_mul, pow_succ, sq]
    exact mul_le_mul (mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)) hl (abs_nonneg _)
      (by positivity)
  unfold regRieszSymbolDeriv
  calc |-((if j = l then 1 else 0) * k i + (if i = l then 1 else 0) * k j) / (‖k‖ ^ 2 + e) +
        2 * (k i * k j * k l) / (‖k‖ ^ 2 + e) ^ 2|
      ≤ |(if j = l then 1 else 0) * k i + (if i = l then 1 else 0) * k j| / (‖k‖ ^ 2 + e) +
        2 * |k i * k j * k l| / (‖k‖ ^ 2 + e) ^ 2 := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_div, abs_neg, abs_of_pos hDpos, abs_div, abs_mul, abs_of_pos (pow_pos hDpos 2),
          abs_of_pos (two_pos : (0 : ℝ) < 2)]
    _ ≤ 2 * ‖k‖ / ‖k‖ ^ 2 + 2 * ‖k‖ ^ 3 / (‖k‖ ^ 2) ^ 2 := by gcongr
    _ = 4 / ‖k‖ := by
        field_simp
        ring

/-- For `e > 0` the regularized symbol is smooth. -/
theorem contDiff_regRieszSymbol (i j : Fin n) {e : ℝ} (he : 0 < e) :
    ContDiff ℝ (⊤ : ℕ∞) (regRieszSymbol i j e) := by
  have hc (a : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun k : ℝ^n ↦ k a) :=
    (EuclideanSpace.proj (𝕜 := ℝ) a).contDiff
  exact ((hc i).mul (hc j)).neg.div ((contDiff_norm_sq ℝ).add contDiff_const)
    fun k ↦ (add_pos_of_nonneg_of_pos (sq_nonneg ‖k‖) he).ne'

/-- The partial derivative of the smooth symbol is `regRieszSymbolDeriv`. -/
theorem iteratedPartialDeriv_regRieszSymbol (i j l : Fin n) {e : ℝ} (he : 0 < e) (k : ℝ^n) :
    PDE.iteratedPartialDeriv [l] (regRieszSymbol i j e) k = regRieszSymbolDeriv i j l e k := by
  have hD : ‖k‖ ^ 2 + e ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg ‖k‖) he).ne'
  have hc (a : Fin n) : HasFDerivAt (fun y : ℝ^n ↦ y a) (EuclideanSpace.proj (𝕜 := ℝ) a) k :=
    (EuclideanSpace.proj (𝕜 := ℝ) a).hasFDerivAt
  have hnum := ((hc i).mul (hc j)).neg
  have hden : HasFDerivAt (fun y : ℝ^n ↦ ‖y‖ ^ 2 + e) (2 • innerSL ℝ k) k :=
    (hasStrictFDerivAt_norm_sq k).hasFDerivAt.add_const e
  have hinv := (hasDerivAt_inv hD).comp_hasFDerivAt k hden
  have hprod : HasFDerivAt (fun y : ℝ^n ↦ -(y i * y j) * (‖y‖ ^ 2 + e)⁻¹)
      ((-(k i * k j)) • (-((‖k‖ ^ 2 + e) ^ 2)⁻¹ • (2 : ℕ) • innerSL ℝ k) +
        (‖k‖ ^ 2 + e)⁻¹ • -(k i • EuclideanSpace.proj j + k j • EuclideanSpace.proj i)) k :=
    hnum.mul hinv
  have hfun : regRieszSymbol i j e = fun y ↦ -(y i * y j) * (‖y‖ ^ 2 + e)⁻¹ :=
    funext fun y ↦ div_eq_mul_inv _ _
  have hp (a : Fin n) : (EuclideanSpace.proj (𝕜 := ℝ) a) (EuclideanSpace.single l (1 : ℝ)) =
      if a = l then 1 else 0 := by simp
  have hin : (innerSL ℝ k) (EuclideanSpace.single l (1 : ℝ)) = k l := by
    simp [EuclideanSpace.inner_single_right]
  simp only [PDE.iteratedPartialDeriv, PDE.partialDeriv, hfun]
  rw [hprod.fderiv]
  simp only [regRieszSymbolDeriv, add_apply, smul_apply, neg_apply, hp, hin, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat]
  field_simp
  ring

/-- For `k ≠ 0` the regularized symbols and their derivatives converge as `e → 0`. -/
theorem tendsto_regRieszSymbol (i j l : Fin n) {k : ℝ^n} (hk : k ≠ 0) {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun m ↦ regRieszSymbol i j (e m) k) atTop (𝓝 (regRieszSymbol i j 0 k)) ∧
      Tendsto (fun m ↦ regRieszSymbolDeriv i j l (e m) k) atTop
        (𝓝 (regRieszSymbolDeriv i j l 0 k)) := by
  have hN : ‖k‖ ^ 2 + 0 ≠ 0 := by
    rw [add_zero]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hk)
  have hden : Tendsto (fun m ↦ ‖k‖ ^ 2 + e m) atTop (𝓝 (‖k‖ ^ 2 + 0)) := he.const_add _
  exact ⟨tendsto_const_nhds.div hden hN,
    (tendsto_const_nhds.div hden hN).add (tendsto_const_nhds.div (hden.pow 2) (pow_ne_zero 2 hN))⟩

/-! ## The product rule across the origin -/

/-- A real square bound `x² ≤ C` read in `[0, ∞]`, in the form that dominated convergence in `L²`
asks for. -/
private theorem eNorm_rpow_two_le_ofReal {x C : ℝ} (h : x ^ 2 ≤ C) :
    ‖x‖ₑ ^ (2 : ℝ≥0∞).toReal ≤ ENNReal.ofReal C := by
  rw [Real.eNorm_eq_ofReal_abs, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat,
    ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]
  exact ENNReal.ofReal_le_ofReal h

/-- **The product rule for the Riesz symbol across the origin**, `n ≥ 3`. If a real `f ∈ L²` has
weak partial derivatives `g i ∈ L²` on `ℝⁿ`, then `m f` has the weak derivative
`m (g l) + (∂_l m) f`, with `m(k) = -kᵢkⱼ/|k|²`. The symbols `-kᵢkⱼ/(|k|² + e)` are smooth, so
the rule holds for them; the limit `e → 0` is dominated by `|f|/|k|`, which is square integrable
by Hardy's inequality. -/
theorem hasWeakDerivativeOn_regRieszSymbol_zero_mul (hn : 3 ≤ n) (i j l : Fin n) {f : ℝ^n → ℝ}
    {g : Fin n → ℝ^n → ℝ} (hf : MemLp f 2 volume) (hg : ∀ a, MemLp (g a) 2 volume)
    (hweak : ∀ a, SobolevSpace.HasWeakDerivativeOn univ [a] f (g a)) :
    SobolevSpace.HasWeakDerivativeOn univ [l] (fun k ↦ regRieszSymbol i j 0 k * f k)
      (fun k ↦ regRieszSymbol i j 0 k * g l k + regRieszSymbolDeriv i j l 0 k * f k) := by
  have : NeZero n := ⟨by omega⟩
  have hne0 : ∀ᵐ k : ℝ^n, k ≠ 0 := by
    have : Nontrivial (ℝ^n) := ⟨⟨EuclideanSpace.single ⟨0, by omega⟩ 1, 0, fun h ↦ by
      simpa using congrArg (fun v : ℝ^n ↦ v ⟨0, by omega⟩) h⟩⟩
    exact Measure.ae_ne volume 0
  obtain ⟨hH, -⟩ := SobolevSpace.Hardy.integrable_hardy_and_bound hn hf hg hweak
  set e : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1) with hedef
  have he (m : ℕ) : 0 < e m := by positivity
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hμ : SobolevSpace.domainMeasure n univ = volume := Measure.restrict_univ
  -- measurability and membership of the products
  have hsm (c : ℝ) : AEStronglyMeasurable (regRieszSymbol i j c) (volume : Measure (ℝ^n)) :=
    (measurable_regRieszSymbol i j c).aestronglyMeasurable
  have hdm (c : ℝ) : AEStronglyMeasurable (regRieszSymbolDeriv i j l c)
      (volume : Measure (ℝ^n)) := (measurable_regRieszSymbolDeriv i j l c).aestronglyMeasurable
  have hsbound {c : ℝ} (hc : 0 ≤ c) :
      MemLp (regRieszSymbol i j c) ⊤ (volume : Measure (ℝ^n)) :=
    memLp_top_of_bound (hsm c) 1 (Eventually.of_forall fun k ↦ by
      simpa using abs_regRieszSymbol_le i j hc k)
  have hmul {c : ℝ} (hc : 0 ≤ c) {u : ℝ^n → ℝ} (hu : MemLp u 2 volume) :
      MemLp (fun k ↦ regRieszSymbol i j c k * u k) 2 volume := (hsbound hc).fun_mul hu
  -- `(∂_l m_c) f` is square integrable, by Hardy
  have hdsq {c : ℝ} (hc : 0 ≤ c) : ∀ᵐ k : ℝ^n,
      (regRieszSymbolDeriv i j l c k * f k) ^ 2 ≤ 16 * (f k ^ 2 / ‖k‖ ^ 2) := by
    filter_upwards [hne0] with k hk
    have h := abs_regRieszSymbolDeriv_le i j l hc hk
    have hN : 0 < ‖k‖ := norm_pos_iff.2 hk
    calc (regRieszSymbolDeriv i j l c k * f k) ^ 2
        = |regRieszSymbolDeriv i j l c k| ^ 2 * f k ^ 2 := by rw [mul_pow, sq_abs]
      _ ≤ (4 / ‖k‖) ^ 2 * f k ^ 2 := by gcongr
      _ = 16 * (f k ^ 2 / ‖k‖ ^ 2) := by
          field_simp
          ring
  have hfm := hf.aestronglyMeasurable
  have hgm := (hg l).aestronglyMeasurable
  have hdmem {c : ℝ} (hc : 0 ≤ c) :
      MemLp (fun k ↦ regRieszSymbolDeriv i j l c k * f k) 2 volume := by
    refine (memLp_two_iff_integrable_sq ((hdm c).mul hfm)).2 ((hH.const_mul 16).mono'
      (((hdm c).mul hfm).pow 2) ?_)
    filter_upwards [hdsq hc] with k hk
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hk
  -- the rule for the smooth symbols
  have hstep (m : ℕ) : SobolevSpace.HasWeakDerivativeOn univ [l]
      (fun k ↦ regRieszSymbol i j (e m) k * f k)
      (fun k ↦ regRieszSymbol i j (e m) k * g l k + regRieszSymbolDeriv i j l (e m) k * f k) := by
    have hderiv : (fun k ↦ PDE.iteratedPartialDeriv [l] (regRieszSymbol i j (e m)) k) =
        regRieszSymbolDeriv i j l (e m) :=
      funext fun k ↦ iteratedPartialDeriv_regRieszSymbol i j l (he m) k
    have hdtop : MemLp (fun k ↦ PDE.iteratedPartialDeriv [l] (regRieszSymbol i j (e m)) k) ⊤
        (SobolevSpace.domainMeasure n univ) := by
      rw [hderiv, hμ]
      refine memLp_top_of_bound (hdm _) (4 / e m) (Eventually.of_forall fun k ↦ ?_)
      rw [Real.norm_eq_abs]
      by_cases hk : ‖k‖ ≤ 1
      · -- inside the unit ball the denominators are at least `e`
        have hi := EuclideanSpace.abs_apply_le_norm k i
        have hj := EuclideanSpace.abs_apply_le_norm k j
        have hl := EuclideanSpace.abs_apply_le_norm k l
        have hDe : e m ≤ ‖k‖ ^ 2 + e m := le_add_of_nonneg_left (sq_nonneg _)
        have hDpos : 0 < ‖k‖ ^ 2 + e m := lt_of_lt_of_le (he m) hDe
        have h1 : |(if j = l then 1 else 0) * k i + (if i = l then 1 else 0) * k j| ≤ 2 := by
          refine (abs_add_le _ _).trans ?_
          have ha : |(if j = l then (1 : ℝ) else 0) * k i| ≤ 1 := by
            split_ifs <;> simp [hi.trans hk]
          have hb : |(if i = l then (1 : ℝ) else 0) * k j| ≤ 1 := by
            split_ifs <;> simp [hj.trans hk]
          linarith
        have h2 : |k i * k j * k l| ≤ ‖k‖ ^ 2 := by
          rw [abs_mul, abs_mul, sq]
          calc |k i| * |k j| * |k l| ≤ ‖k‖ * ‖k‖ * 1 :=
                mul_le_mul (mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)) (hl.trans hk)
                  (abs_nonneg _) (by positivity)
            _ = ‖k‖ * ‖k‖ := mul_one _
        have h3 : 2 * |k i * k j * k l| / (‖k‖ ^ 2 + e m) ^ 2 ≤ 2 / e m := by
          rw [div_le_div_iff₀ (pow_pos hDpos 2) (he m)]
          nlinarith [abs_nonneg (k i * k j * k l), sq_nonneg ‖k‖, he m]
        unfold regRieszSymbolDeriv
        calc |-((if j = l then 1 else 0) * k i + (if i = l then 1 else 0) * k j) /
              (‖k‖ ^ 2 + e m) + 2 * (k i * k j * k l) / (‖k‖ ^ 2 + e m) ^ 2|
            ≤ |(if j = l then 1 else 0) * k i + (if i = l then 1 else 0) * k j| /
                (‖k‖ ^ 2 + e m) + 2 * |k i * k j * k l| / (‖k‖ ^ 2 + e m) ^ 2 := by
              refine (abs_add_le _ _).trans (le_of_eq ?_)
              rw [abs_div, abs_neg, abs_of_pos hDpos, abs_div, abs_mul,
                abs_of_pos (pow_pos hDpos 2), abs_of_pos (two_pos : (0 : ℝ) < 2)]
          _ ≤ 2 / e m + 2 / e m := add_le_add (by gcongr) h3
          _ = 4 / e m := by ring
      · -- outside the unit ball `4 / ‖k‖ ≤ 4 / e`
        have hk0 : k ≠ 0 := fun h ↦ hk (by simp [h])
        have hN : 1 ≤ ‖k‖ := (not_le.1 hk).le
        have he1 : e m ≤ 1 := by
          rw [hedef]
          simp only
          rw [div_le_one (by positivity)]
          linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
        calc |regRieszSymbolDeriv i j l (e m) k| ≤ 4 / ‖k‖ :=
              abs_regRieszSymbolDeriv_le i j l (he m).le hk0
          _ ≤ 4 / e m := by
              gcongr
              exact he1.trans hN
    have h := SobolevSpace.hasWeakDerivativeOn_mul_contDiff_first (p := 2) (Ω := univ) (i := l)
      (hμ ▸ hf) (hμ ▸ hg l) (contDiff_regRieszSymbol i j (he m)) (hμ ▸ hsbound (he m).le) hdtop
      (hweak l)
    simpa only [iteratedPartialDeriv_regRieszSymbol i j l (he m)] using h
  -- the limit `e → 0`
  refine SobolevSpace.WeakChangeOfVariables.hasWeakDerivativeOn_of_tendsto_eLpNorm (p := 2)
    (fSeq := fun m k ↦ regRieszSymbol i j (e m) k * f k)
    (gSeq := fun m k ↦ regRieszSymbol i j (e m) k * g l k +
      regRieszSymbolDeriv i j l (e m) k * f k)
    (fun m ↦ hμ ▸ hmul (he m).le hf)
    (fun m ↦ hμ ▸ (hmul (he m).le (hg l)).add (hdmem (he m).le))
    (hμ ▸ hmul le_rfl hf) (hμ ▸ (hmul le_rfl (hg l)).add (hdmem le_rfl)) hstep ?_ ?_
  · rw [hμ]
    refine tendsto_eLpNorm_zero_of_dominated_convergence two_ne_zero ENNReal.ofNat_ne_top
      (fun k ↦ ENNReal.ofReal (4 * f k ^ 2))
      (Eventually.of_forall fun m ↦ ((hsm _).mul hfm).sub ((hsm _).mul hfm))
      (Eventually.of_forall fun m ↦ Eventually.of_forall fun k ↦ eNorm_rpow_two_le_ofReal ?_)
      (hf.integrable_sq.const_mul 4).lintegral_lt_top.ne ?_
    · have h1 := abs_regRieszSymbol_le i j (he m).le k
      have h2 := abs_regRieszSymbol_le i j le_rfl k
      have h3 : |regRieszSymbol i j (e m) k - regRieszSymbol i j 0 k| ≤ 2 :=
        (abs_sub _ _).trans (by linarith)
      calc (regRieszSymbol i j (e m) k * f k - regRieszSymbol i j 0 k * f k) ^ 2
          = |regRieszSymbol i j (e m) k - regRieszSymbol i j 0 k| ^ 2 * f k ^ 2 := by
            rw [← sub_mul, mul_pow, sq_abs]
        _ ≤ 2 ^ 2 * f k ^ 2 := by gcongr
        _ = 4 * f k ^ 2 := by norm_num
    · filter_upwards [hne0] with k hk
      have h := ((tendsto_regRieszSymbol i j l hk helim).1.sub_const
        (regRieszSymbol i j 0 k)).mul_const (f k)
      simpa only [sub_self, zero_mul, sub_mul] using h
  · rw [hμ]
    refine tendsto_eLpNorm_zero_of_dominated_convergence two_ne_zero ENNReal.ofNat_ne_top
      (fun k ↦ ENNReal.ofReal (8 * g l k ^ 2 + 128 * (f k ^ 2 / ‖k‖ ^ 2)))
      (Eventually.of_forall fun m ↦
        (((hsm _).mul hgm).add ((hdm _).mul hfm)).sub (((hsm _).mul hgm).add ((hdm _).mul hfm)))
      (Eventually.of_forall fun m ↦ ?_)
      (((hg l).integrable_sq.const_mul 8).add (hH.const_mul 128)).lintegral_lt_top.ne ?_
    · filter_upwards [hdsq (he m).le, hdsq le_rfl] with k hk1 hk2
      refine eNorm_rpow_two_le_ofReal ?_
      have h1 := abs_regRieszSymbol_le i j (he m).le k
      have h2 := abs_regRieszSymbol_le i j le_rfl k
      have h3 : ((regRieszSymbol i j (e m) k - regRieszSymbol i j 0 k) * g l k) ^ 2 ≤
          4 * g l k ^ 2 := by
        have : |regRieszSymbol i j (e m) k - regRieszSymbol i j 0 k| ≤ 2 :=
          (abs_sub _ _).trans (by linarith)
        calc ((regRieszSymbol i j (e m) k - regRieszSymbol i j 0 k) * g l k) ^ 2
            = |regRieszSymbol i j (e m) k - regRieszSymbol i j 0 k| ^ 2 * g l k ^ 2 := by
              rw [mul_pow, sq_abs]
          _ ≤ 2 ^ 2 * g l k ^ 2 := by gcongr
          _ = 4 * g l k ^ 2 := by norm_num
      -- `(a + b - c)² ≤ 2 a² + 4 b² + 4 c²`
      nlinarith [sq_nonneg ((regRieszSymbol i j (e m) k - regRieszSymbol i j 0 k) * g l k -
          (regRieszSymbolDeriv i j l (e m) k * f k - regRieszSymbolDeriv i j l 0 k * f k)),
        sq_nonneg (regRieszSymbolDeriv i j l (e m) k * f k + regRieszSymbolDeriv i j l 0 k * f k)]
    · filter_upwards [hne0] with k hk
      obtain ⟨hs, hd⟩ := tendsto_regRieszSymbol i j l hk helim
      have h := ((hs.sub_const (regRieszSymbol i j 0 k)).mul_const (g l k)).add
        ((hd.sub_const (regRieszSymbolDeriv i j l 0 k)).mul_const (f k))
      simp only [sub_self, zero_mul, add_zero] at h
      refine h.congr fun m ↦ ?_
      ring

/-- The product rule of `hasWeakDerivativeOn_regRieszSymbol_zero_mul` for complex `L²` classes:
if `G ∈ L²(ℝⁿ; ℂ)` has complex weak partial derivatives `D a ∈ L²`, then `m G` has the complex
weak derivative `m (D l) + (∂_l m) G`, with `m` the symbol of `RᵢRⱼ`. -/
theorem hasComplexWeakDerivativeOn_doubleRieszSymbol_mul (hn : 3 ≤ n) (i j l : Fin n)
    (G : Lp ℂ 2 (volume : Measure (ℝ^n))) (D : Fin n → Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hD : ∀ a, SobolevSpace.HasComplexWeakDerivativeOn univ [a] G (D a)) :
    SobolevSpace.HasComplexWeakDerivativeOn univ [l] (fun k ↦ doubleRieszSymbol i j k * G k)
      (fun k ↦ doubleRieszSymbol i j k * D l k + (regRieszSymbolDeriv i j l 0 k : ℂ) * G k) := by
  have hre := hasWeakDerivativeOn_regRieszSymbol_zero_mul hn i j l (f := fun x ↦ (G x).re)
    (g := fun a x ↦ (D a x).re) (Lp.memLp G).re (fun a ↦ (Lp.memLp (D a)).re) fun a ↦ (hD a).1
  have him := hasWeakDerivativeOn_regRieszSymbol_zero_mul hn i j l (f := fun x ↦ (G x).im)
    (g := fun a x ↦ (D a x).im) (Lp.memLp G).im (fun a ↦ (Lp.memLp (D a)).im) fun a ↦ (hD a).2
  refine ⟨?_, ?_⟩
  · convert hre using 2 <;>
      simp [← ofReal_regRieszSymbol_zero]
  · convert him using 2 <;>
      simp [← ofReal_regRieszSymbol_zero]

/-! ## Moments and derivatives of the transform -/

/-- The multiplier of a moment on the Fourier side: `‖-2πi t z‖² = (2π)² t² ‖z‖²`. -/
private theorem norm_moment_sq (t : ℝ) (z : ℂ) :
    ‖-(2 * π * Complex.I) * (t : ℂ) * z‖ ^ 2 = (2 * π) ^ 2 * (t ^ 2 * ‖z‖ ^ 2) := by
  rw [norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    show ‖(2 * π : ℂ)‖ = 2 * π by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)], Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
  ring

/-- A moment of `u` in `L²` gives a weak derivative of `û` in `L²`, with
`‖∂_l û‖² = (2π)² ∫ x_l² |u|²`. -/
theorem exists_hasComplexWeakDerivativeOn_fourier_of_moment (u : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (l : Fin n) (hu : Integrable (fun x ↦ x l ^ 2 * ‖u x‖ ^ 2)) :
    ∃ D : Lp ℂ 2 (volume : Measure (ℝ^n)),
      SobolevSpace.HasComplexWeakDerivativeOn univ [l]
        (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) D ∧
      ‖D‖ ^ 2 = (2 * π) ^ 2 * ∫ x, x l ^ 2 * ‖u x‖ ^ 2 := by
  have hnorm (x : ℝ^n) : ‖-(2 * π * Complex.I) * (x l : ℂ) * u x‖ ^ 2 =
      (2 * π) ^ 2 * (x l ^ 2 * ‖u x‖ ^ 2) := norm_moment_sq (x l) (u x)
  have hmeas : AEStronglyMeasurable (fun x : ℝ^n ↦ -(2 * π * Complex.I) * (x l : ℂ) * u x)
      volume := by
    refine AEStronglyMeasurable.mul ?_ (Lp.aestronglyMeasurable u)
    exact (Measurable.aestronglyMeasurable (by fun_prop))
  have hmem : MemLp (fun x : ℝ^n ↦ -(2 * π * Complex.I) * (x l : ℂ) * u x) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
    simp_rw [hnorm]
    exact hu.const_mul _
  refine ⟨𝓕 (hmem.toLp _), (SobolevSpace.hasComplexWeakDerivativeOn_fourier_iff [l] u _).2 ?_, ?_⟩
  · simp only [prod_single_apply, fourierInv_fourier_eq]
    exact hmem.coeFn_toLp.symm
  · rw [Lp.norm_fourier_eq, Lp.norm_sq_eq_integral_norm_sq, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hx, hnorm]

/-- A weak derivative of `û` in `L²` gives a moment of `u` in `L²`, with
`(2π)² ∫ x_l² |u|² = ‖∂_l û‖²`. -/
theorem integrable_moment_of_hasComplexWeakDerivativeOn_fourier
    (u V : Lp ℂ 2 (volume : Measure (ℝ^n))) (l : Fin n)
    (h : SobolevSpace.HasComplexWeakDerivativeOn univ [l]
      (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) V) :
    Integrable (fun x ↦ x l ^ 2 * ‖u x‖ ^ 2) ∧
      (2 * π) ^ 2 * ∫ x, x l ^ 2 * ‖u x‖ ^ 2 = ‖V‖ ^ 2 := by
  have hae := (SobolevSpace.hasComplexWeakDerivativeOn_fourier_iff [l] u V).1 h
  simp only [prod_single_apply] at hae
  have hnorm (x : ℝ^n) : ‖-(2 * π * Complex.I) * (x l : ℂ) * u x‖ ^ 2 =
      (2 * π) ^ 2 * (x l ^ 2 * ‖u x‖ ^ 2) := norm_moment_sq (x l) (u x)
  have hfun : (fun x ↦ ‖(𝓕⁻ V : Lp ℂ 2 (volume : Measure (ℝ^n))) x‖ ^ 2) =ᵐ[volume]
      fun x ↦ (2 * π) ^ 2 * (x l ^ 2 * ‖u x‖ ^ 2) := by
    filter_upwards [hae] with x hx
    rw [← hx, hnorm]
  have hint : Integrable (fun x : ℝ^n ↦ (2 * π) ^ 2 * (x l ^ 2 * ‖u x‖ ^ 2)) :=
    (Lp.memLp (𝓕⁻ V)).norm.integrable_sq.congr hfun
  have hpos : (0 : ℝ) < (2 * π) ^ 2 := by positivity
  refine ⟨(hint.const_mul ((2 * π) ^ 2)⁻¹).congr (Eventually.of_forall fun x ↦ ?_), ?_⟩
  · simp only
    rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  · rw [← integral_const_mul, ← integral_congr_ae hfun, ← Lp.norm_sq_eq_integral_norm_sq,
      ← Lp.norm_fourier_eq, fourier_fourierInv_eq]

/-! ## The weighted bound -/

/-- **The double Riesz transforms on `L²` with the weight `|x|²`**, `n ≥ 3`. If `f ∈ L²(ℝⁿ; ℂ)`
and `|x| f ∈ L²`, then `|x| RᵢRⱼ f ∈ L²` and
`∫ |x|² |RᵢRⱼ f|² ≤ (2 + 128 n) ∫ |x|² |f|²`.

On the Fourier side `x_l RᵢRⱼ f` is `∂_l (m f̂) = m ∂_l f̂ + (∂_l m) f̂` up to the factor `i/2π`.
The first term is bounded by `x_l f` and the second by Hardy's inequality. -/
theorem integrable_norm_sq_mul_doubleRiesz (hn : 3 ≤ n) (i j : Fin n)
    (f : Lp ℂ 2 (volume : Measure (ℝ^n))) (hf : Integrable (fun x ↦ ‖x‖ ^ 2 * ‖f x‖ ^ 2)) :
    Integrable (fun x ↦ ‖x‖ ^ 2 * ‖doubleRiesz i j f x‖ ^ 2) ∧
      ∫ x, ‖x‖ ^ 2 * ‖doubleRiesz i j f x‖ ^ 2 ≤
        (2 + 128 * n) * ∫ x, ‖x‖ ^ 2 * ‖f x‖ ^ 2 := by
  have hπ : (0 : ℝ) < (2 * π) ^ 2 := by positivity
  have hne0 : ∀ᵐ k : ℝ^n, k ≠ 0 := by
    have : Nontrivial (ℝ^n) := ⟨⟨EuclideanSpace.single ⟨0, by omega⟩ 1, 0, fun h ↦ by
      simpa using congrArg (fun v : ℝ^n ↦ v ⟨0, by omega⟩) h⟩⟩
    exact Measure.ae_ne volume 0
  -- the coordinate moments of `f`
  have hcoord (l : Fin n) : Integrable (fun x : ℝ^n ↦ x l ^ 2 * ‖f x‖ ^ 2) := by
    refine hf.mono' (((measurable_pi_apply l).comp (WithLp.measurable_ofLp 2 _)).pow_const 2
      |>.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable f).norm.pow 2)) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity)]
    have := EuclideanSpace.abs_apply_le_norm x l
    have h2 : x l ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hsumf : ∫ x, ‖x‖ ^ 2 * ‖f x‖ ^ 2 = ∑ l, ∫ x, x l ^ 2 * ‖f x‖ ^ 2 := by
    rw [← integral_finsetSum _ fun l _ ↦ hcoord l]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
  choose D hD hDnorm using fun l ↦ exists_hasComplexWeakDerivativeOn_fourier_of_moment f l
    (hcoord l)
  have hS : ∑ l, ‖D l‖ ^ 2 = (2 * π) ^ 2 * ∫ x, ‖x‖ ^ 2 * ‖f x‖ ^ 2 := by
    simp_rw [hDnorm]
    rw [← Finset.mul_sum, hsumf]
  -- Hardy for the transform
  obtain ⟨hHardy, hHardy'⟩ := SobolevSpace.Hardy.integrable_hardy_complex hn (𝓕 f) D hD
  -- the derivative of `m f̂` in the direction `l`
  have key (l : Fin n) : Integrable (fun x : ℝ^n ↦ x l ^ 2 * ‖doubleRiesz i j f x‖ ^ 2) ∧
      (2 * π) ^ 2 * ∫ x, x l ^ 2 * ‖doubleRiesz i j f x‖ ^ 2 ≤
        2 * ‖D l‖ ^ 2 + 128 * ∑ a, ‖D a‖ ^ 2 := by
    set W : ℝ^n → ℂ := fun k ↦ doubleRieszSymbol i j k * D l k +
      (regRieszSymbolDeriv i j l 0 k : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) k with hW
    have hWmeas : AEStronglyMeasurable W volume :=
      ((measurable_doubleRieszSymbol i j).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable _)).add
      ((Complex.measurable_ofReal.comp (measurable_regRieszSymbolDeriv i j l 0)
        ).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _))
    have hWle : ∀ᵐ k : ℝ^n, ‖W k‖ ^ 2 ≤ 2 * ‖D l k‖ ^ 2 +
        32 * (‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) k‖ ^ 2 / ‖k‖ ^ 2) := by
      filter_upwards [hne0] with k hk
      have hN : 0 < ‖k‖ := norm_pos_iff.2 hk
      have h1 : ‖doubleRieszSymbol i j k * D l k‖ ≤ ‖D l k‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (norm_doubleRieszSymbol_le i j k)
      have h2 : ‖(regRieszSymbolDeriv i j l 0 k : ℂ) *
          (𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) k‖ ≤
          4 / ‖k‖ * ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) k‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (abs_regRieszSymbolDeriv_le i j l le_rfl hk)
          (norm_nonneg _)
      have h3 : ‖W k‖ ≤ ‖D l k‖ + 4 / ‖k‖ * ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) k‖ :=
        (norm_add_le _ _).trans (add_le_add h1 h2)
      have h4 : (‖D l k‖ + 4 / ‖k‖ * ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) k‖) ^ 2 ≤
          2 * ‖D l k‖ ^ 2 + 32 * (‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) k‖ ^ 2 / ‖k‖ ^ 2) := by
        have e : 32 * (‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) k‖ ^ 2 / ‖k‖ ^ 2) =
            2 * (4 / ‖k‖ * ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) k‖) ^ 2 := by
          field_simp
          ring
        rw [e]
        nlinarith [sq_nonneg (‖D l k‖ - 4 / ‖k‖ * ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) k‖)]
      exact (pow_le_pow_left₀ (norm_nonneg _) h3 2).trans h4
    have hmaj : Integrable (fun k : ℝ^n ↦ 2 * ‖D l k‖ ^ 2 +
        32 * (‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) k‖ ^ 2 / ‖k‖ ^ 2)) :=
      ((Lp.memLp (D l)).norm.integrable_sq.const_mul 2).add (hHardy.const_mul 32)
    have hWint : Integrable (fun k ↦ ‖W k‖ ^ 2) :=
      hmaj.mono' (hWmeas.norm.pow 2) (hWle.mono fun k hk ↦ by
        rwa [Real.norm_of_nonneg (sq_nonneg _)])
    have hWmem : MemLp W 2 volume := (memLp_two_iff_integrable_sq_norm hWmeas).2 hWint
    have hweak : SobolevSpace.HasComplexWeakDerivativeOn univ [l]
        (𝓕 (doubleRiesz i j f) : Lp ℂ 2 (volume : Measure (ℝ^n))) (hWmem.toLp W) := by
      refine (hasComplexWeakDerivativeOn_doubleRieszSymbol_mul hn i j l (𝓕 f) D hD).congr_ae
        ?_ ?_
      · simpa [SobolevSpace.domainMeasure] using (fourier_doubleRiesz_ae i j f).symm
      · simpa [SobolevSpace.domainMeasure] using hWmem.coeFn_toLp.symm
    obtain ⟨hint, heq⟩ := integrable_moment_of_hasComplexWeakDerivativeOn_fourier
      (doubleRiesz i j f) (hWmem.toLp W) l hweak
    refine ⟨hint, ?_⟩
    rw [heq, Lp.norm_sq_eq_integral_norm_sq]
    calc ∫ k, ‖(hWmem.toLp W) k‖ ^ 2 = ∫ k, ‖W k‖ ^ 2 :=
          integral_congr_ae (hWmem.coeFn_toLp.mono fun k hk ↦ by simp only [hk])
      _ ≤ ∫ k, (2 * ‖D l k‖ ^ 2 +
            32 * (‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) k‖ ^ 2 / ‖k‖ ^ 2)) :=
          integral_mono_ae hWint hmaj hWle
      _ = 2 * ‖D l‖ ^ 2 + 32 * ∫ k, ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) k‖ ^ 2 / ‖k‖ ^ 2 := by
          rw [integral_add ((Lp.memLp (D l)).norm.integrable_sq.const_mul 2)
            (hHardy.const_mul 32), integral_const_mul, integral_const_mul,
            ← Lp.norm_sq_eq_integral_norm_sq]
      _ ≤ 2 * ‖D l‖ ^ 2 + 128 * ∑ a, ‖D a‖ ^ 2 := by linarith
  -- sum over the directions
  have hfun : (fun x : ℝ^n ↦ ‖x‖ ^ 2 * ‖doubleRiesz i j f x‖ ^ 2) =
      fun x ↦ ∑ l, x l ^ 2 * ‖doubleRiesz i j f x‖ ^ 2 :=
    funext fun x ↦ by rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun l _ ↦ (key l).1, ?_⟩
  rw [integral_finsetSum _ fun l _ ↦ (key l).1]
  have hsum : (2 * π) ^ 2 * ∑ l, ∫ x, x l ^ 2 * ‖doubleRiesz i j f x‖ ^ 2 ≤
      (2 + 128 * n) * ∑ a, ‖D a‖ ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ l, (2 * π) ^ 2 * ∫ x, x l ^ 2 * ‖doubleRiesz i j f x‖ ^ 2
        ≤ ∑ l, (2 * ‖D l‖ ^ 2 + 128 * ∑ a, ‖D a‖ ^ 2) := Finset.sum_le_sum fun l _ ↦ (key l).2
      _ = (2 + 128 * n) * ∑ a, ‖D a‖ ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [hS] at hsum
  refine le_of_mul_le_mul_left (hsum.trans_eq ?_) hπ
  ring

end PDE.Analysis.Fourier
