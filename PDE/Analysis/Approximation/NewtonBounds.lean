/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.NodalPolynomialBounds
public import PDE.Analysis.Approximation.PolynomialRemainder

/-!
# Bounds on an interval from four or three equally spaced values

Chen and Hou, Part II, Supplementary Sec 8.1, bound a function on `[a, a + 3h]` by its values
`v_i = f(a + i h)` at four equally spaced nodes. The interpolating cubic, written in the local
variable `t = (x - a) / h` as the Newton polynomial
`v₀ + t D₁ + t (t - 1) D₂,₀ / 2 + t (t - 1) (t - 2) D₃ / 6` with forward differences
`D₂,₀ = v₂ - 2v₁ + v₀`, `D₂,₁ = v₃ - 2v₂ + v₁`, `D₃ = v₃ - 3v₂ + 3v₁ - v₀` (`newtonCubic`),
is bounded on each third of the interval by its linear part through the two nearest nodes plus
`c₁ |D₂| + c₂ |D₃|` with `c₁ = 1/8` and `c₂ = 1/(9 √3)` (`abs_newtonCubic_le`, (8.6)); the
interpolation error is at most `L h⁴ / 24` for an `L`-Lipschitz third derivative
(`abs_sub_newtonCubic_le`, (8.3) with (8.4)). Together they bound the function
(`abs_le_newtonCubicBound`). The three-node version is (8.7)-(8.9): the quadratic `N₂` has error
`L h³ / (9 √3)` for an `L`-Lipschitz second derivative and is bounded on each half by its linear
part plus `|D₂| / 8`.

Here `L` is a Lipschitz constant of the third (second) derivative; `lipschitz_of_abs_deriv_le`
gives it from a bound on the fourth (third) derivative.

In two variables (Sec 8.1.3) the bound is applied in `x` at fixed `y` and then to the values
`f(xᵢ, y)` and the differences `D₂,₀ f(y)`, `D₂,₁ f(y)`, `D₃ f(y)` as functions of `y`;
`newtonCubicBound_le` turns bounds of these into a bound of `newtonCubicBound`, and
`abs_le_newtonCubic_tensor` is the first stage at a fixed `y`, with the bounds of the values and
differences as hypotheses. The second stage, bounding those one-variable functions of `y` by
`abs_le_newtonCubicBound` (their third `y`-derivatives are combinations of those of `f(xᵢ, ·)`),
is left to the certificate that uses it.

## Main definitions

* `newtonCubic`: the Newton form of the cubic through `(i, vᵢ)`, `i = 0, 1, 2, 3`.
* `newtonCubicBound`: the bound (8.6), with the linear part on each third bounded by its two
  nearest values.
* `newtonQuadratic`: the Newton form `N₂` of the quadratic through `(i, vᵢ)`, `i = 0, 1, 2` (8.7).

## Main results

* `abs_newtonCubic_le`: on `[0, 3]` the Newton cubic is at most `newtonCubicBound` (8.6).
* `abs_sub_newtonCubic_le`: for an `L`-Lipschitz third derivative on `[a, a + 3h]`, the Newton
  cubic through the four values differs from `f` by at most `L h⁴ / 24` there (8.3)-(8.4).
* `abs_le_newtonCubicBound`: `|f| ≤ newtonCubicBound + L h⁴ / 24` on `[a, a + 3h]`.
* `abs_sub_newtonQuadratic_le`: for an `L`-Lipschitz second derivative on `[a, a + 2h]`,
  `|f - N₂| ≤ L h³ / (9 √3)` there (8.8).
* `abs_newtonQuadratic_le_left`: `|N₂| ≤ max(|v₀|, |v₁|) + |v₀ - 2v₁ + v₂| / 8` on `[0, 1]` (8.9);
  `abs_newtonQuadratic_le_right` is the bound on `[1, 2]`.
* `newtonCubicBound_le`: bounds of the four values and of the three differences bound
  `newtonCubicBound`.
* `abs_le_newtonCubic_tensor`: the first stage of the cell estimate of Sec 8.1.3, at a fixed `y`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II (in the same PDF), Section 8.1, (8.1)-(8.9).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis.Approximation

open Set Polynomial

/-- A convex combination of two numbers is at most the larger absolute value. -/
theorem abs_lerp_le {u w s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    |u + s * (w - u)| ≤ max |u| |w| := by
  have hid : u + s * (w - u) = (1 - s) * u + s * w := by ring
  rw [hid]
  calc |(1 - s) * u + s * w| ≤ (1 - s) * |u| + s * |w| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hs.2]), abs_of_nonneg hs.1]
    _ ≤ (1 - s) * max |u| |w| + s * max |u| |w| :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [hs.2]))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hs.1)
    _ = max |u| |w| := by ring

/-- Equally spaced nodes `a + i h` are distinct for `h ≠ 0`. -/
theorem equispaced_injective {a h : ℝ} (hh : h ≠ 0) (k : ℕ) :
    Function.Injective fun i : Fin (k + 1) ↦ a + (i : ℕ) * h := by
  intro i j hij
  have hc : ((i : ℕ) : ℝ) = (j : ℕ) := mul_right_cancel₀ hh (add_left_cancel hij)
  exact Fin.ext (by exact_mod_cast hc)

/-- Equally spaced nodes `a + i h`, `i ≤ k`, lie in `[a, a + k h]` for `h ≥ 0`. -/
theorem equispaced_mem {a h : ℝ} (hh : 0 ≤ h) {k : ℕ} (i : Fin (k + 1)) :
    a + (i : ℕ) * h ∈ Icc a (a + k * h) := by
  have hi : ((i : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
  constructor
  · nlinarith [(Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ (i : ℕ))]
  · nlinarith

/-! ### The cubic through four equally spaced values -/

/-- The Newton form of the cubic through `(i, vᵢ)`, `i = 0, 1, 2, 3`, in the local variable `t`. -/
noncomputable def newtonCubic (v₀ v₁ v₂ v₃ t : ℝ) : ℝ :=
  v₀ + t * (v₁ - v₀) + t * (t - 1) / 2 * (v₂ - 2 * v₁ + v₀) +
    t * (t - 1) * (t - 2) / 6 * (v₃ - 3 * v₂ + 3 * v₁ - v₀)

/-- The bound of Supp II (8.6), with the linear part on each third bounded by its two nearest
values. -/
noncomputable def newtonCubicBound (v₀ v₁ v₂ v₃ : ℝ) : ℝ :=
  max (max (max |v₀| |v₁| + |v₂ - 2 * v₁ + v₀| / 8) (max |v₁| |v₂| + |v₂ - 2 * v₁ + v₀| / 8))
      (max |v₂| |v₃| + |v₃ - 2 * v₂ + v₁| / 8) +
    |v₃ - 3 * v₂ + 3 * v₁ - v₀| / (9 * Real.sqrt 3)

/-- **Supp II (8.6).** On `[0, 3]` the Newton cubic is at most `newtonCubicBound`: on each third
its linear part through the nearest two nodes, plus `|D₂| / 8` for the second difference of the
three nodes used and `|D₃| / (9 √3)`. This is at most the bound
`max(max_{i ≤ 2} |vᵢ| + c₁ |D₂,₀|, max_{1 ≤ i ≤ 3} |vᵢ| + c₁ |D₂,₁|) + c₂ |D₃|` of (8.6). -/
theorem abs_newtonCubic_le {v₀ v₁ v₂ v₃ t : ℝ} (ht : t ∈ Icc (0 : ℝ) 3) :
    |newtonCubic v₀ v₁ v₂ v₃ t| ≤ newtonCubicBound v₀ v₁ v₂ v₃ := by
  set D₂₀ := v₂ - 2 * v₁ + v₀
  set D₂₁ := v₃ - 2 * v₂ + v₁
  set D₃ := v₃ - 3 * v₂ + 3 * v₁ - v₀
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hcube (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 2) :
      |s * (s - 1) * (s - 2) / 6 * D₃| ≤ |D₃| / (9 * Real.sqrt 3) := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have := abs_cubicNodal_le hs
    calc |s * (s - 1) * (s - 2)| / 6 * |D₃| ≤ 2 / (3 * Real.sqrt 3) / 6 * |D₃| := by gcongr
      _ = |D₃| / (9 * Real.sqrt 3) := by field_simp; ring
  have hquad {p q : ℝ} (s : ℝ) (hs : s ∈ Icc p q) (hpq : q - p = 1) (D : ℝ) :
      |(s - p) * (s - q) / 2 * D| ≤ |D| / 8 := by
    rw [abs_mul, abs_div, abs_two]
    have := abs_sub_mul_sub_le hs
    rw [hpq] at this
    calc |(s - p) * (s - q)| / 2 * |D| ≤ 1 ^ 2 / 4 / 2 * |D| := by gcongr
      _ = |D| / 8 := by ring
  have hB : ∀ X Y : ℝ, X ≤ max (max X Y) (max |v₂| |v₃| + |D₂₁| / 8) := fun X Y ↦
    (le_max_left _ _).trans (le_max_left _ _)
  rcases le_total t 1 with h1 | h1
  · -- first third: nodes 0, 1, 2
    have hid : newtonCubic v₀ v₁ v₂ v₃ t = (v₀ + t * (v₁ - v₀)) + (t - 0) * (t - 1) / 2 * D₂₀ +
        t * (t - 1) * (t - 2) / 6 * D₃ := by unfold newtonCubic; ring
    rw [hid]
    have := abs_lerp_le (u := v₀) (w := v₁) ⟨ht.1, h1⟩
    have := hquad t ⟨ht.1, h1⟩ (by ring) D₂₀
    have := hcube t ⟨ht.1, by linarith⟩
    have := hB (max |v₀| |v₁| + |D₂₀| / 8) (max |v₁| |v₂| + |D₂₀| / 8)
    unfold newtonCubicBound
    calc _ ≤ |v₀ + t * (v₁ - v₀)| + |(t - 0) * (t - 1) / 2 * D₂₀| +
          |t * (t - 1) * (t - 2) / 6 * D₃| := abs_add_three _ _ _
      _ ≤ _ := by linarith
  rcases le_total t 2 with h2 | h2
  · -- middle third: nodes 1, 2 for the linear part
    have hid : newtonCubic v₀ v₁ v₂ v₃ t = (v₁ + (t - 1) * (v₂ - v₁)) +
        (t - 1) * (t - 2) / 2 * D₂₀ + t * (t - 1) * (t - 2) / 6 * D₃ := by unfold newtonCubic; ring
    rw [hid]
    have := abs_lerp_le (u := v₁) (w := v₂) (s := t - 1) ⟨by linarith, by linarith⟩
    have := hquad t ⟨h1, h2⟩ (by ring) D₂₀
    have := hcube t ⟨ht.1, h2⟩
    have := (le_max_right (max |v₀| |v₁| + |D₂₀| / 8) (max |v₁| |v₂| + |D₂₀| / 8)).trans
      (le_max_left _ (max |v₂| |v₃| + |D₂₁| / 8))
    unfold newtonCubicBound
    calc _ ≤ |v₁ + (t - 1) * (v₂ - v₁)| + |(t - 1) * (t - 2) / 2 * D₂₀| +
          |t * (t - 1) * (t - 2) / 6 * D₃| := abs_add_three _ _ _
      _ ≤ _ := by linarith
  · -- last third: nodes 1, 2, 3
    have hid : newtonCubic v₀ v₁ v₂ v₃ t = (v₂ + (t - 2) * (v₃ - v₂)) +
        (t - 2) * (t - 3) / 2 * D₂₁ + (t - 1) * (t - 1 - 1) * (t - 1 - 2) / 6 * D₃ := by
      unfold newtonCubic; ring
    rw [hid]
    have := abs_lerp_le (u := v₂) (w := v₃) (s := t - 2) ⟨by linarith, by linarith [ht.2]⟩
    have := hquad t ⟨h2, ht.2⟩ (by ring) D₂₁
    have := hcube (t - 1) ⟨by linarith, by linarith [ht.2]⟩
    have := le_max_right (max (max |v₀| |v₁| + |D₂₀| / 8) (max |v₁| |v₂| + |D₂₀| / 8))
      (max |v₂| |v₃| + |D₂₁| / 8)
    unfold newtonCubicBound
    calc _ ≤ |v₂ + (t - 2) * (v₃ - v₂)| + |(t - 2) * (t - 3) / 2 * D₂₁| +
          |(t - 1) * (t - 1 - 1) * (t - 1 - 2) / 6 * D₃| := abs_add_three _ _ _
      _ ≤ _ := by linarith

/-- The Newton cubic as a polynomial in the physical variable. -/
noncomputable def newtonCubicPoly (a h v₀ v₁ v₂ v₃ : ℝ) : ℝ[X] :=
  C v₀ + (C h⁻¹ * (X - C a)) * C (v₁ - v₀) +
    (C h⁻¹ * (X - C a)) * (C h⁻¹ * (X - C a) - 1) * C ((v₂ - 2 * v₁ + v₀) / 2) +
    (C h⁻¹ * (X - C a)) * (C h⁻¹ * (X - C a) - 1) * (C h⁻¹ * (X - C a) - 2) *
      C ((v₃ - 3 * v₂ + 3 * v₁ - v₀) / 6)

/-- The Newton cubic has degree at most `3`. -/
theorem newtonCubicPoly_natDegree_le (a h v₀ v₁ v₂ v₃ : ℝ) :
    (newtonCubicPoly a h v₀ v₁ v₂ v₃).natDegree ≤ 3 := by
  unfold newtonCubicPoly
  compute_degree

/-- At `x` the polynomial `newtonCubicPoly` takes the value of `newtonCubic` at `t = (x - a) / h`.
-/
theorem eval_newtonCubicPoly (a h v₀ v₁ v₂ v₃ x : ℝ) :
    (newtonCubicPoly a h v₀ v₁ v₂ v₃).eval x = newtonCubic v₀ v₁ v₂ v₃ ((x - a) / h) := by
  simp only [newtonCubicPoly, newtonCubic, eval_add, eval_mul, eval_C, eval_sub, eval_X,
    eval_one, eval_ofNat]
  ring

/-- **Supp II (8.3), (8.4).** If the third derivative of `f = Φ 0` is `L`-Lipschitz on
`[a, a + 3h]`, the Newton cubic through the four equally spaced values differs from `f` by at most
`L h⁴ / 24` there. -/
theorem abs_sub_newtonCubic_le {a h L : ℝ} (hh : 0 < h) (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < 3, ContinuousOn (Φ j) (Icc a (a + 3 * h)))
    (hderiv : ∀ j < 3, ∀ z ∈ Ioo a (a + 3 * h), HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc a (a + 3 * h), ∀ y ∈ Icc a (a + 3 * h), |Φ 3 x - Φ 3 y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Icc a (a + 3 * h)) :
    |Φ 0 x - newtonCubic (Φ 0 a) (Φ 0 (a + h)) (Φ 0 (a + 2 * h)) (Φ 0 (a + 3 * h))
      ((x - a) / h)| ≤ L * h ^ 4 / 24 := by
  set nodes : Fin 4 → ℝ := fun i ↦ a + (i : ℕ) * h
  have hinj : Function.Injective nodes := equispaced_injective hh.ne' 3
  have hmem : ∀ i, nodes i ∈ Icc a (a + 3 * h) := by
    intro i
    have hi := equispaced_mem (a := a) (k := 3) hh.le i
    rwa [Nat.cast_ofNat] at hi
  have hq := newtonCubicPoly_natDegree_le a h (Φ 0 a) (Φ 0 (a + h)) (Φ 0 (a + 2 * h))
    (Φ 0 (a + 3 * h))
  have hval : ∀ i, (newtonCubicPoly a h (Φ 0 a) (Φ 0 (a + h)) (Φ 0 (a + 2 * h))
      (Φ 0 (a + 3 * h))).eval (nodes i) = Φ 0 (nodes i) := by
    intro i
    rw [eval_newtonCubicPoly, show (nodes i - a) / h = ((i : ℕ) : ℝ) by
      simp only [nodes]; field_simp; ring]
    fin_cases i <;>
      simp only [nodes, newtonCubic, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
        zero_mul, add_zero, one_mul] <;> ring
  have hrem := abs_sub_eval_le_of_nodes Φ hcontinuous hderiv hlip nodes hinj hmem _ hq hval hx
  rw [eval_newtonCubicPoly] at hrem
  refine hrem.trans ?_
  set t := (x - a) / h
  have hxt : x = a + t * h := by simp only [t]; field_simp; ring
  have hprod : ∏ i, (x - nodes i) = h ^ 4 * (t * (t - 1) * (t - 2) * (t - 3)) := by
    rw [Fin.prod_univ_four]
    change (x - (a + ((0 : ℕ) : ℝ) * h)) * (x - (a + ((1 : ℕ) : ℝ) * h)) *
      (x - (a + ((2 : ℕ) : ℝ) * h)) * (x - (a + ((3 : ℕ) : ℝ) * h)) = _
    simp only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
    rw [hxt]
    ring
  have ht : t ∈ Icc (0 : ℝ) 3 := by
    constructor
    · exact div_nonneg (by linarith [hx.1]) hh.le
    · rw [div_le_iff₀ hh]
      linarith [hx.2]
  have hL : 0 ≤ L := by
    have := hlip a ⟨le_rfl, by linarith⟩ (a + 3 * h) ⟨by linarith, le_rfl⟩
    have hpos : 0 < |a - (a + 3 * h)| := abs_pos.mpr (by linarith)
    nlinarith [abs_nonneg (Φ 3 a - Φ 3 (a + 3 * h))]
  rw [hprod, abs_mul, abs_of_pos (by positivity : 0 < h ^ 4)]
  have := abs_quarticNodal_le ht
  have h24 : ((3 + 1).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h24]
  calc L / 24 * (h ^ 4 * |t * (t - 1) * (t - 2) * (t - 3)|) ≤ L / 24 * (h ^ 4 * 1) := by gcongr
    _ = L * h ^ 4 / 24 := by ring

/-- **Supp II Sec 8.1.1.** The four values at `a + i h` bound `f` on `[a, a + 3h]`:
`|f| ≤ newtonCubicBound + L h⁴ / 24` for an `L`-Lipschitz third derivative. -/
theorem abs_le_newtonCubicBound {a h L : ℝ} (hh : 0 < h) (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < 3, ContinuousOn (Φ j) (Icc a (a + 3 * h)))
    (hderiv : ∀ j < 3, ∀ z ∈ Ioo a (a + 3 * h), HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc a (a + 3 * h), ∀ y ∈ Icc a (a + 3 * h), |Φ 3 x - Φ 3 y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Icc a (a + 3 * h)) :
    |Φ 0 x| ≤ newtonCubicBound (Φ 0 a) (Φ 0 (a + h)) (Φ 0 (a + 2 * h)) (Φ 0 (a + 3 * h)) +
      L * h ^ 4 / 24 := by
  have herr := abs_sub_newtonCubic_le hh Φ hcontinuous hderiv hlip hx
  have ht : (x - a) / h ∈ Icc (0 : ℝ) 3 := by
    constructor
    · exact div_nonneg (by linarith [hx.1]) hh.le
    · rw [div_le_iff₀ hh]
      linarith [hx.2]
  have hP := abs_newtonCubic_le (v₀ := Φ 0 a) (v₁ := Φ 0 (a + h)) (v₂ := Φ 0 (a + 2 * h))
    (v₃ := Φ 0 (a + 3 * h)) ht
  have := abs_sub_abs_le_abs_sub (Φ 0 x) (newtonCubic (Φ 0 a) (Φ 0 (a + h)) (Φ 0 (a + 2 * h))
    (Φ 0 (a + 3 * h)) ((x - a) / h))
  linarith

/-! ### The quadratic through three equally spaced values -/

/-- The Newton form `N₂` of the quadratic through `(i, vᵢ)`, `i = 0, 1, 2` (Supp II (8.7)). -/
noncomputable def newtonQuadratic (v₀ v₁ v₂ t : ℝ) : ℝ :=
  v₀ + t * (v₁ - v₀) + t * (t - 1) / 2 * (v₂ - 2 * v₁ + v₀)

/-- **Supp II (8.9), first half.** On `[0, 1]`, `|N₂| ≤ max(|v₀|, |v₁|) + |v₀ - 2v₁ + v₂| / 8`. -/
theorem abs_newtonQuadratic_le_left {v₀ v₁ v₂ t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |newtonQuadratic v₀ v₁ v₂ t| ≤ max |v₀| |v₁| + |v₀ - 2 * v₁ + v₂| / 8 := by
  have hid : newtonQuadratic v₀ v₁ v₂ t = (v₀ + t * (v₁ - v₀)) +
      (t - 0) * (t - 1) / 2 * (v₀ - 2 * v₁ + v₂) := by unfold newtonQuadratic; ring
  rw [hid]
  have h1 := abs_lerp_le (u := v₀) (w := v₁) ht
  have h2 := abs_sub_mul_sub_le ht
  have h3 : |(t - 0) * (t - 1) / 2 * (v₀ - 2 * v₁ + v₂)| ≤ |v₀ - 2 * v₁ + v₂| / 8 := by
    rw [abs_mul, abs_div, abs_two]
    calc |(t - 0) * (t - 1)| / 2 * |v₀ - 2 * v₁ + v₂| ≤ (1 - 0) ^ 2 / 4 / 2 *
          |v₀ - 2 * v₁ + v₂| := by gcongr
      _ = _ := by ring
  exact (abs_add_le _ _).trans (add_le_add h1 h3)

/-- **Supp II (8.9), second half.** On `[1, 2]`, `|N₂| ≤ max(|v₁|, |v₂|) + |v₀ - 2v₁ + v₂| / 8`. -/
theorem abs_newtonQuadratic_le_right {v₀ v₁ v₂ t : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) :
    |newtonQuadratic v₀ v₁ v₂ t| ≤ max |v₁| |v₂| + |v₀ - 2 * v₁ + v₂| / 8 := by
  have hid : newtonQuadratic v₀ v₁ v₂ t = (v₁ + (t - 1) * (v₂ - v₁)) +
      (t - 1) * (t - 2) / 2 * (v₀ - 2 * v₁ + v₂) := by unfold newtonQuadratic; ring
  rw [hid]
  have h1 := abs_lerp_le (u := v₁) (w := v₂) (s := t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 := abs_sub_mul_sub_le ht
  have h3 : |(t - 1) * (t - 2) / 2 * (v₀ - 2 * v₁ + v₂)| ≤ |v₀ - 2 * v₁ + v₂| / 8 := by
    rw [abs_mul, abs_div, abs_two]
    calc |(t - 1) * (t - 2)| / 2 * |v₀ - 2 * v₁ + v₂| ≤ (2 - 1) ^ 2 / 4 / 2 *
          |v₀ - 2 * v₁ + v₂| := by gcongr
      _ = _ := by ring
  exact (abs_add_le _ _).trans (add_le_add h1 h3)

/-- The quadratic `N₂` as a polynomial in the physical variable. -/
noncomputable def newtonQuadraticPoly (a h v₀ v₁ v₂ : ℝ) : ℝ[X] :=
  C v₀ + (C h⁻¹ * (X - C a)) * C (v₁ - v₀) +
    (C h⁻¹ * (X - C a)) * (C h⁻¹ * (X - C a) - 1) * C ((v₂ - 2 * v₁ + v₀) / 2)

/-- At `x` the polynomial `newtonQuadraticPoly` takes the value of `newtonQuadratic` at `t = (x - a)
/ h`. -/
theorem eval_newtonQuadraticPoly (a h v₀ v₁ v₂ x : ℝ) :
    (newtonQuadraticPoly a h v₀ v₁ v₂).eval x = newtonQuadratic v₀ v₁ v₂ ((x - a) / h) := by
  simp only [newtonQuadraticPoly, newtonQuadratic, eval_add, eval_mul, eval_C, eval_sub, eval_X,
    eval_one]
  ring

/-- **Supp II (8.8).** If the second derivative of `f = Φ 0` is `L`-Lipschitz on `[a, a + 2h]`,
then `|f - N₂| ≤ L h³ / (9 √3)` there. -/
theorem abs_sub_newtonQuadratic_le {a h L : ℝ} (hh : 0 < h) (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < 2, ContinuousOn (Φ j) (Icc a (a + 2 * h)))
    (hderiv : ∀ j < 2, ∀ z ∈ Ioo a (a + 2 * h), HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc a (a + 2 * h), ∀ y ∈ Icc a (a + 2 * h), |Φ 2 x - Φ 2 y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Icc a (a + 2 * h)) :
    |Φ 0 x - newtonQuadratic (Φ 0 a) (Φ 0 (a + h)) (Φ 0 (a + 2 * h)) ((x - a) / h)| ≤
      L * h ^ 3 / (9 * Real.sqrt 3) := by
  set nodes : Fin 3 → ℝ := fun i ↦ a + (i : ℕ) * h
  have hinj : Function.Injective nodes := equispaced_injective hh.ne' 2
  have hmem : ∀ i, nodes i ∈ Icc a (a + 2 * h) := by
    intro i
    have hi := equispaced_mem (a := a) (k := 2) hh.le i
    rwa [Nat.cast_ofNat] at hi
  have hq : (newtonQuadraticPoly a h (Φ 0 a) (Φ 0 (a + h)) (Φ 0 (a + 2 * h))).natDegree ≤ 2 := by
    unfold newtonQuadraticPoly
    compute_degree
  have hval : ∀ i, (newtonQuadraticPoly a h (Φ 0 a) (Φ 0 (a + h)) (Φ 0 (a + 2 * h))).eval
      (nodes i) = Φ 0 (nodes i) := by
    intro i
    rw [eval_newtonQuadraticPoly, show (nodes i - a) / h = ((i : ℕ) : ℝ) by
      simp only [nodes]; field_simp; ring]
    fin_cases i <;>
      simp only [nodes, newtonQuadratic, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
        zero_mul, add_zero, one_mul] <;> ring
  have hrem := abs_sub_eval_le_of_nodes Φ hcontinuous hderiv hlip nodes hinj hmem _ hq hval hx
  rw [eval_newtonQuadraticPoly] at hrem
  refine hrem.trans ?_
  set t := (x - a) / h
  have hxt : x = a + t * h := by simp only [t]; field_simp; ring
  have hprod : ∏ i, (x - nodes i) = h ^ 3 * (t * (t - 1) * (t - 2)) := by
    rw [Fin.prod_univ_three]
    change (x - (a + ((0 : ℕ) : ℝ) * h)) * (x - (a + ((1 : ℕ) : ℝ) * h)) *
      (x - (a + ((2 : ℕ) : ℝ) * h)) = _
    simp only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
    rw [hxt]
    ring
  have ht : t ∈ Icc (0 : ℝ) 2 := by
    constructor
    · exact div_nonneg (by linarith [hx.1]) hh.le
    · rw [div_le_iff₀ hh]
      linarith [hx.2]
  have hL : 0 ≤ L := by
    have := hlip a ⟨le_rfl, by linarith⟩ (a + 2 * h) ⟨by linarith, le_rfl⟩
    have hpos : 0 < |a - (a + 2 * h)| := abs_pos.mpr (by linarith)
    nlinarith [abs_nonneg (Φ 2 a - Φ 2 (a + 2 * h))]
  rw [hprod, abs_mul, abs_of_pos (by positivity : 0 < h ^ 3)]
  have := abs_cubicNodal_le ht
  have h6 : ((2 + 1).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6]
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  calc L / 6 * (h ^ 3 * |t * (t - 1) * (t - 2)|) ≤ L / 6 * (h ^ 3 * (2 / (3 * Real.sqrt 3))) := by
        gcongr
    _ = L * h ^ 3 / (9 * Real.sqrt 3) := by field_simp; ring

/-! ### The tensor form (Supp II Sec 8.1.3) -/

/-- `newtonCubicBound` is controlled by bounds of the four values and of the three differences. -/
theorem newtonCubicBound_le {v₀ v₁ v₂ v₃ a₀ a₁ a₂ a₃ d₀ d₁ d₃ : ℝ} (h₀ : |v₀| ≤ a₀)
    (h₁ : |v₁| ≤ a₁) (h₂ : |v₂| ≤ a₂) (h₃ : |v₃| ≤ a₃) (e₀ : |v₂ - 2 * v₁ + v₀| ≤ d₀)
    (e₁ : |v₃ - 2 * v₂ + v₁| ≤ d₁) (e₃ : |v₃ - 3 * v₂ + 3 * v₁ - v₀| ≤ d₃) :
    newtonCubicBound v₀ v₁ v₂ v₃ ≤
      max (max (max a₀ a₁ + d₀ / 8) (max a₁ a₂ + d₀ / 8)) (max a₂ a₃ + d₁ / 8) +
        d₃ / (9 * Real.sqrt 3) := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  unfold newtonCubicBound
  gcongr

/-- **Supp II Sec 8.1.3, the cell estimate.** On `[a, a + 3h₁] × Y`, if the third `x`-derivative
of `f(·, y)` is `Lₓ`-Lipschitz for every `y`, and at the point `y` the values `f(a + i h₁, y)` and
the differences `D₂,₀`, `D₂,₁`, `D₃` in `x` are bounded by `aᵢ`, `d₀`, `d₁`, `d₃` (for instance by
the one-variable bound `abs_le_newtonCubicBound` applied in `y`), then
`|f(x, y)| ≤ max(max(a₀, a₁) + d₀/8, max(a₁, a₂) + d₀/8, max(a₂, a₃) + d₁/8) + d₃ / (9 √3)
+ Lₓ h₁⁴ / 24`. -/
theorem abs_le_newtonCubic_tensor {a h₁ Lx y : ℝ} {a₀ a₁ a₂ a₃ d₀ d₁ d₃ : ℝ} (hh : 0 < h₁)
    (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < 3, ContinuousOn (Φ j) (Icc a (a + 3 * h₁)))
    (hderiv : ∀ j < 3, ∀ z ∈ Ioo a (a + 3 * h₁), HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc a (a + 3 * h₁), ∀ x' ∈ Icc a (a + 3 * h₁),
      |Φ 3 x - Φ 3 x'| ≤ Lx * |x - x'|)
    (f : ℝ → ℝ → ℝ) (hf : ∀ x, Φ 0 x = f x y)
    (h₀ : |f a y| ≤ a₀) (h₁' : |f (a + h₁) y| ≤ a₁) (h₂ : |f (a + 2 * h₁) y| ≤ a₂)
    (h₃ : |f (a + 3 * h₁) y| ≤ a₃)
    (e₀ : |f (a + 2 * h₁) y - 2 * f (a + h₁) y + f a y| ≤ d₀)
    (e₁ : |f (a + 3 * h₁) y - 2 * f (a + 2 * h₁) y + f (a + h₁) y| ≤ d₁)
    (e₃ : |f (a + 3 * h₁) y - 3 * f (a + 2 * h₁) y + 3 * f (a + h₁) y - f a y| ≤ d₃)
    {x : ℝ} (hx : x ∈ Icc a (a + 3 * h₁)) :
    |f x y| ≤ max (max (max a₀ a₁ + d₀ / 8) (max a₁ a₂ + d₀ / 8)) (max a₂ a₃ + d₁ / 8) +
      d₃ / (9 * Real.sqrt 3) + Lx * h₁ ^ 4 / 24 := by
  have h := abs_le_newtonCubicBound hh Φ hcontinuous hderiv hlip hx
  simp only [hf] at h
  have hb := newtonCubicBound_le h₀ h₁' h₂ h₃ e₀ e₁ e₃
  linarith

end PDE.Analysis.Approximation
