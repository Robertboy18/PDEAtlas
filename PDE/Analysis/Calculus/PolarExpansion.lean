/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PolarDerivatives
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The polar expansion of Cartesian derivatives

On an open set carrying a polar chart (`IsPolarChart`),
`∂ₓⁱ ∂_yʲ (A(r) B(β)) = ∑_{k, l} C_{i,j,k,l}(β) r^{k - i - j} A^{(k)}(r) B^{(l)}(β)` with the
coefficient tables `polarCoeff i j` of `PolarDerivatives`; this is (C.15) of Chen and Hou. The
`y`-derivatives are taken first, then the `x`-derivatives, matching the order in which the tables
are built; `A` and `B` enter through derivative chains at the points of the chart. The charts
`r = (x² + y²)^{1/2}` with `β = arctan(y/x)` on `x > 0` and `β = π/2 - arctan(x/y)` on `y > 0`
cover the closed quadrant without the origin. A Cartesian cell `[x_l, x_u] × [y_l, y_u]` with
`x_l > 0`, `y_l ≥ 0` lies in the polar cell `r ∈ [(x_l² + y_l²)^{1/2}, (x_u² + y_u²)^{1/2}]`,
`β ∈ [arctan(y_l / x_u), arctan(y_u / x_l)]` (App C.3.3), which is how bounds on polar cells
transfer to it.

## Main results

* `derivX_eq_polarExpansion`: the `x`-derivative of an expansion of order `n` is the expansion of
  order `n + 1` with the stepped table (C.17).
* `derivY_eq_polarExpansion`: the same for the `y`-derivative and (C.18).
* `derivX_iterate_derivY_iterate_eq`: the expansion (C.15) of `∂ₓⁱ ∂_yʲ (A₀(r) B₀(β))` on a polar
  chart.
* `isPolarChart_right`: `r = (x² + y²)^{1/2}`, `β = arctan(y / x)` is a polar chart on `x > 0`.
* `isPolarChart_upper`: `r = (x² + y²)^{1/2}`, `β = π/2 - arctan(x / y)` is a polar chart on
  `y > 0`.
* `mem_polarCell_of_mem_rect`: a Cartesian cell lies in the polar cell above.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix C.3.1,
  (C.15)-(C.18), and Appendix C.3.3. <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis

open Finset Real Filter Topology

/-- The derivative of the expansion along a curve `t ↦ (r t, θ t)`, for a table supported in
`k + l ≤ n`; only the factors `A k`, `B l` with `k, l ≤ n` are differentiated. -/
theorem hasDerivAt_polarExpansion_comp {N n : ℕ} {C : ℕ → ℕ → List TrigTerm}
    (hC : ∀ k l, n < k + l → C k l = [])
    {A B : ℕ → ℝ → ℝ} {r θ : ℝ → ℝ} {x r' θ' : ℝ} (hr : HasDerivAt r r' x)
    (hθ : HasDerivAt θ θ' x) (hpos : 0 < r x)
    (hA : ∀ k ≤ n, HasDerivAt (A k) (A (k + 1) (r x)) (r x))
    (hB : ∀ l ≤ n, HasDerivAt (B l) (B (l + 1) (θ x)) (θ x)) :
    HasDerivAt (fun t ↦ polarExpansion N n C A B (r t) (θ t))
      (∑ k ∈ range N, ∑ l ∈ range N,
        (trigTermsEval (trigTermsDeriv (C k l)) (θ x) * θ' * r x ^ ((k : ℤ) - n) * A k (r x) *
            B l (θ x) +
          trigTermsEval (C k l) (θ x) * (((k : ℤ) - n : ℤ) * r x ^ ((k : ℤ) - n - 1) * r') *
            A k (r x) * B l (θ x) +
          trigTermsEval (C k l) (θ x) * r x ^ ((k : ℤ) - n) * (A (k + 1) (r x) * r') *
            B l (θ x) +
          trigTermsEval (C k l) (θ x) * r x ^ ((k : ℤ) - n) * A k (r x) *
            (B (l + 1) (θ x) * θ'))) x := by
  unfold polarExpansion
  refine HasDerivAt.fun_sum fun k _ ↦ HasDerivAt.fun_sum fun l _ ↦ ?_
  by_cases hkl : n < k + l
  · -- a vanishing coefficient: the term is identically zero
    have h0 := hC k l hkl
    simp only [h0, trigTermsDeriv, List.map_nil, trigTermsEval_nil, zero_mul, add_zero]
    exact hasDerivAt_const x 0
  have hc : HasDerivAt (trigTermsEval (C k l) ∘ θ)
      (trigTermsEval (trigTermsDeriv (C k l)) (θ x) * θ') x :=
    (hasDerivAt_trigTermsEval (C k l) (θ x)).comp x hθ
  have hz := (hasDerivAt_zpow ((k : ℤ) - n) (r x) (Or.inl hpos.ne')).comp x hr
  have ha := (hA k (by omega)).comp x hr
  have hb := (hB l (by omega)).comp x hθ
  have h := ((hc.fun_mul hz).fun_mul ha).fun_mul hb
  simp only [Function.comp_apply] at h
  convert h using 1
  ring

/-- Near a point of an open set, the horizontal line stays in the set. -/
theorem eventually_mem_horizontal {U : Set (ℝ × ℝ)} (hU : IsOpen U) {p : ℝ × ℝ} (hp : p ∈ U) :
    ∀ᶠ t in 𝓝 p.1, (t, p.2) ∈ U :=
  (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hU.mem_nhds hp)

/-- Near a point of an open set, the vertical line stays in the set. -/
theorem eventually_mem_vertical {U : Set (ℝ × ℝ)} (hU : IsOpen U) {p : ℝ × ℝ} (hp : p ∈ U) :
    ∀ᶠ t in 𝓝 p.2, (p.1, t) ∈ U :=
  (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hp)

/-- **The `x`-step of (C.15).** If `H` equals the expansion of order `n` with a table supported in
`k + l ≤ n` on the chart, then `∂ₓ H` equals the expansion of order `n + 1` with the table
`polarStepX n C`, i.e. (C.16) with (C.17). -/
theorem derivX_eq_polarExpansion {U : Set (ℝ × ℝ)} {ρ θ : ℝ → ℝ → ℝ}
    (hU : IsPolarChart U ρ θ) {A B : ℕ → ℝ → ℝ} {N n : ℕ}
    (hA : ∀ k ≤ n, ∀ p ∈ U, HasDerivAt (A k) (A (k + 1) (ρ p.1 p.2)) (ρ p.1 p.2))
    (hB : ∀ l ≤ n, ∀ p ∈ U, HasDerivAt (B l) (B (l + 1) (θ p.1 p.2)) (θ p.1 p.2))
    (hN : n + 2 ≤ N) {C : ℕ → ℕ → List TrigTerm}
    (hC : ∀ k l, n < k + l → C k l = []) {H : ℝ → ℝ → ℝ}
    (hH : ∀ p ∈ U, H p.1 p.2 = polarExpansion N n C A B (ρ p.1 p.2) (θ p.1 p.2)) :
    ∀ p ∈ U, derivX H p.1 p.2 =
      polarExpansion N (n + 1) (polarStepX n C) A B (ρ p.1 p.2) (θ p.1 p.2) := by
  intro p hp
  have hev : (fun t ↦ H t p.2) =ᶠ[𝓝 p.1]
      fun t ↦ polarExpansion N n C A B (ρ t p.2) (θ t p.2) := by
    filter_upwards [eventually_mem_horizontal hU.isOpen hp] with t ht using hH (t, p.2) ht
  have hd := hasDerivAt_polarExpansion_comp (N := N) (n := n) (C := C) (A := A) (B := B) hC
    (r := fun t ↦ ρ t p.2) (θ := fun t ↦ θ t p.2) (hU.hasDerivAt_ρ_x p hp)
    (hU.hasDerivAt_θ_x p hp) (hU.pos p hp) (fun k hk ↦ hA k hk p hp) (fun l hl ↦ hB l hl p hp)
  simp only [derivX]
  rw [hev.deriv_eq, hd.deriv]
  unfold polarExpansion
  simp only [trigTermsEval_polarStepX]
  exact polar_step_sum N n hN (fun k l ↦ trigTermsEval (C k l) (θ p.1 p.2))
    (fun k l ↦ trigTermsEval (trigTermsDeriv (C k l)) (θ p.1 p.2))
    (fun k l h ↦ by simp [hC k l h]) (hU.pos p hp).ne' _ _ _ _

/-- **The `y`-step of (C.15).** As `derivX_eq_polarExpansion`, with (C.18). -/
theorem derivY_eq_polarExpansion {U : Set (ℝ × ℝ)} {ρ θ : ℝ → ℝ → ℝ}
    (hU : IsPolarChart U ρ θ) {A B : ℕ → ℝ → ℝ} {N n : ℕ}
    (hA : ∀ k ≤ n, ∀ p ∈ U, HasDerivAt (A k) (A (k + 1) (ρ p.1 p.2)) (ρ p.1 p.2))
    (hB : ∀ l ≤ n, ∀ p ∈ U, HasDerivAt (B l) (B (l + 1) (θ p.1 p.2)) (θ p.1 p.2))
    (hN : n + 2 ≤ N) {C : ℕ → ℕ → List TrigTerm}
    (hC : ∀ k l, n < k + l → C k l = []) {H : ℝ → ℝ → ℝ}
    (hH : ∀ p ∈ U, H p.1 p.2 = polarExpansion N n C A B (ρ p.1 p.2) (θ p.1 p.2)) :
    ∀ p ∈ U, derivY H p.1 p.2 =
      polarExpansion N (n + 1) (polarStepY n C) A B (ρ p.1 p.2) (θ p.1 p.2) := by
  intro p hp
  have hev : H p.1 =ᶠ[𝓝 p.2] fun t ↦ polarExpansion N n C A B (ρ p.1 t) (θ p.1 t) := by
    filter_upwards [eventually_mem_vertical hU.isOpen hp] with t ht using hH (p.1, t) ht
  have hd := hasDerivAt_polarExpansion_comp (N := N) (n := n) (C := C) (A := A) (B := B) hC
    (r := ρ p.1) (θ := θ p.1) (hU.hasDerivAt_ρ_y p hp)
    (hU.hasDerivAt_θ_y p hp) (hU.pos p hp) (fun k hk ↦ hA k hk p hp) (fun l hl ↦ hB l hl p hp)
  simp only [derivY]
  rw [hev.deriv_eq, hd.deriv]
  unfold polarExpansion
  simp only [trigTermsEval_polarStepY]
  exact polar_step_sum N n hN (fun k l ↦ trigTermsEval (C k l) (θ p.1 p.2))
    (fun k l ↦ trigTermsEval (trigTermsDeriv (C k l)) (θ p.1 p.2))
    (fun k l h ↦ by simp [hC k l h]) (hU.pos p hp).ne' _ _ _ _

/-- The function itself is the expansion of order `0` with the base table. -/
theorem polarExpansion_base {N : ℕ} (hN : 0 < N) (A B : ℕ → ℝ → ℝ) (r θ : ℝ) :
    polarExpansion N 0 polarBase A B r θ = A 0 r * B 0 θ := by
  unfold polarExpansion
  rw [sum_eq_single 0, sum_eq_single 0]
  · simp [polarBase, trigTermsEval, TrigTerm.eval]
  · intro l _ hl
    simp [polarBase, hl]
  · intro h
    exact absurd (mem_range.mpr hN) h
  · intro k _ hk
    exact sum_eq_zero fun l _ ↦ by simp [polarBase, hk]
  · intro h
    exact absurd (mem_range.mpr hN) h

/-- **Part II (C.15).** On a polar chart, for derivative chains `A k` (radial) and `B l`
(angular) of order `i + j` and any box size `N > i + j`,
`∂ₓⁱ ∂_yʲ (A₀(r) B₀(β)) = ∑_{k, l < N} C_{i,j,k,l}(β) r^{k - i - j} A_k(r) B_l(β)`
with `C = polarCoeff i j`; the terms with `k + l > i + j` vanish. -/
theorem derivX_iterate_derivY_iterate_eq {U : Set (ℝ × ℝ)} {ρ θ : ℝ → ℝ → ℝ}
    (hU : IsPolarChart U ρ θ) {A B : ℕ → ℝ → ℝ} (i j N : ℕ) (hN : i + j < N)
    (hA : ∀ k < i + j, ∀ p ∈ U, HasDerivAt (A k) (A (k + 1) (ρ p.1 p.2)) (ρ p.1 p.2))
    (hB : ∀ l < i + j, ∀ p ∈ U, HasDerivAt (B l) (B (l + 1) (θ p.1 p.2)) (θ p.1 p.2)) :
    ∀ p ∈ U, (derivX^[i] (derivY^[j] fun x y ↦ A 0 (ρ x y) * B 0 (θ x y))) p.1 p.2 =
      polarExpansion N (i + j) (polarCoeff i j) A B (ρ p.1 p.2) (θ p.1 p.2) := by
  induction i with
  | zero =>
    induction j with
    | zero =>
      intro p _
      simp only [Function.iterate_zero, id_eq, polarCoeff_zero, polarCoeffY]
      exact (polarExpansion_base (by omega) A B _ _).symm
    | succ j ih =>
      intro p hp
      simp only [Function.iterate_zero, id_eq, polarCoeff_zero, polarCoeffY,
        Function.iterate_succ_apply', zero_add] at ih ⊢ hA hB
      exact derivY_eq_polarExpansion hU (fun k hk ↦ hA k (by omega)) (fun l hl ↦ hB l (by omega))
        (by omega) (fun k l h ↦ by simpa using polarCoeff_eq_nil 0 j k l (by omega))
        (ih (by omega) (fun k hk ↦ hA k (by omega)) (fun l hl ↦ hB l (by omega))) p hp
  | succ i ih =>
    intro p hp
    rw [Function.iterate_succ_apply', polarCoeff_succ, show i + 1 + j = i + j + 1 by ring]
    exact derivX_eq_polarExpansion hU (fun k hk ↦ hA k (by omega)) (fun l hl ↦ hB l (by omega))
      (by omega) (polarCoeff_eq_nil i j)
      (ih (by omega) (fun k hk ↦ hA k (by omega)) (fun l hl ↦ hB l (by omega))) p hp

/-! ### Two polar charts -/

/-- `cos (arctan t) = 1 / (1 + t²)^{1/2}` and `sin (arctan t) = t / (1 + t²)^{1/2}` in the form
`x / r`, `y / r` for `t = y / x`, `x > 0`. -/
theorem sqrt_one_add_div_sq {x y : ℝ} (hx : 0 < x) :
    Real.sqrt (1 + (y / x) ^ 2) = Real.sqrt (x ^ 2 + y ^ 2) / x := by
  have hρ : 0 < Real.sqrt (x ^ 2 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [show 1 + (y / x) ^ 2 = (Real.sqrt (x ^ 2 + y ^ 2) / x) ^ 2 by
    rw [div_pow, div_pow, Real.sq_sqrt (by positivity)]
    field_simp]
  exact Real.sqrt_sq (by positivity)

/-- For `x > 0`, `cos (arctan (y / x)) = x / √(x² + y²)`. -/
theorem cos_arctan_div {x y : ℝ} (hx : 0 < x) :
    Real.cos (Real.arctan (y / x)) = x / Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [Real.cos_arctan, sqrt_one_add_div_sq hx]
  have hρ : 0 < Real.sqrt (x ^ 2 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- For `x > 0`, `sin (arctan (y / x)) = y / √(x² + y²)`. -/
theorem sin_arctan_div {x y : ℝ} (hx : 0 < x) :
    Real.sin (Real.arctan (y / x)) = y / Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [Real.sin_arctan, sqrt_one_add_div_sq hx]
  have hρ : 0 < Real.sqrt (x ^ 2 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- Where `x² + y² ≠ 0`, the derivative of `t ↦ √(t² + y²)` at `x` is `x / √(x² + y²)`. -/
theorem hasDerivAt_sqrt_sq_add_sq_left (x y : ℝ) (h : x ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun t ↦ Real.sqrt (t ^ 2 + y ^ 2)) (x / Real.sqrt (x ^ 2 + y ^ 2)) x := by
  have h1 : HasDerivAt (fun t ↦ t ^ 2 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (y ^ 2)
  convert h1.sqrt h using 1
  field_simp

/-- Where `x² + y² ≠ 0`, the derivative of `t ↦ √(x² + t²)` at `y` is `y / √(x² + y²)`. -/
theorem hasDerivAt_sqrt_sq_add_sq_right (x y : ℝ) (h : x ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun t ↦ Real.sqrt (x ^ 2 + t ^ 2)) (y / Real.sqrt (x ^ 2 + y ^ 2)) y := by
  have h1 : HasDerivAt (fun t ↦ x ^ 2 + t ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (x ^ 2)
  convert h1.sqrt h using 1
  field_simp

/-- **The right half-plane chart** `r = (x² + y²)^{1/2}`, `β = arctan(y / x)` on `x > 0`. -/
theorem isPolarChart_right :
    IsPolarChart {p : ℝ × ℝ | 0 < p.1} (fun x y ↦ Real.sqrt (x ^ 2 + y ^ 2))
      (fun x y ↦ Real.arctan (y / x)) := by
  refine ⟨isOpen_lt continuous_const continuous_fst, fun p hp ↦ ?_, fun p hp ↦ ?_,
    fun p hp ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · exact Real.sqrt_pos.mpr (by have : 0 < p.1 := hp; positivity)
  · have hx : 0 < p.1 := hp
    rw [cos_arctan_div hx]
    exact hasDerivAt_sqrt_sq_add_sq_left _ _ (by positivity)
  · have hx : 0 < p.1 := hp
    rw [sin_arctan_div hx]
    exact hasDerivAt_sqrt_sq_add_sq_right _ _ (by positivity)
  · have hx : 0 < p.1 := hp
    simp only [sin_arctan_div hx]
    have h1 : HasDerivAt (fun t ↦ p.2 / t) (-p.2 / p.1 ^ 2) p.1 := by
      have := (hasDerivAt_inv hx.ne').const_mul p.2
      convert this using 1
      · funext t
        ring
      · ring
    convert h1.arctan using 1
    have hρ := Real.sq_sqrt (show 0 ≤ p.1 ^ 2 + p.2 ^ 2 by positivity)
    have hρ0 : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := Real.sqrt_pos.mpr (by positivity)
    field_simp
    rw [hρ]
  · have hx : 0 < p.1 := hp
    simp only [cos_arctan_div hx]
    have h1 : HasDerivAt (fun t ↦ t / p.1) (1 / p.1) p.2 := by
      simpa using (hasDerivAt_id p.2).div_const p.1
    convert h1.arctan using 1
    have hρ := Real.sq_sqrt (show 0 ≤ p.1 ^ 2 + p.2 ^ 2 by positivity)
    have hρ0 : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := Real.sqrt_pos.mpr (by positivity)
    field_simp
    rw [hρ]

/-- **The upper half-plane chart** `r = (x² + y²)^{1/2}`, `β = π/2 - arctan(x / y)` on `y > 0`;
it contains the axis `β = π/2`. -/
theorem isPolarChart_upper :
    IsPolarChart {p : ℝ × ℝ | 0 < p.2} (fun x y ↦ Real.sqrt (x ^ 2 + y ^ 2))
      (fun x y ↦ π / 2 - Real.arctan (x / y)) := by
  have hcos {x y : ℝ} (hy : 0 < y) :
      Real.cos (π / 2 - Real.arctan (x / y)) = x / Real.sqrt (x ^ 2 + y ^ 2) := by
    rw [Real.cos_pi_div_two_sub, sin_arctan_div hy, add_comm]
  have hsin {x y : ℝ} (hy : 0 < y) :
      Real.sin (π / 2 - Real.arctan (x / y)) = y / Real.sqrt (x ^ 2 + y ^ 2) := by
    rw [Real.sin_pi_div_two_sub, cos_arctan_div hy, add_comm]
  refine ⟨isOpen_lt continuous_const continuous_snd, fun p hp ↦ ?_, fun p hp ↦ ?_,
    fun p hp ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · exact Real.sqrt_pos.mpr (by have : 0 < p.2 := hp; positivity)
  · have hy : 0 < p.2 := hp
    rw [hcos hy]
    exact hasDerivAt_sqrt_sq_add_sq_left _ _ (by positivity)
  · have hy : 0 < p.2 := hp
    rw [hsin hy]
    exact hasDerivAt_sqrt_sq_add_sq_right _ _ (by positivity)
  · have hy : 0 < p.2 := hp
    simp only [hsin hy]
    have h1 : HasDerivAt (fun t ↦ t / p.2) (1 / p.2) p.1 := by
      simpa using (hasDerivAt_id p.1).div_const p.2
    convert (h1.arctan).const_sub (π / 2) using 1
    have hρ := Real.sq_sqrt (show 0 ≤ p.1 ^ 2 + p.2 ^ 2 by positivity)
    have hρ0 : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := Real.sqrt_pos.mpr (by positivity)
    field_simp
    rw [hρ]
    ring
  · have hy : 0 < p.2 := hp
    simp only [hcos hy]
    have h1 : HasDerivAt (fun t ↦ p.1 / t) (-p.1 / p.2 ^ 2) p.2 := by
      have := (hasDerivAt_inv hy.ne').const_mul p.1
      convert this using 1
      · funext t
        ring
      · ring
    convert (h1.arctan).const_sub (π / 2) using 1
    have hρ := Real.sq_sqrt (show 0 ≤ p.1 ^ 2 + p.2 ^ 2 by positivity)
    have hρ0 : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := Real.sqrt_pos.mpr (by positivity)
    field_simp
    rw [hρ]
    ring

/-- **Part II, App C.3.3.** A point of `[x_l, x_u] × [y_l, y_u]`, `0 < x_l`, `0 ≤ y_l`, has radius
in `[(x_l² + y_l²)^{1/2}, (x_u² + y_u²)^{1/2}]` and angle `arctan(y / x)` in
`[arctan(y_l / x_u), arctan(y_u / x_l)]`. -/
theorem mem_polarCell_of_mem_rect {xl xu yl yu x y : ℝ} (hxl : 0 < xl) (hyl : 0 ≤ yl)
    (hx : x ∈ Set.Icc xl xu) (hy : y ∈ Set.Icc yl yu) :
    Real.sqrt (x ^ 2 + y ^ 2) ∈
        Set.Icc (Real.sqrt (xl ^ 2 + yl ^ 2)) (Real.sqrt (xu ^ 2 + yu ^ 2)) ∧
      Real.arctan (y / x) ∈ Set.Icc (Real.arctan (yl / xu)) (Real.arctan (yu / xl)) := by
  have hx0 : 0 < x := hxl.trans_le hx.1
  have hy0 : 0 ≤ y := hyl.trans hy.1
  refine ⟨⟨Real.sqrt_le_sqrt ?_, Real.sqrt_le_sqrt ?_⟩,
    ⟨Real.arctan_mono ?_, Real.arctan_mono ?_⟩⟩
  · nlinarith [hx.1, hy.1]
  · nlinarith [hx.2, hy.2]
  · exact div_le_div₀ hy0 hy.1 hx0 hx.2
  · exact div_le_div₀ (hy0.trans hy.2) hy.2 hxl hx.1

end PDE.Analysis
