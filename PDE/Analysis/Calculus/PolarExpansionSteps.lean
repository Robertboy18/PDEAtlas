/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PolarExpansion
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Derivatives of polar expansions along the coordinate lines

On a polar chart (`IsPolarChart`) the polar expansion of order `n` of a table `C`,
`E_C(x, y) = ∑_{k, l} C_{k,l}(β) r^{k - n} A_k(r) B_l(β)`, has along horizontal lines the
derivative `E_{polarStepX n C}` and along vertical lines the derivative `E_{polarStepY n C}`,
both of order `n + 1`. These are (C.16)-(C.18) of Chen and Hou, stated as derivatives along the
coordinate lines. A chain of these steps gives the derivative relations that the
second-order cell estimate (C.13) asks of a function and its derivatives in each direction, with
any tables, and without comparing the tables of different orders of differentiation. The
iterates of `derivX` and `derivY` are iterated one-variable derivatives, and they depend only on
the values on an open set.

On `x > 0` and on `y > 0` the angle of Mathlib's `polarCoord` is the angle of the two charts of
`PolarExpansion`. A function that is `Cⁿ` on an open set has its iterated derivatives as a
derivative chain there.

## Main results

* `hasDerivAt_polarExpansion_x`: the horizontal derivative of `E_C` is `E_{polarStepX n C}`.
* `hasDerivAt_polarExpansion_y`: the vertical derivative of `E_C` is `E_{polarStepY n C}`.
* `derivX_iterate_derivY_iterate_congr`: the iterated derivatives depend only on the values on an
  open set.
* `polarCoord_snd_of_pos_left`: on `x > 0` the angle of `polarCoord` is `arctan (y / x)`.
* `polarCoord_snd_of_pos_right`: on `y > 0` the angle of `polarCoord` is `π/2 - arctan (x / y)`.
* `hasDerivAt_iteratedDeriv_of_contDiffOn`: on an open set where `f` is `Cⁿ`, `f⁽ᵏ⁾` has the
  derivative `f⁽ᵏ⁺¹⁾` for `k < n`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix C.3.1,
  (C.16)-(C.18), and Appendix C.2, (C.13). <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis

open Finset Real Filter Topology

/-- **The `x`-step as a derivative.** -/
theorem hasDerivAt_polarExpansion_x {U : Set (ℝ × ℝ)} {ρ θ : ℝ → ℝ → ℝ}
    (hU : IsPolarChart U ρ θ) {A B : ℕ → ℝ → ℝ} {N n : ℕ}
    (hA : ∀ k ≤ n, ∀ p ∈ U, HasDerivAt (A k) (A (k + 1) (ρ p.1 p.2)) (ρ p.1 p.2))
    (hB : ∀ l ≤ n, ∀ p ∈ U, HasDerivAt (B l) (B (l + 1) (θ p.1 p.2)) (θ p.1 p.2))
    (hN : n + 2 ≤ N) {C : ℕ → ℕ → List TrigTerm} (hC : ∀ k l, n < k + l → C k l = [])
    {p : ℝ × ℝ} (hp : p ∈ U) :
    HasDerivAt (fun t ↦ polarExpansion N n C A B (ρ t p.2) (θ t p.2))
      (polarExpansion N (n + 1) (polarStepX n C) A B (ρ p.1 p.2) (θ p.1 p.2)) p.1 := by
  have hd := hasDerivAt_polarExpansion_comp (N := N) (n := n) (C := C) (A := A) (B := B) hC
    (r := fun t ↦ ρ t p.2) (θ := fun t ↦ θ t p.2) (hU.hasDerivAt_ρ_x p hp)
    (hU.hasDerivAt_θ_x p hp) (hU.pos p hp) (fun k hk ↦ hA k hk p hp) (fun l hl ↦ hB l hl p hp)
  convert hd using 1
  unfold polarExpansion
  simp only [trigTermsEval_polarStepX]
  exact (polar_step_sum N n hN (fun k l ↦ trigTermsEval (C k l) (θ p.1 p.2))
    (fun k l ↦ trigTermsEval (trigTermsDeriv (C k l)) (θ p.1 p.2))
    (fun k l h ↦ by simp [hC k l h]) (hU.pos p hp).ne' _ _ _ _).symm

/-- **The `y`-step as a derivative.** -/
theorem hasDerivAt_polarExpansion_y {U : Set (ℝ × ℝ)} {ρ θ : ℝ → ℝ → ℝ}
    (hU : IsPolarChart U ρ θ) {A B : ℕ → ℝ → ℝ} {N n : ℕ}
    (hA : ∀ k ≤ n, ∀ p ∈ U, HasDerivAt (A k) (A (k + 1) (ρ p.1 p.2)) (ρ p.1 p.2))
    (hB : ∀ l ≤ n, ∀ p ∈ U, HasDerivAt (B l) (B (l + 1) (θ p.1 p.2)) (θ p.1 p.2))
    (hN : n + 2 ≤ N) {C : ℕ → ℕ → List TrigTerm} (hC : ∀ k l, n < k + l → C k l = [])
    {p : ℝ × ℝ} (hp : p ∈ U) :
    HasDerivAt (fun t ↦ polarExpansion N n C A B (ρ p.1 t) (θ p.1 t))
      (polarExpansion N (n + 1) (polarStepY n C) A B (ρ p.1 p.2) (θ p.1 p.2)) p.2 := by
  have hd := hasDerivAt_polarExpansion_comp (N := N) (n := n) (C := C) (A := A) (B := B) hC
    (r := ρ p.1) (θ := θ p.1) (hU.hasDerivAt_ρ_y p hp)
    (hU.hasDerivAt_θ_y p hp) (hU.pos p hp) (fun k hk ↦ hA k hk p hp) (fun l hl ↦ hB l hl p hp)
  convert hd using 1
  unfold polarExpansion
  simp only [trigTermsEval_polarStepY]
  exact (polar_step_sum N n hN (fun k l ↦ trigTermsEval (C k l) (θ p.1 p.2))
    (fun k l ↦ trigTermsEval (trigTermsDeriv (C k l)) (θ p.1 p.2))
    (fun k l h ↦ by simp [hC k l h]) (hU.pos p hp).ne' _ _ _ _).symm

/-- A polar chart restricts to open subsets. -/
theorem IsPolarChart.mono {U V : Set (ℝ × ℝ)} {ρ θ : ℝ → ℝ → ℝ} (h : IsPolarChart U ρ θ)
    (hV : IsOpen V) (hVU : V ⊆ U) : IsPolarChart V ρ θ :=
  ⟨hV, fun p hp ↦ h.pos p (hVU hp), fun p hp ↦ h.hasDerivAt_ρ_x p (hVU hp),
    fun p hp ↦ h.hasDerivAt_ρ_y p (hVU hp), fun p hp ↦ h.hasDerivAt_θ_x p (hVU hp),
    fun p hp ↦ h.hasDerivAt_θ_y p (hVU hp)⟩

/-! ### Values on open sets -/

/-- Functions that agree on an open set `U` have the same `y`-derivative at the points of `U`. -/
theorem derivY_congr {U : Set (ℝ × ℝ)} (hU : IsOpen U) {F G : ℝ → ℝ → ℝ}
    (h : ∀ p ∈ U, F p.1 p.2 = G p.1 p.2) : ∀ p ∈ U, derivY F p.1 p.2 = derivY G p.1 p.2 := by
  intro p hp
  unfold derivY
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_mem_vertical hU hp] with t ht
  exact h (p.1, t) ht

/-- Functions that agree on an open set `U` have the same `x`-derivative at the points of `U`. -/
theorem derivX_congr {U : Set (ℝ × ℝ)} (hU : IsOpen U) {F G : ℝ → ℝ → ℝ}
    (h : ∀ p ∈ U, F p.1 p.2 = G p.1 p.2) : ∀ p ∈ U, derivX F p.1 p.2 = derivX G p.1 p.2 := by
  intro p hp
  unfold derivX
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_mem_horizontal hU hp] with t ht
  exact h (t, p.2) ht

/-- The iterated derivatives depend only on the values on an open set. -/
theorem derivX_iterate_derivY_iterate_congr {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F G : ℝ → ℝ → ℝ} (h : ∀ p ∈ U, F p.1 p.2 = G p.1 p.2) (i j : ℕ) :
    ∀ p ∈ U, (derivX^[i] (derivY^[j] F)) p.1 p.2 = (derivX^[i] (derivY^[j] G)) p.1 p.2 := by
  induction i with
  | zero =>
    induction j with
    | zero => simpa using h
    | succ j ih =>
      simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply'] at ih ⊢
      exact derivY_congr hU ih
  | succ i ih =>
    simp only [Function.iterate_succ_apply']
    exact derivX_congr hU ih

/-! ### Mathlib's polar angle on the two charts -/

/-- The complex number `x + i y` has modulus `√(x² + y²)`. -/
theorem norm_equivRealProd_symm (x y : ℝ) :
    ‖Complex.equivRealProd.symm (x, y)‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp [pow_two]

/-- On `x > 0` the angle of `polarCoord` is `arctan (y / x)`. -/
theorem polarCoord_snd_of_pos_left {x y : ℝ} (hx : 0 < x) :
    (polarCoord (x, y)).2 = Real.arctan (y / x) := by
  set z := Complex.equivRealProd.symm (x, y)
  have hz : z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [z] at this
    linarith
  have hre : z.re = x := by simp [z]
  have him : z.im = y := by simp [z]
  change Complex.arg z = _
  have hlt : |Complex.arg z| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; exact hx))
  have h1 : Complex.arg z ∈ Set.Icc (-(π / 2)) (π / 2) :=
    ⟨by linarith [neg_abs_le (Complex.arg z)], by linarith [le_abs_self (Complex.arg z)]⟩
  have h2 : Real.arctan (y / x) ∈ Set.Icc (-(π / 2)) (π / 2) :=
    ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  refine Real.injOn_sin h1 h2 ?_
  rw [Complex.sin_arg, sin_arctan_div hx, him, norm_equivRealProd_symm]

/-- On `y > 0` the angle of `polarCoord` is `π/2 - arctan (x / y)`. -/
theorem polarCoord_snd_of_pos_right {x y : ℝ} (hy : 0 < y) :
    (polarCoord (x, y)).2 = π / 2 - Real.arctan (x / y) := by
  set z := Complex.equivRealProd.symm (x, y)
  have hz : z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [z] at this
    linarith
  have hre : z.re = x := by simp [z]
  have him : z.im = y := by simp [z]
  change Complex.arg z = _
  have h1 : Complex.arg z ∈ Set.Icc 0 π :=
    ⟨Complex.arg_nonneg_iff.mpr (by rw [him]; exact hy.le), Complex.arg_le_pi z⟩
  have h2 : π / 2 - Real.arctan (x / y) ∈ Set.Icc 0 π :=
    ⟨by linarith [Real.arctan_lt_pi_div_two (x / y)],
      by linarith [Real.neg_pi_div_two_lt_arctan (x / y)]⟩
  refine Real.injOn_cos h1 h2 ?_
  rw [Complex.cos_arg hz, Real.cos_pi_div_two_sub, sin_arctan_div hy, hre,
    norm_equivRealProd_symm, add_comm]

/-! ### Derivative chains -/

/-- On an open set where `f` is `Cⁿ`, `f⁽ᵏ⁾` has the derivative `f⁽ᵏ⁺¹⁾` for `k < n`. -/
theorem hasDerivAt_iteratedDeriv_of_contDiffOn {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) {n : ℕ}
    (hf : ContDiffOn ℝ n f s) {k : ℕ} (hk : k < n) {x : ℝ} (hx : x ∈ s) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
  have hd : DifferentiableOn ℝ (iteratedDerivWithin k f s) s :=
    hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) hs.uniqueDiffOn
  have heq : Set.EqOn (iteratedDerivWithin k f s) (iteratedDeriv k f) s :=
    iteratedDerivWithin_of_isOpen hs
  have hdx : DifferentiableAt ℝ (iteratedDeriv k f) x :=
    ((hd x hx).differentiableAt (hs.mem_nhds hx)).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hs.mem_nhds hx) fun y hy ↦ (heq hy).symm)
  rw [iteratedDeriv_succ]
  exact hdx.hasDerivAt

end PDE.Analysis
