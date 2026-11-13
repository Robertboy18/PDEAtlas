/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Continuum.Quadrature.Gaussian.Rolle
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Polynomial interpolation remainders with a Lipschitz top derivative

Let `Φ` be a derivative chain of order `n` on `[a, b]`: `Φ k` is continuous on `[a, b]` and has
derivative `Φ (k + 1)` on `(a, b)` for `k < n`. If `Φ 0` has `n + 2` zeros counted with
multiplicity and they are not all equal, then `Φ n` has two distinct zeros
(`exists_two_derivative_chain_zeros`). Rolle's theorem places a zero of `Φ 1` strictly between two
distinct consecutive zeros and reuses a repeated zero, so every run of equal zeros shortens by one
at each step, and the two zeros left after `n` steps coincide only if all `n + 2` zeros did.

With this, a polynomial `p` of degree at most `n` that agrees with `Φ 0` on a multiset `s` of
`n + 1` points (with multiplicity) has the remainder bound
`|Φ 0 x - p x| ≤ L / (n + 1)! |∏_{z ∈ s} (x - z)|` whenever `Φ n` is `L`-Lipschitz on `[a, b]`
(`abs_sub_eval_le_of_lipschitz`). The hypothesis is a Lipschitz `n`-th derivative, as for the
`C^{4,1}` functions to which Chen and Hou, Part II, Supplementary Sec 8.3.1, apply the fifth-order
Hermite interpolant. For a bounded `(n + 1)`-st derivative the Lipschitz
constant is that bound (`lipschitz_of_abs_deriv_le`). The Lagrange case is
`abs_sub_interpolate_le` (Supp II (8.12) in one variable).

## Main results

* `exists_two_derivative_chain_zeros_of_multiset`: `n + 2` zeros of `Φ 0` in `[a, b]` counted
  with multiplicity, not all equal, give two distinct zeros of `Φ n`.
* `lipschitz_of_abs_deriv_le`: a step of a derivative chain with a bounded derivative is
  Lipschitz on the closed interval.
* `abs_sub_eval_le_of_lipschitz`: `|Φ 0 x - p x| ≤ L / (n + 1)! |∏_{z ∈ s} (x - z)|` for `p` of
  degree at most `n` agreeing with the chain on `s`.
* `abs_sub_eval_le_of_nodes`: the same remainder at `k + 1` distinct nodes, for any polynomial of
  degree at most `k` taking the values of `Φ 0` there.
* `abs_sub_interpolate_le`: the Lagrange remainder, Supp II (8.12) in one variable.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II (in the same PDF), Section 8.2, (8.12), and Section 8.3.1.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis.Approximation

open Set Polynomial

/-- **Two distinct zeros after `n` derivatives.** If `Φ 0` vanishes at the monotone list
`x 0 ≤ ⋯ ≤ x (n + 1)` in `[a, b]` with multiplicity (a run of equal entries from `i` to `j` is a
zero of `Φ (j - i)`), and `x 0 < x (n + 1)`, then `Φ n` has two distinct zeros in `[a, b]`. -/
theorem exists_two_derivative_chain_zeros {a b : ℝ} (n : ℕ) (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ k < n, ContinuousOn (Φ k) (Icc a b))
    (hderiv : ∀ k < n, ∀ z ∈ Ioo a b, HasDerivAt (Φ k) (Φ (k + 1) z) z)
    (x : Fin (n + 2) → ℝ) (hmonotone : Monotone x) (hmem : ∀ i, x i ∈ Icc a b)
    (hzero : ∀ i j, i ≤ j → x i = x j → Φ (j.val - i.val) (x i) = 0)
    (hspread : x 0 < x (Fin.last (n + 1))) :
    ∃ ξ₁ ∈ Icc a b, ∃ ξ₂ ∈ Icc a b, ξ₁ < ξ₂ ∧ Φ n ξ₁ = 0 ∧ Φ n ξ₂ = 0 := by
  induction n generalizing Φ with
  | zero =>
    refine ⟨x 0, hmem 0, x 1, hmem 1, hspread, ?_, ?_⟩
    · simpa using hzero 0 0 le_rfl rfl
    · simpa using hzero 1 1 le_rfl rfl
  | succ n ih =>
    have hbetween (i : Fin (n + 2)) :
        ∃ y ∈ Icc (x i.castSucc) (x i.succ),
          Φ 1 y = 0 ∧ (x i.castSucc < x i.succ → y ∈ Ioo (x i.castSucc) (x i.succ)) := by
      apply CAS.Continuum.exists_between_derivative_zero (hcontinuous 0 (by omega))
        (hderiv 0 (by omega)) (hmem i.castSucc) (hmem i.succ)
        (hmonotone (show i.castSucc ≤ i.succ from Nat.le_succ _))
      · simpa using hzero i.castSucc i.castSucc le_rfl rfl
      · simpa using hzero i.succ i.succ le_rfl rfl
      · intro heq
        simpa using hzero i.castSucc i.succ (Nat.le_succ _) heq
    choose y hy hyzero hystrict using hbetween
    have hsep {i j : Fin (n + 2)} (hij : i < j) : x i.succ ≤ x j.castSucc :=
      hmonotone (by simpa using hij)
    have hymono : Monotone y := fun i j hij ↦ hij.eq_or_lt.elim (fun h ↦ h ▸ le_rfl)
      fun hij ↦ (hy i).2.trans ((hsep hij).trans (hy j).1)
    have hymem (i : Fin (n + 2)) : y i ∈ Icc a b :=
      ⟨(hmem i.castSucc).1.trans (hy i).1, (hy i).2.trans (hmem i.succ).2⟩
    -- equal derived zeros come from a run of equal zeros one entry longer
    have hcollapse (i j : Fin (n + 2)) (hij : i < j) (heq : y i = y j) :
        y i = x i.castSucc ∧ x i.castSucc = x j.succ := by
      have hfirst : x i.castSucc = x i.succ := by
        by_contra hne
        linarith [(hystrict i ((hmonotone (show i.castSucc ≤ i.succ from Nat.le_succ _)).lt_of_ne
          hne)).2, (hy j).1, hsep hij]
      have hlast : x j.castSucc = x j.succ := by
        by_contra hne
        linarith [(hystrict j ((hmonotone (show j.castSucc ≤ j.succ from Nat.le_succ _)).lt_of_ne
          hne)).1, (hy i).2, hsep hij]
      have hyleft : y i = x i.castSucc :=
        le_antisymm (by simpa [← hfirst] using (hy i).2) (hy i).1
      have hyright : y j = x j.succ :=
        le_antisymm (hy j).2 (by simpa [hlast] using (hy j).1)
      exact ⟨hyleft, by rw [← hyleft, ← hyright, heq]⟩
    have hyrepeat (i j : Fin (n + 2)) (hij : i ≤ j) (heq : y i = y j) :
        Φ (j.val - i.val + 1) (y i) = 0 := by
      rcases hij.eq_or_lt with rfl | hij
      · simpa using hyzero i
      · obtain ⟨hyleft, hx⟩ := hcollapse i j hij heq
        have hz := hzero i.castSucc j.succ
          (show i.val ≤ j.val + 1 from (Fin.le_iff_val_le_val.mp hij.le).trans
            (Nat.le_succ _)) hx
        have horder : j.succ.val - i.castSucc.val = j.val - i.val + 1 := by
          simp only [Fin.val_succ, Fin.val_castSucc]
          have := hij.le
          omega
        rwa [horder, ← hyleft] at hz
    have hyspread : y 0 < y (Fin.last (n + 1)) := by
      refine lt_of_le_of_ne (hymono (Fin.zero_le _)) fun heq ↦ ?_
      obtain ⟨-, hx⟩ := hcollapse 0 (Fin.last (n + 1)) Fin.last_pos heq
      have hlast : (Fin.last (n + 1)).succ = Fin.last (n + 2) := rfl
      rw [hlast] at hx
      exact (lt_irrefl _) (hx ▸ hspread)
    exact ih (fun k ↦ Φ (k + 1))
      (fun k hk ↦ hcontinuous (k + 1) (by omega))
      (fun k hk ↦ hderiv (k + 1) (by omega)) y hymono hymem hyrepeat hyspread

/-- Multiset form of `exists_two_derivative_chain_zeros`: `n + 2` zeros of `Φ 0` in `[a, b]`
counted with multiplicity (`Φ k z = 0` for `k` below the multiplicity of `z`), not all equal,
give two distinct zeros of `Φ n`. -/
theorem exists_two_derivative_chain_zeros_of_multiset {a b : ℝ} (n : ℕ) (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ k < n, ContinuousOn (Φ k) (Icc a b))
    (hderiv : ∀ k < n, ∀ z ∈ Ioo a b, HasDerivAt (Φ k) (Φ (k + 1) z) z)
    (s : Multiset ℝ) (hcard : s.card = n + 2) (hmem : ∀ z ∈ s, z ∈ Icc a b)
    (hzero : ∀ z ∈ s, ∀ k < s.count z, Φ k z = 0)
    {z₁ z₂ : ℝ} (hz₁ : z₁ ∈ s) (hz₂ : z₂ ∈ s) (hne : z₁ ≠ z₂) :
    ∃ ξ₁ ∈ Icc a b, ∃ ξ₂ ∈ Icc a b, ξ₁ < ξ₂ ∧ Φ n ξ₁ = 0 ∧ Φ n ξ₂ = 0 := by
  classical
  let v : List.Vector ℝ (n + 2) := ⟨s.sort (· ≤ ·), by simpa using hcard⟩
  have hmono : Monotone v.get := fun i j hij ↦ (s.pairwise_sort (· ≤ ·)).rel_get_of_le hij
  have hvmem (i : Fin (n + 2)) : v.get i ∈ s :=
    (Multiset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)
  have hvsurj (z : ℝ) (hz : z ∈ s) : ∃ i, v.get i = z := by
    have hz' : z ∈ v.toList := (Multiset.mem_sort (· ≤ ·)).mpr hz
    obtain ⟨i, hi⟩ := List.get_of_mem hz'
    exact ⟨⟨i.val, by simpa using i.isLt⟩, by simpa [List.Vector.get_eq_get_toList] using hi⟩
  apply exists_two_derivative_chain_zeros n Φ hcontinuous hderiv v.get hmono
    (fun i ↦ hmem _ (hvmem i))
  · intro i j hij heq
    apply hzero _ (hvmem i)
    have hsub : Finset.Icc i j ⊆ Finset.univ.filter (fun k ↦ v.get k = v.get i) := fun k hk ↦
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_antisymm
        ((hmono (Finset.mem_Icc.mp hk).2).trans heq.ge) (hmono (Finset.mem_Icc.mp hk).1)⟩
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Icc, Fin.card_filter_univ_eq_vector_get_eq_count] at hc
    have hcount : v.toList.count (v.get i) = s.count (v.get i) := by
      change (s.sort (· ≤ ·)).count _ = _
      rw [← Multiset.coe_count, Multiset.sort_eq]
    rw [hcount] at hc
    have := Fin.le_iff_val_le_val.mp hij
    omega
  · refine lt_of_le_of_ne (hmono (Fin.zero_le _)) fun heq ↦ hne ?_
    obtain ⟨i₁, rfl⟩ := hvsurj z₁ hz₁
    obtain ⟨i₂, rfl⟩ := hvsurj z₂ hz₂
    have hconst (i : Fin (n + 2)) : v.get i = v.get 0 :=
      le_antisymm ((hmono (Fin.le_last i)).trans heq.ge) (hmono (Fin.zero_le i))
    rw [hconst i₁, hconst i₂]

/-- A derivative chain step with a bounded derivative is Lipschitz on the closed interval. -/
theorem lipschitz_of_abs_deriv_le {g g' : ℝ → ℝ} {a b M : ℝ} (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ z ∈ Ioo a b, HasDerivAt g (g' z) z) (hbound : ∀ z ∈ Ioo a b, |g' z| ≤ M) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |g x - g y| ≤ M * |x - y| := by
  have key : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x < y → |g y - g x| ≤ M * (y - x) := by
    intro x hx y hy hxy
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g g' hxy
      (hcont.mono (Icc_subset_Icc hx.1 hy.2))
      (fun z hz ↦ hderiv z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩)
    have hpos : 0 < y - x := sub_pos.mpr hxy
    have heq : g y - g x = g' c * (y - x) := by
      rw [hslope]
      field_simp
    rw [heq, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right
      (hbound c ⟨hx.1.trans_lt hc.1, hc.2.trans_le hy.2⟩) hpos.le
  intro x hx y hy
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · rw [abs_sub_comm, abs_sub_comm x y, abs_of_pos (sub_pos.mpr hxy)]
    exact key x hx y hy hxy
  · simp
  · rw [abs_of_pos (sub_pos.mpr hxy)]
    exact key y hy x hx hxy

/-- The `n`-th derivative of the monic polynomial `∏_{z ∈ s} (X - z)` of degree `n + 1` has slope
`(n + 1)!`. -/
theorem eval_iterate_derivative_prod_sub (s : Multiset ℝ) {n : ℕ} (hcard : s.card = n + 1)
    (u v : ℝ) :
    (derivative^[n] (s.map fun z ↦ X - C z).prod).eval u -
      (derivative^[n] (s.map fun z ↦ X - C z).prod).eval v =
      (n + 1).factorial * (u - v) := by
  set w := (s.map fun z ↦ X - C z).prod
  have hw : w.Monic := monic_multiset_prod_of_monic _ _ fun z _ ↦ monic_X_sub_C z
  have hdeg : w.natDegree = n + 1 := by
    rw [natDegree_multiset_prod_X_sub_C_eq_card, hcard]
  have hq : (derivative^[n] w).natDegree < 2 := by
    have := natDegree_iterate_derivative w n
    omega
  have hcoeff : (derivative^[n] w).coeff 1 = (n + 1).factorial := by
    rw [coeff_iterate_derivative, show 1 + n = n + 1 by ring, ← hdeg, hw.coeff_natDegree, hdeg,
      nsmul_eq_mul, mul_one, Nat.descFactorial_eq_div (by omega), show n + 1 - n = 1 by omega,
      Nat.factorial_one, Nat.div_one]
  rw [eval_eq_sum_range' hq, eval_eq_sum_range' hq]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero, pow_one,
    hcoeff, zero_add]
  ring

/-- **Interpolation remainder with a Lipschitz top derivative.** Let `Φ` be a derivative chain of
order `n` on `[a, b]` with `Φ n` `L`-Lipschitz there, and let `p` be a polynomial of degree at most
`n` whose derivatives agree with the chain on a multiset `s` of `n + 1` points of `[a, b]` up to
the multiplicity of each point. Then
`|Φ 0 x - p x| ≤ L / (n + 1)! |∏_{z ∈ s} (x - z)|` on `[a, b]`.

Distinct points give Lagrange interpolation, double points Hermite interpolation. The classical
form with `‖f^{(n+1)}‖_{L^∞}` is the case where `L` bounds the next derivative
(`lipschitz_of_abs_deriv_le`). -/
theorem abs_sub_eval_le_of_lipschitz {a b L : ℝ} {n : ℕ} (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ k < n, ContinuousOn (Φ k) (Icc a b))
    (hderiv : ∀ k < n, ∀ z ∈ Ioo a b, HasDerivAt (Φ k) (Φ (k + 1) z) z)
    (hlip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |Φ n x - Φ n y| ≤ L * |x - y|)
    (p : ℝ[X]) (hp : p.natDegree ≤ n) (s : Multiset ℝ) (hcard : s.card = n + 1)
    (hmem : ∀ z ∈ s, z ∈ Icc a b)
    (hagree : ∀ z ∈ s, ∀ k < s.count z, Φ k z = (derivative^[k] p).eval z)
    {x : ℝ} (hx : x ∈ Icc a b) :
    |Φ 0 x - p.eval x| ≤ L / (n + 1).factorial * |(s.map fun z ↦ x - z).prod| := by
  classical
  by_cases hxs : x ∈ s
  · have h0 := hagree x hxs 0 (Multiset.count_pos.mpr hxs)
    simp only [Function.iterate_zero, id_eq] at h0
    simp [h0, Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨x, hxs, sub_self x⟩)]
  set w := (s.map fun z ↦ X - C z).prod with hwdef
  have hweval : w.eval x = (s.map fun z ↦ x - z).prod := by
    simp only [hwdef, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub, eval_X,
      eval_C]
  have hwx : w.eval x ≠ 0 := by
    rw [hweval]
    refine Multiset.prod_ne_zero fun h0 ↦ ?_
    obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.mp h0
    exact hxs (by rwa [← sub_eq_zero.mp hz0] at hz)
  have hw0 : w ≠ 0 := fun h ↦ hwx (by simp [h])
  set c := (Φ 0 x - p.eval x) / w.eval x with hcdef
  let G : ℕ → ℝ → ℝ := fun k y ↦ Φ k y - (derivative^[k] p).eval y - c * (derivative^[k] w).eval y
  have hGcont : ∀ k < n, ContinuousOn (G k) (Icc a b) := fun k hk ↦
    ((hcontinuous k hk).sub (derivative^[k] p).continuous.continuousOn).sub
      (continuousOn_const.mul (derivative^[k] w).continuous.continuousOn)
  have hGderiv : ∀ k < n, ∀ z ∈ Ioo a b, HasDerivAt (G k) (G (k + 1) z) z := by
    intro k hk z hz
    convert ((hderiv k hk z hz).sub ((derivative^[k] p).hasDerivAt z)).sub
      (((derivative^[k] w).hasDerivAt z).const_mul c) using 1
    simp only [G, Function.iterate_succ_apply']
  have hroot (z : ℝ) (k : ℕ) (hk : k < s.count z) : (derivative^[k] w).eval z = 0 := by
    have hmult : w.rootMultiplicity z = s.count z := by
      rw [← count_roots, hwdef, roots_multiset_prod_X_sub_C]
    exact isRoot_iterate_derivative_of_lt_rootMultiplicity (hmult ▸ hk)
  -- the zeros of `G 0`: the points of `s` and `x`
  have hGzero : ∀ z ∈ x ::ₘ s, ∀ k < (x ::ₘ s).count z, G k z = 0 := by
    intro z hz k hk
    by_cases hzx : z = x
    · subst hzx
      obtain rfl : k = 0 := by
        rw [Multiset.count_cons_self, Multiset.count_eq_zero.mpr hxs] at hk; omega
      simp only [G, Function.iterate_zero, id_eq, hcdef]
      field_simp
      ring
    · have hzs : z ∈ s := (Multiset.mem_cons.mp hz).resolve_left hzx
      rw [Multiset.count_cons_of_ne hzx] at hk
      simp [G, hagree z hzs k hk, hroot z k hk]
  obtain ⟨z₀, hz₀⟩ : ∃ z, z ∈ s := Multiset.card_pos_iff_exists_mem.mp (by omega)
  have hne : x ≠ z₀ := fun h ↦ hxs (h ▸ hz₀)
  obtain ⟨ξ₁, hξ₁, ξ₂, hξ₂, hlt, h₁, h₂⟩ := exists_two_derivative_chain_zeros_of_multiset n G
    hGcont hGderiv (x ::ₘ s) (by simp [hcard])
    (fun z hz ↦ (Multiset.mem_cons.mp hz).elim (· ▸ hx) (hmem z)) hGzero
    (Multiset.mem_cons_self x s)
    (Multiset.mem_cons_of_mem hz₀) hne
  -- `p⁽ⁿ⁾` is constant and `w⁽ⁿ⁾` has slope `(n + 1)!`
  have hpconst : (derivative^[n] p).eval ξ₂ = (derivative^[n] p).eval ξ₁ := by
    rw [eq_C_of_natDegree_eq_zero (p := derivative^[n] p)
      (by have := natDegree_iterate_derivative p n; omega)]
    simp
  have hwslope := eval_iterate_derivative_prod_sub s hcard ξ₂ ξ₁
  rw [← hwdef] at hwslope
  have hdiff : Φ n ξ₂ - Φ n ξ₁ = c * ((n + 1).factorial * (ξ₂ - ξ₁)) := by
    simp only [G] at h₁ h₂
    rw [← hwslope]
    linear_combination h₂ - h₁ + hpconst
  have hfac : (0 : ℝ) < (n + 1).factorial := by positivity
  have hpos : 0 < ξ₂ - ξ₁ := sub_pos.mpr hlt
  have hc : |c| * (n + 1).factorial ≤ L := by
    have h := hlip ξ₂ hξ₂ ξ₁ hξ₁
    rw [hdiff, abs_mul, abs_mul, abs_of_pos hfac, abs_of_pos hpos] at h
    exact le_of_mul_le_mul_right (by linarith) hpos
  have hrepr : Φ 0 x - p.eval x = c * w.eval x := (div_mul_cancel₀ _ hwx).symm
  rw [hrepr, abs_mul, ← hweval, div_mul_eq_mul_div, le_div_iff₀ hfac]
  linarith [mul_le_mul_of_nonneg_right hc (abs_nonneg (w.eval x))]

/-- **Remainder at distinct nodes.** For `k + 1` distinct nodes in `[a, b]`, a derivative chain of
order `k` with `L`-Lipschitz top derivative, and any polynomial `q` of degree at most `k` taking
the values of `Φ 0` at the nodes, `|Φ 0 x - q x| ≤ L / (k + 1)! |∏ᵢ (x - xᵢ)|` on `[a, b]`. -/
theorem abs_sub_eval_le_of_nodes {a b L : ℝ} {k : ℕ} (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < k, ContinuousOn (Φ j) (Icc a b))
    (hderiv : ∀ j < k, ∀ z ∈ Ioo a b, HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |Φ k x - Φ k y| ≤ L * |x - y|)
    (nodes : Fin (k + 1) → ℝ) (hnodes : Function.Injective nodes)
    (hmem : ∀ i, nodes i ∈ Icc a b) (q : ℝ[X]) (hq : q.natDegree ≤ k)
    (hval : ∀ i, q.eval (nodes i) = Φ 0 (nodes i)) {x : ℝ} (hx : x ∈ Icc a b) :
    |Φ 0 x - q.eval x| ≤ L / (k + 1).factorial * |∏ i, (x - nodes i)| := by
  classical
  set s : Multiset ℝ := (Finset.univ : Finset (Fin (k + 1))).val.map nodes
  have hs : (s.map fun z ↦ x - z).prod = ∏ i, (x - nodes i) := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  rw [← hs]
  refine abs_sub_eval_le_of_lipschitz Φ hcontinuous hderiv hlip q hq s (by simp [s])
    (fun z hz ↦ ?_) (fun z hz j hj ↦ ?_) hx
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hz
    exact hmem i
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hz
    have hcount : s.count (nodes i) = 1 :=
      Multiset.count_eq_one_of_mem (Multiset.Nodup.map hnodes Finset.univ.nodup) hz
    rw [hcount] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [Function.iterate_zero, id_eq]
    exact (hval i).symm

/-- **Lagrange remainder (Supp II (8.12), one variable).** For `k + 1` distinct nodes in `[a, b]`
and a derivative chain of order `k` with `L`-Lipschitz top derivative, the Lagrange interpolant
`P` of `Φ 0` at the nodes satisfies `|Φ 0 x - P x| ≤ L / (k + 1)! |∏ᵢ (x - xᵢ)|` on `[a, b]`. -/
theorem abs_sub_interpolate_le {a b L : ℝ} {k : ℕ} (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < k, ContinuousOn (Φ j) (Icc a b))
    (hderiv : ∀ j < k, ∀ z ∈ Ioo a b, HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |Φ k x - Φ k y| ≤ L * |x - y|)
    (nodes : Fin (k + 1) → ℝ) (hnodes : Function.Injective nodes)
    (hmem : ∀ i, nodes i ∈ Icc a b) {x : ℝ} (hx : x ∈ Icc a b) :
    |Φ 0 x - (Lagrange.interpolate Finset.univ nodes (fun i ↦ Φ 0 (nodes i))).eval x| ≤
      L / (k + 1).factorial * |∏ i, (x - nodes i)| := by
  have hinj : Set.InjOn nodes (Finset.univ : Finset (Fin (k + 1))) := hnodes.injOn
  refine abs_sub_eval_le_of_nodes Φ hcontinuous hderiv hlip nodes hnodes hmem _ ?_
    (fun i ↦ Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i)) hx
  have h := Lagrange.degree_interpolate_lt (r := fun i ↦ Φ 0 (nodes i)) hinj
  rw [Finset.card_univ, Fintype.card_fin] at h
  by_cases hP : Lagrange.interpolate Finset.univ nodes (fun i ↦ Φ 0 (nodes i)) = 0
  · simp [hP]
  · rw [degree_eq_natDegree hP] at h
    exact Nat.lt_succ_iff.mp (by exact_mod_cast h)

end PDE.Analysis.Approximation
