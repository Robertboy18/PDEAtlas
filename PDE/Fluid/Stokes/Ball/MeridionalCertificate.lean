/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.RootCertificate

/-!
# Soundness of the meridional root check

`meridional_roots_of_check` turns a successful `meridionalCheck l E F`, together with
enclosures `E` of the zeros of `j_l` in `(0, 100]`, into the meridional roots below `100`: every
zero of the meridional boundary function in `(0, 100)` lies in an interval of `F`, and each
interval of `F` contains exactly one zero.

## How it works

We apply `PDE.Analysis.mem_Ioo_of_regions`, which locates the zeros of a function whose derivative
has a fixed sign at its zeros on each region, to `f = meridionalBoundaryJ l`. The breakpoints are
`0`, the zeros of `j_l` in `(0, 100)`, the point `γ = √(l (l - 1)(l + 2))` when it is active, and
`100`. At a zero `α > 0` of `f` we have `Q_l(α²) > 0`
(`boundaryFunction_meridional_ne_zero_of_rootPolynomial_nonpos`) and
`f'(α) (α² - γ²) = j_l(α) Q_l(α²)` (`deriv_meridionalBoundaryJ_mul_of_eq_zero`), so `f'` has the
sign of `j_l (α² - γ²)` there. On each region `j_l` and `α² - γ²` keep their signs, which the check
reads at the left end of the enclosure, or at `100` for a region without one
(`meridionalCheck_spec`, `rootPointSigns_sound`). At the breakpoints `f` does not vanish: at a zero
`z` of `j_l` it is `(z² - γ²) j_{l+1}(z)` (`meridionalBoundaryJ_of_sphericalBesselJ_eq_zero`), and
at `γ` it is `-(l - 1)² (l + 1) γ j_l(γ)` (`meridionalBoundaryJ_of_sq_eq`).
-/

@[expose] public section

open PDE.Analysis.SpecialFunctions

namespace PDE.Fluid.Stokes.Ball

/-- A predicate on `{0, ..., N - 1}` that is closed downwards holds exactly below the number of
indices that satisfy it. -/
private theorem lt_length_filter_range_iff (p : ℕ → Bool) (N : ℕ)
    (hp : ∀ k, k + 1 < N → p (k + 1) = true → p k = true) :
    ∀ k < N, (p k = true ↔ k < ((List.range N).filter p).length) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hle : ((List.range N).filter p).length ≤ N := (List.length_filter_le _ _).trans (by simp)
    intro k hk
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hN : p N = true
    · have hall : ∀ j ≤ N, p j = true := fun j hj ↦
        Nat.decreasingInduction (fun i hi h ↦ hp i (by omega) h) hN hj
      rw [List.filter_eq_self.2 fun j hj ↦ hall j (List.mem_range.1 hj).le]
      simp [hN, hall k (by omega), hk]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · simpa [hN] using ih (fun k hk ↦ hp k (by omega)) k hk
      · simpa [hN] using hle

/-- At most `E.length` zeros of `j_l` lie below `γ`. -/
theorem gammaPosition_le (l : ℕ) (E : List (ℕ × ℕ)) : gammaPosition l E ≤ E.length :=
  (List.length_filter_le _ _).trans (by simp)

/-- Only the breakpoint `gammaPosition l E + 1` is `γ`, and only when `γ` is active. -/
theorem meridionalBreakpoint_eq_none {l : ℕ} {E : List (ℕ × ℕ)} {i : ℕ}
    (h : meridionalBreakpoint l E i = none) :
    gammaActive l = true ∧ i = gammaPosition l E + 1 := by
  unfold meridionalBreakpoint at h
  split_ifs at h with h₁ h₂ h₃
  · exact ⟨h₁, h₃⟩

/-- Consecutive breakpoints that are both zeros of `j_l` are consecutive zeros. -/
theorem meridionalBreakpoint_succ {l : ℕ} {E : List (ℕ × ℕ)} {i j j' : ℕ} (hi : 1 ≤ i)
    (h : meridionalBreakpoint l E i = some j) (h' : meridionalBreakpoint l E (i + 1) = some j') :
    j' = j + 1 := by
  unfold meridionalBreakpoint at h h'
  split_ifs at h h' <;> simp only [Option.some.injEq] at h h' <;> omega

/-- The zero of `j_l` just before the breakpoint `γ` is one of the first
`gammaPosition l E` zeros. -/
theorem meridionalBreakpoint_some_none {l : ℕ} {E : List (ℕ × ℕ)} {i j : ℕ} (hi : 1 ≤ i)
    (h : meridionalBreakpoint l E i = some j) (h' : meridionalBreakpoint l E (i + 1) = none) :
    j < gammaPosition l E := by
  have ⟨_, h₂⟩ := meridionalBreakpoint_eq_none h'
  unfold meridionalBreakpoint at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> omega

/-- The zero of `j_l` just after the breakpoint `γ` is not among the first
`gammaPosition l E` zeros. -/
theorem meridionalBreakpoint_none_some {l : ℕ} {E : List (ℕ × ℕ)} {i j : ℕ}
    (h : meridionalBreakpoint l E i = none) (h' : meridionalBreakpoint l E (i + 1) = some j) :
    gammaPosition l E ≤ j := by
  have ⟨h₁, h₂⟩ := meridionalBreakpoint_eq_none h
  unfold meridionalBreakpoint at h'
  split_ifs at h' <;> simp only [Option.some.injEq] at h' <;> omega

/-- Every interior breakpoint that is a zero of `j_l` is an entry of `E`. -/
theorem meridionalBreakpoint_some_lt {l : ℕ} {E : List (ℕ × ℕ)} {i j : ℕ} (hi : 1 ≤ i)
    (hic : i ≤ meridionalBreakpointCount l E) (h : meridionalBreakpoint l E i = some j) :
    j < E.length := by
  have hP := gammaPosition_le l E
  unfold meridionalBreakpoint at h
  unfold meridionalBreakpointCount at hic
  split_ifs at h hic <;> simp only [Option.some.injEq] at h <;> omega

/-- Every entry of `E` is an interior breakpoint. -/
theorem exists_meridionalBreakpoint_eq_some {l : ℕ} {E : List (ℕ × ℕ)} {j : ℕ}
    (hj : j < E.length) : ∃ i, 1 ≤ i ∧ i ≤ meridionalBreakpointCount l E ∧
      meridionalBreakpoint l E i = some j := by
  unfold meridionalBreakpoint meridionalBreakpointCount
  by_cases ha : gammaActive l = true
  · by_cases hjP : j < gammaPosition l E
    · exact ⟨j + 1, by omega, by simp only [ha, ite_true]; omega, by simp [ha]; omega⟩
    · refine ⟨j + 2, by omega, by simp only [ha, ite_true]; omega, ?_⟩
      simp only [ha, ite_true]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
  · exact ⟨j + 1, by omega, by simp [ha]; omega, by simp [ha]⟩

/-- When `γ` is active it is the interior breakpoint `gammaPosition l E + 1`. -/
theorem meridionalBreakpoint_gammaPosition {l : ℕ} {E : List (ℕ × ℕ)} (ha : gammaActive l = true) :
    meridionalBreakpoint l E (gammaPosition l E + 1) = none ∧
      gammaPosition l E + 1 ≤ meridionalBreakpointCount l E := by
  have hP := gammaPosition_le l E
  unfold meridionalBreakpoint meridionalBreakpointCount
  simp only [ha, ite_true]
  rw [ite_eq_right (by omega)]
  exact ⟨rfl, by omega⟩

/-! ### Dyadic points -/

/-- `(a / 2 ^ 40)² < G` as a comparison of natural numbers. -/
private theorem sq_div_two_pow_lt_iff {a G : ℕ} :
    ((a : ℝ) / 2 ^ 40) ^ 2 < G ↔ a ^ 2 < G * 2 ^ 80 := by
  have e : ((a : ℝ) / 2 ^ 40) ^ 2 = ((a ^ 2 : ℕ) : ℝ) / ((2 ^ 80 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [e, div_lt_iff₀ (by positivity), ← Nat.cast_mul, Nat.cast_lt]

/-- `G < (a / 2 ^ 40)²` as a comparison of natural numbers. -/
private theorem lt_sq_div_two_pow_iff {a G : ℕ} :
    (G : ℝ) < ((a : ℝ) / 2 ^ 40) ^ 2 ↔ G * 2 ^ 80 < a ^ 2 := by
  have e : ((a : ℝ) / 2 ^ 40) ^ 2 = ((a ^ 2 : ℕ) : ℝ) / ((2 ^ 80 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [e, lt_div_iff₀ (by positivity), ← Nat.cast_mul, Nat.cast_lt]

/-- `a / 2 ^ 40 < √G` from a comparison of natural numbers. -/
private theorem div_two_pow_lt_sqrt {a G : ℕ} (h : a ^ 2 < G * 2 ^ 80) :
    (a : ℝ) / 2 ^ 40 < Real.sqrt G :=
  Real.lt_sqrt_of_sq_lt (sq_div_two_pow_lt_iff.mpr h)

/-- `√G < a / 2 ^ 40` from a comparison of natural numbers. -/
private theorem sqrt_lt_div_two_pow {a G : ℕ} (h : G * 2 ^ 80 < a ^ 2) :
    Real.sqrt G < (a : ℝ) / 2 ^ 40 :=
  (Real.sqrt_lt (Nat.cast_nonneg G) (by positivity)).2 (lt_sq_div_two_pow_iff.mpr h)

/-- `gammaSign l n = 1` for `n / 2 ^ 40 > γ`. -/
theorem gammaSign_eq_one {l n : ℕ} (h : gammaSq l * 2 ^ 80 < n ^ 2) : gammaSign l n = 1 :=
  ite_eq_left h

/-- `gammaSign l n = -1` for `n / 2 ^ 40 ≤ γ`. -/
theorem gammaSign_eq_neg_one {l n : ℕ} (h : ¬gammaSq l * 2 ^ 80 < n ^ 2) :
    gammaSign l n = -1 :=
  ite_eq_right h

/-- `gammaSign l n` is a sign. -/
theorem gammaSign_sq (l n : ℕ) : (gammaSign l n : ℝ) ^ 2 = 1 := by
  unfold gammaSign
  split_ifs <;> norm_num

/-- `gammaSign l n` does not vanish. -/
theorem gammaSign_ne_zero (l n : ℕ) : gammaSign l n ≠ 0 := by
  unfold gammaSign
  split_ifs <;> norm_num

/-! ### Signs -/

/-- For `x > 0`, `meridionalBoundaryJ l x` has the sign of the meridional boundary
function. -/
private theorem mul_meridionalBoundaryJ_pos {l : ℕ} {c x : ℝ} (hx : 0 < x)
    (h : 0 < c * boundaryFunction .meridional l x) : 0 < c * meridionalBoundaryJ l x := by
  rw [← pow_mul_boundaryFunction_meridional_eq, mul_left_comm]
  exact mul_pos (pow_pos hx _) h

/-- For `x > 0`, `j_l x` has the sign of `g_l x`. -/
private theorem mul_sphericalBesselJ_pos_of_reduced {l : ℕ} {c x : ℝ} (hx : 0 < x)
    (h : 0 < c * reducedSphericalBesselJ l x) : 0 < c * sphericalBesselJ l x := by
  rw [sphericalBesselJ_eq_pow_mul, mul_left_comm]
  exact mul_pos (pow_pos hx _) h

/-! ### The check -/

/-- The conditions of `meridionalCheck` that the soundness proof uses. -/
theorem meridionalCheck_spec {l : ℕ} {E F : List (ℕ × ℕ)} (h : meridionalCheck l E F = true) :
    enclosuresSorted F = true ∧
      (F.length = meridionalBreakpointCount l E + 1 ∨
        F.length = meridionalBreakpointCount l E) ∧
      (gammaActive l = true → ∀ k < E.length,
        (E.getD k (0, 0)).2 ^ 2 < gammaSq l * 2 ^ 80 ∨
          gammaSq l * 2 ^ 80 < (E.getD k (0, 0)).1 ^ 2) ∧
      (∀ k < F.length, meridionalLeftCheck l E k (F.getD k (0, 0)).1 = true ∧
        meridionalRightCheck l E k (F.getD k (0, 0)).2 = true ∧
        (rootPointSigns l (F.getD k (0, 0)).1).1 ≠ 0 ∧
        (rootPointSigns l (F.getD k (0, 0)).1).2.2.1 =
          -((rootPointSigns l (F.getD k (0, 0)).1).1 * gammaSign l (F.getD k (0, 0)).1) ∧
        (rootPointSigns l (F.getD k (0, 0)).2).2.2.1 =
          (rootPointSigns l (F.getD k (0, 0)).1).1 * gammaSign l (F.getD k (0, 0)).1) ∧
      (cutSigns l).1 ≠ 0 ∧ (cutSigns l).2.2.1 ≠ 0 ∧
      (F.length = meridionalBreakpointCount l E →
        (cutSigns l).2.2.1 = -((cutSigns l).1 * gammaSign l cutNumerator)) := by
  unfold meridionalCheck at h
  obtain ⟨h₁, hcut⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h₂, hall⟩ := Bool.and_eq_true_iff.mp h₁
  obtain ⟨h₃, hγ⟩ := Bool.and_eq_true_iff.mp h₂
  obtain ⟨hF, hlen⟩ := Bool.and_eq_true_iff.mp h₃
  refine ⟨hF, of_decide_eq_true hlen, fun ha k hk ↦ ?_, fun k hk ↦ ?_, ?_⟩
  · rw [ha, Bool.not_true, Bool.false_or, List.all_eq_true] at hγ
    exact of_decide_eq_true (hγ k (List.mem_range.mpr hk))
  · have h' := List.all_eq_true.mp hall k (List.mem_range.mpr hk)
    obtain ⟨h'', hS⟩ := Bool.and_eq_true_iff.mp h'
    obtain ⟨hL, hR⟩ := Bool.and_eq_true_iff.mp h''
    refine ⟨hL, hR, ?_⟩
    generalize rootPointSigns l (F.getD k (0, 0)).1 = u at hS ⊢
    generalize rootPointSigns l (F.getD k (0, 0)).2 = w at hS ⊢
    obtain ⟨a, b, y, t⟩ := u
    obtain ⟨c, d, v, r⟩ := w
    obtain ⟨h₁, -, h₃, h₄⟩ := of_decide_eq_true hS
    exact ⟨h₁, h₃, h₄⟩
  · generalize cutSigns l = u at hcut ⊢
    obtain ⟨a, b, y, t⟩ := u
    exact of_decide_eq_true hcut

/-! ### The meridional roots below `100` -/

/-- For sorted enclosures, `k < gammaPosition l E` exactly when the right end `b` of entry `k`
of `E` satisfies `b² < γ² 2 ^ 80`, that is `b / 2 ^ 40 < γ`. -/
theorem lt_gammaPosition_iff {l : ℕ} {E : List (ℕ × ℕ)} (hs : enclosuresSorted E = true) {k : ℕ}
    (hk : k < E.length) :
    k < gammaPosition l E ↔ (E.getD k (0, 0)).2 ^ 2 < gammaSq l * 2 ^ 80 := by
  have h := lt_length_filter_range_iff
    (fun k ↦ decide ((E.getD k (0, 0)).2 ^ 2 < gammaSq l * 2 ^ 80)) E.length (fun k hk hp ↦ by
      have h₁ := (enclosuresSorted_spec hs (k := k) (by omega)).2.2.2.resolve_left (by omega)
      have h₂ := (enclosuresSorted_spec hs (k := k + 1) hk).2.1
      exact decide_eq_true
        ((Nat.pow_lt_pow_left (h₁.trans h₂) two_ne_zero).trans (of_decide_eq_true hp))) k hk
  rw [decide_eq_true_iff] at h
  exact h.symm

/-- `gammaSign l n` is the sign of `x² - γ²` at every `0 ≤ x < γ` when `n / 2 ^ 40 ≤ γ`, where
`γ = √(gammaSq l)`. -/
theorem gammaSign_mul_sub_pos_of_lt_sqrt {l n : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hxγ : x < Real.sqrt (gammaSq l)) (hn : (n : ℝ) / 2 ^ 40 ≤ Real.sqrt (gammaSq l)) :
    0 < (gammaSign l n : ℝ) * (x ^ 2 - gammaSq l) := by
  rw [gammaSign_eq_neg_one fun h ↦ not_le.mpr (sqrt_lt_div_two_pow h) hn]
  have := (Real.lt_sqrt hx).mp hxγ
  push_cast
  linarith

/-- `gammaSign l n` is the sign of `x² - γ²` at every `x > γ` when `n / 2 ^ 40 > γ`, where
`γ = √(gammaSq l)`. -/
theorem gammaSign_mul_sub_pos_of_sqrt_lt {l n : ℕ} {x : ℝ} (hxγ : Real.sqrt (gammaSq l) < x)
    (hn : Real.sqrt (gammaSq l) < (n : ℝ) / 2 ^ 40) :
    0 < (gammaSign l n : ℝ) * (x ^ 2 - gammaSq l) := by
  have hγ := Real.sqrt_nonneg (gammaSq l : ℝ)
  rw [gammaSign_eq_one (lt_sq_div_two_pow_iff.mp ((Real.sqrt_lt' (hγ.trans_lt hn)).mp hn))]
  have := (Real.sqrt_lt' (hγ.trans_lt hxγ)).mp hxγ
  push_cast
  linarith

/-- A successful `meridionalLeftCheck l E k a` with `1 ≤ k` puts `a / 2 ^ 40` above breakpoint
`k`, which is `γ = √(gammaSq l)` or a point `z j < enclosureHi E j`. -/
private theorem meridionalBreakpoint_elim_lt_of_meridionalLeftCheck {l : ℕ} {E : List (ℕ × ℕ)}
    {k a : ℕ} {z : ℕ → ℝ} (hz : ∀ j < E.length, z j < enclosureHi E j) (hk : 1 ≤ k)
    (hkc : k ≤ meridionalBreakpointCount l E) (h : meridionalLeftCheck l E k a = true) :
    (meridionalBreakpoint l E k).elim (Real.sqrt (gammaSq l)) z < (a : ℝ) / 2 ^ 40 := by
  unfold meridionalLeftCheck at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact absurd (of_decide_eq_true h) (by omega)
  revert h
  rcases hb : meridionalBreakpoint l E k with _ | j
  · intro h
    exact sqrt_lt_div_two_pow (of_decide_eq_true h)
  · intro h
    exact (hz j (meridionalBreakpoint_some_lt hk hkc hb)).trans_le
      (natCast_div_two_pow_forty_le (of_decide_eq_true h))

/-- A successful `meridionalRightCheck l E k b` with `k < meridionalBreakpointCount l E` puts
`b / 2 ^ 40` below breakpoint `k + 1`, which is `γ = √(gammaSq l)` or a point
`z j > enclosureLo E j`. -/
private theorem lt_meridionalBreakpoint_elim_of_meridionalRightCheck {l : ℕ} {E : List (ℕ × ℕ)}
    {k b : ℕ} {z : ℕ → ℝ} (hz : ∀ j < E.length, enclosureLo E j < z j)
    (hk : k < meridionalBreakpointCount l E) (h : meridionalRightCheck l E k b = true) :
    (b : ℝ) / 2 ^ 40 < (meridionalBreakpoint l E (k + 1)).elim (Real.sqrt (gammaSq l)) z := by
  unfold meridionalRightCheck at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact absurd (of_decide_eq_true h) (by omega)
  revert h
  rcases hb : meridionalBreakpoint l E (k + 1) with _ | j
  · intro h
    exact div_two_pow_lt_sqrt (of_decide_eq_true h)
  · intro h
    exact (natCast_div_two_pow_forty_le (of_decide_eq_true h)).trans_lt
      (hz j (meridionalBreakpoint_some_lt (by omega) hk hb))

/-- At a zero `x > 0` of `f = meridionalBoundaryJ l`, `f'(x)` has the sign of
`j_l(x) (x² - γ²)`: if `a j_l(x) > 0` and `g (x² - γ²) > 0`, then `a g f'(x) > 0`. -/
private theorem mul_deriv_meridionalBoundaryJ_pos {l : ℕ} (hl : 1 ≤ l) {a g x : ℝ} (hx : 0 < x)
    (hfx : meridionalBoundaryJ l x = 0) (ha : 0 < a * sphericalBesselJ l x)
    (hg : 0 < g * (x ^ 2 - l * (l - 1) * (l + 2))) :
    0 < a * g * deriv (meridionalBoundaryJ l) x := by
  have hQ : 0 < meridionalRootPolynomial l (x ^ 2) := by
    by_contra hle
    push Not at hle
    exact boundaryFunction_meridional_ne_zero_of_rootPolynomial_nonpos hl hx hle
      ((boundaryFunction_meridional_eq_zero_iff hx).mpr hfx)
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hg
    exact lt_irrefl _ hg
  have e : a * g * deriv (meridionalBoundaryJ l) x * (g * (x ^ 2 - l * (l - 1) * (l + 2))) =
      a * sphericalBesselJ l x * meridionalRootPolynomial l (x ^ 2) * g ^ 2 := by
    linear_combination a * g ^ 2 * deriv_meridionalBoundaryJ_mul_of_eq_zero hx.ne' hfx
  refine pos_of_mul_pos_left ?_ hg.le
  rw [e]
  exact mul_pos (mul_pos ha hQ) (lt_of_le_of_ne (sq_nonneg g) (pow_ne_zero 2 hg0).symm)

/-- The sign that the check records for the meridional boundary function at a dyadic point
`n / 2 ^ 40 > 0`. -/
private theorem mul_meridionalBoundaryJ_pos_of_rootPointSigns {l n : ℕ} (hn : 0 < n) {c : ℤ}
    (hc : (rootPointSigns l n).2.2.1 = c) (hc0 : c ≠ 0) :
    0 < (c : ℝ) * meridionalBoundaryJ l (n / 2 ^ 40) := by
  subst hc
  exact mul_meridionalBoundaryJ_pos (natCast_div_two_pow_forty_pos hn)
    ((rootPointSigns_sound l n).2.2.1 hc0)

/-- **Meridional roots below `100`.** If `E` encloses the zeros of `j_l` in `(0, 100]` and
`meridionalCheck l E F` succeeds, then every meridional root in `(0, 100)` lies in an interval of
`F`, and each interval of `F` contains exactly one meridional root. -/
theorem meridional_roots_of_check {l : ℕ} (hl : 1 ≤ l) {E F : List (ℕ × ℕ)}
    (hE : JZeroEnclosures l E) (h : meridionalCheck l E F = true) :
    (∀ α ∈ Set.Ioo (0 : ℝ) 100, boundaryFunction .meridional l α = 0 →
        ∃ k < F.length, α ∈ Set.Ioo (enclosureLo F k) (enclosureHi F k)) ∧
      ∀ k < F.length, ∃! α, α ∈ Set.Ioo (enclosureLo F k) (enclosureHi F k) ∧
        boundaryFunction .meridional l α = 0 := by
  obtain ⟨hFs, hlen, hγc, hent, hcA, hcY, hcut⟩ := meridionalCheck_spec h
  unfold cutSigns at hcA hcY hcut
  set N := E.length with hN
  set cnt := meridionalBreakpointCount l E with hcnt
  set P := gammaPosition l E with hPdef
  set m := F.length with hm
  have hPN : P ≤ N := gammaPosition_le l E
  set G : ℝ := (gammaSq l : ℝ) with hGdef
  set γ : ℝ := Real.sqrt G with hγdef
  have hγsq : γ ^ 2 = G := Real.sq_sqrt (Nat.cast_nonneg _)
  have hGl : G = l * ((l : ℝ) - 1) * (l + 2) := by
    rw [hGdef, gammaSq]
    push_cast [Nat.cast_sub hl]
    ring
  have hact : gammaActive l = true ↔ 2 ≤ l ∧ gammaSq l < 10 ^ 4 := decide_eq_true_iff
  have hl₂ : gammaActive l = true → (2 : ℝ) ≤ l := fun ha ↦ mod_cast (hact.mp ha).1
  have hnact : gammaActive l ≠ true → G = 0 ∨ 10 ^ 4 ≤ G := fun ha ↦ by
    rw [ne_eq, hact, not_and, not_lt] at ha
    rcases Nat.lt_or_ge l 2 with h2 | h2
    · obtain rfl : l = 1 := by omega
      exact Or.inl (by rw [hGl]; norm_num)
    · exact Or.inr (by rw [hGdef]; exact_mod_cast ha h2)
  -- the zeros of `j_l`
  choose! z hz using fun k (hk : k < N) ↦ (hE.existsUnique k hk).exists
  have hzu : ∀ j < N, ∀ y ∈ Set.Ioo (enclosureLo E j) (enclosureHi E j),
      sphericalBesselJ l y = 0 → y = z j := fun j hj y hy hy0 ↦
    (hE.existsUnique j hj).unique ⟨hy, hy0⟩ (hz j hj)
  have hz0 : ∀ j < N, 0 < z j := fun j hj ↦ (enclosureLo_pos hE.sorted hj).trans (hz j hj).1.1
  have hz100 : ∀ j < N, z j < 100 := fun j hj ↦
    (hz j hj).1.2.trans (enclosureHi_lt_hundred hE.sorted hj)
  have hzz : ∀ i j, i < j → j < N → z i < z j := fun i j hij hj ↦
    ((hz i (hij.trans hj)).1.2.trans (enclosureHi_lt_enclosureLo hE.sorted hij hj)).trans
      (hz j hj).1.1
  -- the position of `γ`
  have hhiγ : gammaActive l = true → ∀ j < N, j < P → enclosureHi E j < γ :=
    fun _ j hj hjP ↦ div_two_pow_lt_sqrt ((lt_gammaPosition_iff hE.sorted hj).mp hjP)
  have hγlo : gammaActive l = true → ∀ j < N, P ≤ j → γ < enclosureLo E j :=
    fun ha j hj hjP ↦ sqrt_lt_div_two_pow ((hγc ha j hj).resolve_left
      fun h' ↦ not_lt.mpr hjP ((lt_gammaPosition_iff hE.sorted hj).mpr h'))
  have hzγ : gammaActive l = true → ∀ j < N, j < P → z j < γ :=
    fun ha j hj hjP ↦ (hz j hj).1.2.trans (hhiγ ha j hj hjP)
  have hγz : gammaActive l = true → ∀ j < N, P ≤ j → γ < z j :=
    fun ha j hj hjP ↦ (hγlo ha j hj hjP).trans (hz j hj).1.1
  have hγpos : gammaActive l = true → 0 < γ := fun ha ↦ Real.sqrt_pos.2 <| by
    have := hl₂ ha
    rw [hGl]
    exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hγ100 : gammaActive l = true → γ < 100 := fun ha ↦ (Real.sqrt_lt' (by norm_num)).2 <| by
    have : G < 10 ^ 4 := by rw [hGdef]; exact_mod_cast (hact.mp ha).2
    linarith
  have hzB : ∀ j < N, z j ^ 2 - G ≠ 0 := by
    intro j hj
    by_cases ha : gammaActive l = true
    · rcases lt_or_ge j P with hjP | hjP
      · exact sub_ne_zero.2 (hγsq ▸ (pow_lt_pow_left₀ (hzγ ha j hj hjP) (hz0 j hj).le
          two_ne_zero).ne)
      · exact sub_ne_zero.2 (hγsq ▸ (pow_lt_pow_left₀ (hγz ha j hj hjP) (Real.sqrt_nonneg _)
          two_ne_zero).ne')
    · rcases hnact ha with h0 | h4
      · rw [h0, sub_zero]
        exact (pow_pos (hz0 j hj) 2).ne'
      · nlinarith [pow_lt_pow_left₀ (hz100 j hj) (hz0 j hj).le two_ne_zero]
  -- the breakpoints
  set β : ℕ → ℝ := fun i ↦
    if i = 0 then 0 else if i ≤ cnt then (meridionalBreakpoint l E i).elim γ z else 100
    with hβdef
  have hβ0 : β 0 = 0 := ite_eq_left rfl
  have hβn : β (cnt + 1) = 100 := (ite_eq_right (by omega)).trans (ite_eq_right (by omega))
  have hβi : ∀ i, 1 ≤ i → i ≤ cnt → β i = (meridionalBreakpoint l E i).elim γ z :=
    fun i h₁ h₂ ↦ (ite_eq_right (by omega)).trans (ite_eq_left h₂)
  have hβv : ∀ i, 1 ≤ i → i ≤ cnt →
      (∃ j < N, β i = z j ∧ meridionalBreakpoint l E i = some j) ∨
        (gammaActive l = true ∧ i = P + 1 ∧ β i = γ ∧ meridionalBreakpoint l E i = none) := by
    intro i h₁ h₂
    rcases hb : meridionalBreakpoint l E i with _ | j
    · obtain ⟨ha, hi⟩ := meridionalBreakpoint_eq_none hb
      exact Or.inr ⟨ha, hi, by rw [hβi i h₁ h₂, hb]; rfl, rfl⟩
    · exact Or.inl ⟨j, meridionalBreakpoint_some_lt h₁ h₂ hb, by rw [hβi i h₁ h₂, hb]; rfl, rfl⟩
  have hβin : ∀ i, 1 ≤ i → i ≤ cnt → 0 < β i ∧ β i < 100 := fun i h₁ h₂ ↦ by
    rcases hβv i h₁ h₂ with ⟨j, hj, hβj, -⟩ | ⟨ha, -, hβj, -⟩ <;> rw [hβj]
    exacts [⟨hz0 j hj, hz100 j hj⟩, ⟨hγpos ha, hγ100 ha⟩]
  have hstep : ∀ i < cnt + 1, β i < β (i + 1) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi₁
    · rw [hβ0]
      rcases Nat.eq_zero_or_pos cnt with hc | hc
      · rw [show 0 + 1 = cnt + 1 by omega, hβn]
        norm_num
      · exact (hβin 1 le_rfl hc).1
    rcases Nat.lt_or_ge i cnt with hic | hic
    · rcases hβv i hi₁ hic.le with ⟨j, hj, hβj, hbj⟩ | ⟨ha, hiP, hβj, hbj⟩ <;>
        rcases hβv (i + 1) (by omega) hic with ⟨j', hj', hβj', hbj'⟩ | ⟨ha', hiP', hβj', hbj'⟩ <;>
        rw [hβj, hβj']
      · exact hzz j j' (by have := meridionalBreakpoint_succ hi₁ hbj hbj'; omega) hj'
      · exact hzγ ha' j hj (meridionalBreakpoint_some_none hi₁ hbj hbj')
      · exact hγz ha j' hj' (meridionalBreakpoint_none_some hbj hbj')
      · omega
    · rw [show i = cnt by omega, hβn]
      exact (hβin cnt (by omega) le_rfl).2
  have hmono : ∀ i j, i < j → j ≤ cnt + 1 → β i < β j := fun i j hij hj ↦
    strictMonoOn_Iic_of_lt_succ hstep (Set.mem_Iic.mpr (by omega)) (Set.mem_Iic.mpr hj) hij
  have hmono' : ∀ i j, i ≤ j → j ≤ cnt + 1 → β i ≤ β j := fun i j hij hj ↦
    (strictMonoOn_Iic_of_lt_succ hstep).monotoneOn (Set.mem_Iic.mpr (by omega))
      (Set.mem_Iic.mpr hj) hij
  have hβ01 : ∀ k ≤ cnt + 1, 0 ≤ β k ∧ β k ≤ 100 := fun k hk ↦
    ⟨hβ0 ▸ hmono' 0 k k.zero_le hk, hβn ▸ hmono' k (cnt + 1) hk le_rfl⟩
  -- the regions
  have hreg : ∀ k < cnt + 1, ∀ x ∈ Set.Ioo (β k) (β (k + 1)), 0 < x ∧ x < 100 :=
    fun k hk x hx ↦ ⟨(hβ01 k hk.le).1.trans_lt hx.1, hx.2.trans_le (hβ01 (k + 1) hk).2⟩
  have hnotβ : ∀ k < cnt + 1, ∀ x ∈ Set.Ioo (β k) (β (k + 1)), ∀ i ≤ cnt + 1, x ≠ β i := by
    rintro k hk x hx i hi rfl
    rcases Nat.lt_or_ge k i with h' | h'
    · exact (hmono' (k + 1) i (by omega) hi).not_gt hx.2
    · exact (hmono' i k h' (by omega)).not_gt hx.1
  have hjne : ∀ k < cnt + 1, ∀ x ∈ Set.Ioo (β k) (β (k + 1)), sphericalBesselJ l x ≠ 0 := by
    intro k hk x hx hjx
    obtain ⟨hx0, hx100⟩ := hreg k hk x hx
    obtain ⟨j, hj, hxj⟩ := hE.complete x ⟨hx0, hx100.le⟩ hjx
    obtain ⟨i, hi₁, hic, hbi⟩ := exists_meridionalBreakpoint_eq_some (l := l) hj
    have hβz : β i = z j := by rw [hβi i hi₁ hic, hbi]; rfl
    exact hnotβ k hk x hx i (by omega) ((hzu j hj x hxj hjx).trans hβz.symm)
  have hγβ : gammaActive l = true → β (P + 1) = γ ∧ P + 1 ≤ cnt := fun ha ↦ by
    obtain ⟨hb, hc⟩ := meridionalBreakpoint_gammaPosition (E := E) ha
    exact ⟨by rw [hβi (P + 1) (by omega) hc, hb]; rfl, hc⟩
  -- the enclosures of `F` and the signs
  have hFe : ∀ k < m, 0 < (F.getD k (0, 0)).1 ∧ (F.getD k (0, 0)).1 < (F.getD k (0, 0)).2 ∧
      (F.getD k (0, 0)).2 < cutNumerator := fun k hk ↦
    let h := enclosuresSorted_spec hFs hk; ⟨h.1, h.2.1, h.2.2.1⟩
  have hpq : ∀ k < m, enclosureLo F k < enclosureHi F k := fun k hk ↦
    natCast_div_two_pow_forty_lt (hFe k hk).2.1
  have hp : ∀ k < m, β k < enclosureLo F k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk₀
    · rw [hβ0]
      exact natCast_div_two_pow_forty_pos (hFe 0 hk).1
    · rw [hβi k hk₀ (by omega)]
      exact meridionalBreakpoint_elim_lt_of_meridionalLeftCheck (fun j hj ↦ (hz j hj).1.2) hk₀
        (by omega) (hent k hk).1
  have hq : ∀ k < m, enclosureHi F k < β (k + 1) := by
    intro k hk
    by_cases hck : cnt ≤ k
    · rw [show k + 1 = cnt + 1 by omega, hβn, enclosureHi, ← cutNumerator_div_two_pow_forty]
      exact natCast_div_two_pow_forty_lt (hFe k hk).2.2
    · rw [hβi (k + 1) (by omega) (by omega)]
      exact lt_meridionalBreakpoint_elim_of_meridionalRightCheck (fun j hj ↦ (hz j hj).1.1)
        (by omega) (hent k hk).2.1
  set R : ℕ → ℕ := fun k ↦ if k < m then (F.getD k (0, 0)).1 else cutNumerator with hRdef
  set s : ℕ → ℝ := fun k ↦ ((rootPointSigns l (R k)).1 : ℝ) * (gammaSign l (R k) : ℝ)
    with hsdef
  have hRlt : ∀ k < m, R k = (F.getD k (0, 0)).1 := fun k hk ↦ ite_eq_left hk
  have hRge : ∀ k, m ≤ k → R k = cutNumerator := fun k hk ↦ ite_eq_right (by omega)
  have hsk : ∀ k < m, s k = ((rootPointSigns l (F.getD k (0, 0)).1).1 : ℝ) *
      (gammaSign l (F.getD k (0, 0)).1 : ℝ) := fun k hk ↦ by simp only [hsdef, hRlt k hk]
  have hfp : ∀ k < m, s k * meridionalBoundaryJ l (enclosureLo F k) < 0 := fun k hk ↦ by
    have := mul_meridionalBoundaryJ_pos_of_rootPointSigns (hFe k hk).1 (hent k hk).2.2.2.1
      (neg_ne_zero.mpr (mul_ne_zero (hent k hk).2.2.1 (gammaSign_ne_zero _ _)))
    rw [hsk k hk, enclosureLo]
    push_cast at this
    linarith
  have hfq : ∀ k < m, 0 < s k * meridionalBoundaryJ l (enclosureHi F k) := fun k hk ↦ by
    have := mul_meridionalBoundaryJ_pos_of_rootPointSigns ((hFe k hk).1.trans (hFe k hk).2.1)
      (hent k hk).2.2.2.2 (mul_ne_zero (hent k hk).2.2.1 (gammaSign_ne_zero _ _))
    rw [hsk k hk, enclosureHi]
    exact_mod_cast this
  have hcut' : m < cnt + 1 → s m * meridionalBoundaryJ l (β (cnt + 1)) < 0 := fun hmc ↦ by
    have hY := hcut (by omega)
    have := mul_meridionalBoundaryJ_pos_of_rootPointSigns (by unfold cutNumerator; positivity) hY
      (hY ▸ hcY)
    rw [cutNumerator_div_two_pow_forty] at this
    have hsm : s m = ((rootPointSigns l cutNumerator).1 : ℝ) * (gammaSign l cutNumerator : ℝ) := by
      simp only [hsdef, hRge m le_rfl]
    rw [hsm, hβn]
    push_cast at this
    linarith
  -- the breakpoints are not zeros
  have hβf : ∀ k, 0 < k → k < cnt + 1 → meridionalBoundaryJ l (β k) ≠ 0 := by
    intro k hk₀ hkc
    rcases hβv k hk₀ (by omega) with ⟨j, hj, hβj, -⟩ | ⟨ha, -, hβj, -⟩
    · have hzj := (hz j hj).2
      rw [hβj, meridionalBoundaryJ_of_sphericalBesselJ_eq_zero hzj, ← hGl]
      exact mul_ne_zero (hzB j hj) (sphericalBesselJ_succ_ne_zero_of_eq_zero (hz0 j hj).ne' hzj)
    · have hjγ : sphericalBesselJ l γ ≠ 0 := fun h0 ↦ by
        obtain ⟨j, hj, hγj⟩ := hE.complete γ ⟨hγpos ha, (hγ100 ha).le⟩ h0
        rcases lt_or_ge j P with hjP | hjP
        · exact (hhiγ ha j hj hjP).not_gt hγj.2
        · exact (hγlo ha j hj hjP).not_gt hγj.1
      have hl₁ : (0 : ℝ) < l - 1 := by linarith [hl₂ ha]
      rw [hβj, meridionalBoundaryJ_of_sq_eq (hγsq.trans hGl)]
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by positivity)) (hγpos ha).ne') hjγ
  -- the sign of the derivative at the zeros
  have hs : ∀ k < cnt + 1, ∀ x ∈ Set.Ioo (β k) (β (k + 1)), meridionalBoundaryJ l x = 0 →
      0 < s k * deriv (meridionalBoundaryJ l) x := by
    intro k hk x hx hfx
    obtain ⟨hx0, hx100⟩ := hreg k hk x hx
    -- the signs are read at `R k / 2 ^ 40 ∈ (β k, β (k + 1)]`
    obtain ⟨hRβ, hRβ', hA⟩ : β k < (R k : ℝ) / 2 ^ 40 ∧ (R k : ℝ) / 2 ^ 40 ≤ β (k + 1) ∧
        (rootPointSigns l (R k)).1 ≠ 0 := by
      by_cases hkm : k < m
      · rw [hRlt k hkm]
        exact ⟨hp k hkm, ((hpq k hkm).trans (hq k hkm)).le, (hent k hkm).2.2.1⟩
      · rw [hRge k (by omega), cutNumerator_div_two_pow_forty, ← hβn,
          show k + 1 = cnt + 1 by omega]
        exact ⟨hmono k (cnt + 1) (by omega) le_rfl, le_rfl, hcA⟩
    have hR0 : 0 < (R k : ℝ) / 2 ^ 40 := (hβ01 k hk.le).1.trans_lt hRβ
    -- the sign of `j_l`
    have hJ := PDE.Analysis.pos_mul_of_witness (continuous_sphericalBesselJ l) (hjne k hk)
      ⟨hRβ, hRβ'⟩ (mul_sphericalBesselJ_pos_of_reduced hR0 ((rootPointSigns_sound l (R k)).1 hA))
      x hx
    -- the sign of `x² - γ²`
    have hΓ : 0 < (gammaSign l (R k) : ℝ) * (x ^ 2 - G) := by
      by_cases ha : gammaActive l = true
      · obtain ⟨hγb, hPc⟩ := hγβ ha
        by_cases hkP : k + 1 ≤ P + 1
        · have hb : β (k + 1) ≤ γ := hγb ▸ hmono' (k + 1) (P + 1) hkP (by omega)
          exact gammaSign_mul_sub_pos_of_lt_sqrt hx0.le (hx.2.trans_le hb) (hRβ'.trans hb)
        · have hb : γ ≤ β k := hγb ▸ hmono' (P + 1) k (by omega) (by omega)
          exact gammaSign_mul_sub_pos_of_sqrt_lt (hb.trans_lt hx.1) (hb.trans_lt hRβ)
      · rcases hnact ha with h0 | h4
        · have hγ' : γ = 0 := by rw [hγdef, h0, Real.sqrt_zero]
          exact gammaSign_mul_sub_pos_of_sqrt_lt (hγ'.trans_lt hx0) (hγ'.trans_lt hR0)
        · have h100 : 100 ≤ γ := Real.le_sqrt_of_sq_le (by linarith)
          exact gammaSign_mul_sub_pos_of_lt_sqrt hx0.le (hx100.trans_le h100)
            ((hRβ'.trans (hβ01 (k + 1) hk).2).trans h100)
    rw [hGl] at hΓ
    exact mul_deriv_meridionalBoundaryJ_pos hl hx0 hfx hJ hΓ
  -- conclusion
  obtain ⟨h₁, h₂⟩ := PDE.Analysis.mem_Ioo_of_regions (differentiable_meridionalBoundaryJ l)
    (n := cnt + 1) (m := m) (β := β) (p := enclosureLo F) (q := enclosureHi F) (s := s)
    hβf hs (by omega) (by omega) hp hpq hq hfp hfq hcut'
  refine ⟨fun α hα hFα ↦ h₁ α (by rwa [hβ0, hβn])
    ((boundaryFunction_meridional_eq_zero_iff hα.1).mp hFα), fun k hk ↦ ?_⟩
  refine (existsUnique_congr fun α ↦ and_congr_right fun hα ↦ ?_).mp (h₂ k hk)
  exact (boundaryFunction_meridional_eq_zero_iff
    ((hβ01 k (by omega)).1.trans_lt ((hp k hk).trans hα.1))).symm

end PDE.Fluid.Stokes.Ball
