/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.style.header false

/-!
# Order facts: minima, maxima, intervals

The lemmas compare minima and maxima, place a point in an interval and compare intervals. The proofs
are case splits closed by `linarith` or by the lemmas of Mathlib on `min` and `max`.

## Main results

* `PDE.Analysis.Icc_prod_Icc_subset_prod_Icc_abs`: For real `R`, `z₁`, `z₂`, the rectangle
  `Icc 0 R ×ˢ Icc z₁ z₂` is contained in the symmetric rectangle
  `Icc 0 R ×ˢ Icc (-(|z₁| + |z₂|)) (|z₁| + |z₂|)`.
* `PDE.Analysis.min_max_add_sub_of_mem_pair`: For reals `x < y` and `c` equal to `x` or to `y`, the
  numbers `c` and `x + y - c` are `x` and `y` in some order: `min c (x + y - c) = x` and
  `max c (x + y - c) = y`.
* `PDE.Analysis.lt_abs_of_notMem_Icc`: If a real `s` is not in `Set.Icc (-S) S`, then `S < |s|`.
* `PDE.Analysis.abs_le_of_mem_uIoc`: For reals `t` and `δ`, if `t` lies in the unordered interval
  `Ι 0 δ`, that is `Set.uIoc 0 δ`, then `|t| ≤ |δ|`.
* `PDE.Analysis.add_mul_floor_le_and_sub_lt`: For reals `0 < h` and `a ≤ s`, the grid point
  `a + h * ⌊(s - a) / h⌋` lies in `[a, s]` and is less than `h` below `s`:
  `a ≤ a + h * ⌊(s - a) / h⌋`, `a + h * ⌊(s - a) / h⌋ ≤ s` and `s - (a + h * ⌊(s - a) / h⌋) < h`.
* `PDE.Analysis.exists_injective_fin_le_lt_one`: For a real number `tb < 1` and a natural number `D`
  there is an injective map `v : Fin (D + 1) → ℝ` with `tb ≤ v k` and `v k < 1` for every `k`, that
  is, `D + 1` distinct points of the interval `[tb, 1)`.
* `PDE.Analysis.exists_lt_one_forall_mem_list_le`: If every element of a list of reals is less than
  `1`, there is a real `m` with `1 / 2 ≤ m`, `m < 1` and `b ≤ m` for every element `b` of the list.
* `PDE.Analysis.exists_nat_add_mul_lt_and_lt`: Let `s > 0` and `a < x < a + n * s` for real `a`,
  `x`, `s` and a natural number `n`, and suppose `x ≠ a + k * s` for every natural number `k`. Then
  there is a natural number `j` with `j + 1 ≤ n` and `a + j * s < x < a + (j + 1) * s`.

There are 21 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Set Real
open scoped Interval

namespace PDE.Analysis

/-- For real `R`, `z₁`, `z₂`, the rectangle `Icc 0 R ×ˢ Icc z₁ z₂` is contained in the symmetric
rectangle `Icc 0 R ×ˢ Icc (-(|z₁| + |z₂|)) (|z₁| + |z₂|)`. -/
theorem Icc_prod_Icc_subset_prod_Icc_abs (R z₁ z₂ : ℝ) :
    Icc (0 : ℝ) R ×ˢ Icc z₁ z₂ ⊆ Icc 0 R ×ˢ Icc (-(|z₁| + |z₂|)) (|z₁| + |z₂|) := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨h1, ?_, ?_⟩
  · linarith [neg_abs_le z₁, abs_nonneg z₂]
  · linarith [le_abs_self z₂, abs_nonneg z₁]

/-- For reals `t` and `δ`, if `t` lies in the unordered interval `Ι 0 δ`, that is `Set.uIoc 0 δ`,
then `|t| ≤ |δ|`. -/
theorem abs_le_of_mem_uIoc {t δ : ℝ} (ht : t ∈ Ι (0 : ℝ) δ) : |t| ≤ |δ| := by
  rcases mem_uIcc.1 (uIoc_subset_uIcc ht) with h | h
  · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]
    exact h.2
  · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]
    linarith [h.1]

/-- For real `t` and `s` and natural numbers `k ≤ N + 1`, the point `t + (k / (N + 1)) * (s - t)`
lies in the segment `segment ℝ t s`. -/
theorem add_div_mul_sub_mem_segment (t s : ℝ) (N k : ℕ) (hk : k ≤ N + 1) :
    t + ((k : ℝ) / (N + 1)) * (s - t) ∈ segment ℝ t s := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  have h0 : (0 : ℝ) ≤ (k : ℝ) / (N + 1) := by positivity
  have h1 : (k : ℝ) / (N + 1) ≤ 1 := by
    rw [div_le_one hN]; exact_mod_cast hk
  refine ⟨1 - (k : ℝ) / (N + 1), (k : ℝ) / (N + 1), by linarith, h0, by ring, ?_⟩
  simp only [smul_eq_mul]; ring

/-- For reals `0 < h` and `a ≤ s`, the grid point `a + h * ⌊(s - a) / h⌋` lies in `[a, s]` and is
less than `h` below `s`: `a ≤ a + h * ⌊(s - a) / h⌋`, `a + h * ⌊(s - a) / h⌋ ≤ s` and
`s - (a + h * ⌊(s - a) / h⌋) < h`. -/
theorem add_mul_floor_le_and_sub_lt {a s h : ℝ} (hh : 0 < h) (hs : a ≤ s) :
    a ≤ a + h * ⌊(s - a) / h⌋ ∧ a + h * ⌊(s - a) / h⌋ ≤ s ∧ s - (a + h * ⌊(s - a) / h⌋) < h := by
  have h0 : 0 ≤ (s - a) / h := div_nonneg (sub_nonneg.2 hs) hh.le
  have h1 : ((⌊(s - a) / h⌋ : ℤ) : ℝ) ≤ (s - a) / h := Int.floor_le _
  have h2 : (s - a) / h < ((⌊(s - a) / h⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : (0 : ℝ) ≤ ((⌊(s - a) / h⌋ : ℤ) : ℝ) := by exact_mod_cast Int.floor_nonneg.2 h0
  have e : h * ((s - a) / h) = s - a := by field_simp
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- For a real number `tb < 1` and a natural number `D` there is an injective map
`v : Fin (D + 1) → ℝ` with `tb ≤ v k` and `v k < 1` for every `k`, that is, `D + 1` distinct points
of the interval `[tb, 1)`. The proof takes the equally spaced points
`v k = tb + (1 - tb) * (k + 1) / (D + 2)`. -/
theorem exists_injective_fin_le_lt_one (tb : ℝ) (htb : tb < 1) (D : ℕ) :
    ∃ v : Fin (D + 1) → ℝ, Function.Injective v ∧ ∀ k, tb ≤ v k ∧ v k < 1 := by
  have hD : (0 : ℝ) < (D : ℝ) + 2 := by positivity
  have hc : (0 : ℝ) < 1 - tb := by linarith
  refine ⟨fun k ↦ tb + (1 - tb) * (((k : ℕ) : ℝ) + 1) / ((D : ℝ) + 2), ?_, fun k ↦ ⟨?_, ?_⟩⟩
  · intro a b hab
    have e1 := add_left_cancel hab
    rw [div_left_inj₀ hD.ne'] at e1
    have e2 := mul_left_cancel₀ hc.ne' e1
    exact Fin.ext (by exact_mod_cast add_right_cancel e2)
  · exact le_add_of_nonneg_right (by positivity)
  · have hk : (((k : ℕ) : ℝ) + 1) < (D : ℝ) + 2 := by
      have := k.isLt
      have : ((k : ℕ) : ℝ) ≤ D := by exact_mod_cast Nat.lt_succ_iff.1 this
      linarith
    have : (1 - tb) * (((k : ℕ) : ℝ) + 1) / ((D : ℝ) + 2) < 1 - tb := by
      rw [div_lt_iff₀ hD]
      nlinarith
    linarith

/-- If every element of a list of reals is less than `1`, there is a real `m` with `1 / 2 ≤ m`,
`m < 1` and `b ≤ m` for every element `b` of the list. The proof is by induction on the list, taking
the maximum with the head. -/
theorem exists_lt_one_forall_mem_list_le (l : List ℝ) (h : ∀ b ∈ l, b < 1) :
    ∃ m : ℝ, 1 / 2 ≤ m ∧ m < 1 ∧ ∀ b ∈ l, b ≤ m := by
  induction l with
  | nil => exact ⟨1 / 2, le_rfl, by norm_num, by simp⟩
  | cons a l ih =>
    obtain ⟨m, h1, h2, h3⟩ := ih (fun b hb ↦ h b (List.mem_cons_of_mem _ hb))
    refine ⟨max a m, le_max_of_le_right h1, max_lt (h a (by simp)) h2, ?_⟩
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact le_max_left _ _
    · exact le_max_of_le_right (h3 b hb)

/-- Let `s > 0` and `a < x < a + n * s` for real `a`, `x`, `s` and a natural number `n`, and suppose
`x ≠ a + k * s` for every natural number `k`. Then there is a natural number `j` with `j + 1 ≤ n`
and `a + j * s < x < a + (j + 1) * s`. The proof takes `j = ⌊(x - a) / s⌋₊`. -/
theorem exists_nat_add_mul_lt_and_lt {a x s : ℝ} (hs : 0 < s) {n : ℕ} (hx1 : a < x)
    (hx2 : x < a + (n : ℝ) * s)
    (hG : ∀ k : ℕ, x ≠ a + (k : ℝ) * s) :
    ∃ j : ℕ, j + 1 ≤ n ∧ a + (j : ℝ) * s < x ∧ x < a + ((j : ℝ) + 1) * s := by
  have ht0 : 0 ≤ (x - a) / s := div_nonneg (by linarith) hs.le
  refine ⟨⌊(x - a) / s⌋₊, ?_, ?_, ?_⟩
  · have h1 : (x - a) / s < n := by rw [div_lt_iff₀ hs]; linarith
    have h2 := (Nat.floor_lt ht0).2 h1
    omega
  · have hle : (⌊(x - a) / s⌋₊ : ℝ) ≤ (x - a) / s := Nat.floor_le ht0
    have hle' : a + (⌊(x - a) / s⌋₊ : ℝ) * s ≤ x := by
      have := mul_le_mul_of_nonneg_right hle hs.le
      rw [div_mul_cancel₀ _ hs.ne'] at this; linarith
    exact lt_of_le_of_ne hle' (fun e ↦ hG _ e.symm)
  · have h3 := Nat.lt_floor_add_one ((x - a) / s)
    have := mul_lt_mul_of_pos_right h3 hs
    rw [div_mul_cancel₀ _ hs.ne'] at this; linarith

/-- Finitely many properties that are monotone in a real constant share one constant. If `P j K` and
`K ≤ K'` imply `P j K'`, and every `j < n` has some `K` with `P j K`, then there is `K ≥ 0` with
`P j K` for all `j < n`. The proof is by induction on `n`, taking the maximum of the constants. -/
theorem exists_nonneg_forall_lt_of_mono (n : ℕ) (P : ℕ → ℝ → Prop)
    (hmono : ∀ j K K', P j K → K ≤ K' → P j K')
    (h : ∀ j < n, ∃ K, P j K) : ∃ K, 0 ≤ K ∧ ∀ j < n, P j K := by
  induction n with
  | zero => exact ⟨0, le_rfl, fun j hj ↦ absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨K, hK0, hK⟩ := ih (fun j hj ↦ h j (by omega))
    obtain ⟨K', hK'⟩ := h n (by omega)
    refine ⟨max K K', le_max_of_le_left hK0, fun j hj ↦ ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact hmono _ _ _ (hK j hj) (le_max_left _ _)
    · exact hmono _ _ _ hK' (le_max_right _ _)

/-- If every element of a list of reals is positive, there is `δ > 0` with `δ ≤ b` for every element
`b` of the list. -/
theorem exists_pos_forall_mem_list_le : ∀ (r : List ℝ), (∀ b ∈ r, 0 < b) → ∃ δ, 0 < δ ∧ ∀ b ∈ r, δ ≤
    b
  | [], _ => ⟨1, one_pos, fun b hb ↦ by simp at hb⟩
  | a :: r, h => by
    obtain ⟨δ, hδ, hr⟩ := exists_pos_forall_mem_list_le r
        (fun b hb ↦ h b (List.mem_cons_of_mem _ hb))
    refine ⟨min a δ, lt_min (h a (by simp)) hδ, fun b hb ↦ ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hr b hb)

/-- For real `s₀` and `s`, the image of `Set.Ioc s₀ s` under `x ↦ 1 - Real.exp (-(x - s₀))` is
`Set.Ioc 0 (1 - Real.exp (-(s - s₀)))`. The two inclusions are checked directly, and a point `r` of
the right side is the image of `s₀ - Real.log (1 - r)`. -/
theorem image_one_sub_exp_neg_Ioc (s₀ s : ℝ) :
    (fun x : ℝ ↦ 1 - exp (-(x - s₀))) '' Ioc s₀ s = Ioc 0 (1 - exp (-(s - s₀))) := by
  ext r
  constructor
  · rintro ⟨σ, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have : exp (-(σ - s₀)) < exp 0 := exp_lt_exp.mpr (by linarith)
      rw [exp_zero] at this
      linarith
    · have : exp (-(s - s₀)) ≤ exp (-(σ - s₀)) := exp_le_exp.mpr (by linarith)
      linarith
  · rintro ⟨h1, h2⟩
    have hpos : 0 < 1 - r := by
      have := exp_pos (-(s - s₀))
      linarith
    refine ⟨s₀ - Real.log (1 - r), ⟨?_, ?_⟩, ?_⟩
    · have : Real.log (1 - r) < 0 := Real.log_neg hpos (by linarith)
      linarith
    · have : -(s - s₀) ≤ Real.log (1 - r) := by
        rw [Real.le_log_iff_exp_le hpos]
        linarith
      linarith
    · simp only
      rw [show -(s₀ - Real.log (1 - r) - s₀) = Real.log (1 - r) by ring, Real.exp_log hpos]
      ring

/-- For a decidable proposition `p` and a real number `a ≥ 0`, `(if p then a else 0) ≤ a`. -/
theorem ite_zero_le_self_of_nonneg {p : Prop} [Decidable p] {a : ℝ} (ha : 0 ≤ a) :
    (if p then a else 0) ≤ a := by
  split_ifs <;> simp [ha]

/-- For a decidable proposition `p` and a real number `a ≥ 0`, `0 ≤ (if p then a else 0)`. -/
theorem ite_zero_nonneg_of_nonneg {p : Prop} [Decidable p] {a : ℝ} (ha : 0 ≤ a) : 0 ≤
    (if p then a else 0) := by
  split_ifs <;> simp [ha]

/-- For `f : ℤ × ℤ → ℝ` and reals `a` and `b` with `0 ≤ b`, if `a ≤ f ι * b` for all `ι`, then
`a ≤ (⨅ ι, f ι) * b`. For `b = 0` both bounds read `a ≤ 0`, and for `b > 0` the proof divides by
`b`. -/
theorem le_iInf_mul_of_forall_le {f : ℤ × ℤ → ℝ} {a b : ℝ} (hb : 0 ≤ b) (h : ∀ ι, a ≤ f ι * b) :
    a ≤ (⨅ ι, f ι) * b := by
  rcases hb.eq_or_lt with hb0 | hbpos
  · rw [← hb0, mul_zero]
    have := h 0
    rw [← hb0, mul_zero] at this
    exact this
  · have : a / b ≤ ⨅ ι, f ι := le_ciInf fun ι ↦ (div_le_iff₀ hbpos).mpr (h ι)
    exact (div_le_iff₀ hbpos).mp this

/-- If `0 < r`, `0 ≤ m`, `X ≤ A * r ^ 3` and `X ≤ B * r ^ 3 * m` for real numbers, then
`X ≤ max A B * r ^ 3 * min 1 m`. -/
theorem le_max_mul_cube_mul_min_one {X A B r m : ℝ} (hr : 0 < r) (hm : 0 ≤ m) (h1 : X ≤ A * r ^ 3)
    (h2 : X ≤ B * r ^ 3 * m) : X ≤ max A B * r ^ 3 * min 1 m := by
  have hr3 : 0 ≤ r ^ 3 := by positivity
  rcases le_total 1 m with h | h
  · rw [min_eq_left h, mul_one]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr3)
  · rw [min_eq_right h]
    exact h2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hr3) hm)

/-- If a real `s` is not in `Set.Ioo (-1) 1`, then `s ≤ -1` or `1 ≤ s`. -/
theorem le_or_le_of_notMem_Ioo_one {s : ℝ} (hs : s ∉ Set.Ioo (-1 : ℝ) 1) : s ≤ -1 ∨ 1 ≤ s := by
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hs
  exact hs

/-- For real numbers, if `a < τ` and `τ ≤ max a c`, then `τ ≤ c`. -/
theorem le_right_of_lt_of_le_max {τ a c : ℝ} (h1 : a < τ) (h2 : τ ≤ max a c) : τ ≤ c := by
  rcases le_max_iff.1 h2 with h | h
  · exact absurd h (not_le.2 h1)
  · exact h

/-- If a real `s` is not in `Set.Icc (-S) S`, then `S < |s|`. -/
theorem lt_abs_of_notMem_Icc {S s : ℝ} (h : s ∉ Set.Icc (-S) S) : S < |s| := by
  rw [Set.mem_Icc, ← abs_le] at h
  exact lt_of_not_ge h

/-- If the real number `s` lies in `Set.Icc a b`, then `max a (min b s) = s`. -/
theorem max_min_eq_self_of_mem_Icc {a b s : ℝ} (hs : s ∈ Icc a b) : max a (min b s) = s := by
  rw [min_eq_right hs.2, max_eq_right hs.1]

/-- If `a ≤ b` are real numbers, then `max a (min b s)` lies in `Set.Icc a b` for every real `s`. -/
theorem max_min_mem_Icc {a b : ℝ} (hab : a ≤ b) (s : ℝ) : max a (min b s) ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

/-- For every real `o`, `max 0 (-o) = -min 0 o`. -/
theorem max_zero_neg_eq_neg_min (o : ℝ) : max 0 (-o) = -min 0 o := by
  simpa using max_neg_neg (0 : ℝ) o

/-- For reals `x < y` and `c` equal to `x` or to `y`, the numbers `c` and `x + y - c` are `x` and
`y` in some order: `min c (x + y - c) = x` and `max c (x + y - c) = y`. -/
theorem min_max_add_sub_of_mem_pair {x y c : ℝ} (hxy : x < y) (hc : c = x ∨ c = y) :
    min c (x + y - c) = x ∧ max c (x + y - c) = y := by
  rcases hc with rfl | rfl
  · have : c + y - c = y := by ring
    rw [this]; exact ⟨min_eq_left hxy.le, max_eq_right hxy.le⟩
  · have : x + c - c = x := by ring
    rw [this]; exact ⟨min_eq_right hxy.le, max_eq_left hxy.le⟩

/-- For a real `lev`, `min lev (lev + 1) = lev` and `max lev (lev + 1) = lev + 1`. -/
theorem min_max_self_add_one (lev : ℝ) : min lev (lev + 1) = lev ∧ max lev (lev + 1) = lev + 1 :=
  ⟨min_eq_left (by linarith), max_eq_right (by linarith)⟩

/-- For every real `o`, `min 0 (-o) = -max 0 o`. -/
theorem min_zero_neg_eq_neg_max (o : ℝ) : min 0 (-o) = -max 0 o := by
  simpa using min_neg_neg (0 : ℝ) o

/-- For reals `0 ≤ r₁ < r₂` and `l` equal to `r₁` or to `r₂`, the numbers `l` and `r₁ + r₂ - l` are
nonnegative and different, and `0 ≤ min l (r₁ + r₂ - l)`. -/
theorem nonneg_ne_add_sub_of_mem_pair {r₁ r₂ l : ℝ} (h0 : 0 ≤ r₁) (h12 : r₁ < r₂)
    (hl : l = r₁ ∨ l = r₂) :
    0 ≤ min l (r₁ + r₂ - l) ∧ r₁ + r₂ - l ≠ l ∧ 0 ≤ l ∧ 0 ≤ r₁ + r₂ - l := by
  rcases hl with rfl | rfl
  · refine ⟨le_min h0 (by linarith), by linarith, h0, by linarith⟩
  · refine ⟨le_min (by linarith) (by linarith), by linarith, by linarith, by linarith⟩

/-- If a real `s` is not in `Set.Icc (-2) 2`, then it is not in `Set.Icc (-1) 1`. -/
theorem notMem_Icc_one_of_notMem_Icc_two {s : ℝ} (hs : s ∉ Set.Icc (-2 : ℝ) 2) :
    s ∉ Set.Icc (-1 : ℝ) 1 := by
  intro h
  exact hs ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Let `tlo j < thi j` for every `j : Fin n`, let `thi j = tlo j'` whenever `j'` is the index
after `j`, and let `tlo j = lo` for the index `j = 0`. Then `lo ≤ tlo j` for every `j`. By
induction on the index. -/
theorem le_left_endpoint_of_adjacent {n : ℕ} (tlo thi : Fin n → ℝ) (lo : ℝ)
    (hlt : ∀ j, tlo j < thi j)
    (hnext : ∀ j j' : Fin n, j.val + 1 = j'.val → thi j = tlo j')
        (hfirst : ∀ j : Fin n, j.val = 0 → tlo j = lo) :
    ∀ j : Fin n, lo ≤ tlo j := by
  intro j
  obtain ⟨m, hm⟩ := j
  induction m with
  | zero => exact (hfirst ⟨0, hm⟩ rfl).ge
  | succ m ih =>
    have h1 := ih (by omega)
    have h2 := hnext ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl
    have h3 := hlt ⟨m, by omega⟩
    linarith

/-- For every real `x`, `max x 0 = x + max (-x) 0`: the positive part of `x` is `x` plus its
negative part. -/
theorem max_zero_eq_add_max_neg_zero (x : ℝ) : max x 0 = x + max (-x) 0 := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring

/-- Let `u < w` be real and let `l` be `u` or `w`. Then
`Icc (min l (u + w - l)) (max l (u + w - l)) = Icc u w`, since `u + w - l` is the other
endpoint. -/
theorem Icc_min_max_add_sub_eq_Icc {u w l : ℝ} (huw : u < w) (hl : l = u ∨ l = w) :
    Icc (min l (u + w - l)) (max l (u + w - l)) = Icc u w := by
  rcases hl with rfl | rfl
  · rw [add_sub_cancel_left, min_eq_left huw.le, max_eq_right huw.le]
  · rw [add_sub_cancel_right, min_eq_right huw.le, max_eq_left huw.le]

/-- For all real `lo` and `hi`, the interval `[lo, hi]` is contained in the symmetric interval
`[-(|lo| + |hi|), |lo| + |hi|]`. -/
theorem Icc_subset_Icc_neg_abs_add_abs (lo hi : ℝ) :
    Icc lo hi ⊆ Icc (-(|lo| + |hi|)) (|lo| + |hi|) := fun s hs ↦
  ⟨by linarith [neg_abs_le lo, abs_nonneg hi, hs.1], by
    linarith [le_abs_self hi, abs_nonneg lo, hs.2]⟩

end PDE.Analysis
