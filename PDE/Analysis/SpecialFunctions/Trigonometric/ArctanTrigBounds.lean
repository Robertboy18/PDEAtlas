/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigTerms
public import PDE.Analysis.Calculus.IteratedDerivBound

/-!
# Derivatives of trigonometric sums in the compactified radius

For a sparse trigonometric sum `S(β) = trigTermsEval l β` and `β(r) = arctan (r / a)`, `a > 0`,
the derivative of `r ↦ S(β(r))` is again such a sum in `β`: since `β'(r) = cos² β / a`, it is
`cos² β · S'(β) / a`, the list `arctanDerivTerms a l` (`hasDerivAt_trigTermsEval_arctan`). Hence
all derivatives are sums in `β` (`iteratedDeriv_trigTermsEval_arctan`), and their sizes follow
from the coefficient norm `trigTermsNorm` and the largest frequency `trigTermsDegree`: one step
multiplies the norm by at most `D / a` and raises the frequency by at most `2`
(`trigTermsNorm_arctanDerivTerms_le`, `trigTermsDegree_arctanDerivTerms_le`). This gives
`iteratedDerivBoundOn_trigTermsEval_arctan`: `|dⁿ/drⁿ S(β(r))| ≤ ‖S‖₁ ∏_{j<n} (D + 2j) / a` on the
whole line, a real-variable bound for the profiles in the compactified variable. For sums given
by coefficient sequences, `∑_{k<K} (a k cos (kβ) + b k sin (kβ))` (`trigCoeffTerms`), the bound
reads `∑ (|a k| + |b k|) ∏_{j<n} (K + 2j) / a` (`iteratedDerivBoundOn_trigSum_arctan`).
-/

@[expose] public section

namespace PDE.Analysis

open Real

/-- The sum of the absolute coefficients of a list of terms. -/
def trigTermsNorm (l : List TrigTerm) : ℚ := (l.map fun t ↦ |t.coeff|).sum

/-- The largest absolute frequency of a list of terms. -/
def trigTermsDegree (l : List TrigTerm) : ℕ := (l.map fun t ↦ t.freq.natAbs).foldr max 0

theorem trigTermsNorm_nonneg (l : List TrigTerm) : 0 ≤ trigTermsNorm l := by
  unfold trigTermsNorm
  induction l with
  | nil => simp
  | cons t l ih => simp only [List.map_cons, List.sum_cons]; positivity

theorem trigTermsNorm_cons (t : TrigTerm) (l : List TrigTerm) :
    trigTermsNorm (t :: l) = |t.coeff| + trigTermsNorm l := by
  simp [trigTermsNorm]

theorem trigTermsNorm_append (l m : List TrigTerm) :
    trigTermsNorm (l ++ m) = trigTermsNorm l + trigTermsNorm m := by
  simp [trigTermsNorm]

theorem natAbs_freq_le_trigTermsDegree {l : List TrigTerm} {t : TrigTerm} (ht : t ∈ l) :
    t.freq.natAbs ≤ trigTermsDegree l := by
  induction l with
  | nil => simp at ht
  | cons s l ih =>
    simp only [trigTermsDegree, List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact le_max_left _ _
    · exact (ih ht).trans (le_max_right _ _)

theorem trigTermsDegree_le {l : List TrigTerm} {D : ℕ} (h : ∀ t ∈ l, t.freq.natAbs ≤ D) :
    trigTermsDegree l ≤ D := by
  induction l with
  | nil => simp [trigTermsDegree]
  | cons s l ih =>
    simp only [trigTermsDegree, List.map_cons, List.foldr_cons]
    exact max_le (h s List.mem_cons_self) (ih fun t ht ↦ h t (List.mem_cons_of_mem _ ht))

/-- A trigonometric sum is bounded by the sum of its absolute coefficients. -/
theorem abs_trigTermsEval_le (l : List TrigTerm) (θ : ℝ) :
    |trigTermsEval l θ| ≤ trigTermsNorm l := by
  induction l with
  | nil => simp [trigTermsEval, trigTermsNorm]
  | cons t l ih =>
    rw [trigTermsEval_cons, trigTermsNorm_cons]
    push_cast
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    unfold TrigTerm.eval
    rw [abs_mul]
    calc |(t.coeff : ℝ)| * |if t.isSin then Real.sin (t.freq * θ) else Real.cos (t.freq * θ)|
        ≤ |(t.coeff : ℝ)| * 1 := by
          gcongr
          split_ifs
          · exact abs_sin_le_one _
          · exact abs_cos_le_one _
      _ = |(t.coeff : ℝ)| := mul_one _

theorem trigTermsNorm_mul (s t : TrigTerm) : trigTermsNorm (s.mul t) = |s.coeff| * |t.coeff| := by
  rcases s with ⟨c, f, b⟩
  rcases t with ⟨c', f', b'⟩
  cases b <;> cases b' <;> simp [TrigTerm.mul, trigTermsNorm, abs_div, abs_mul]

theorem trigTermsNorm_flatMap_mul (s : TrigTerm) (m : List TrigTerm) :
    trigTermsNorm (m.flatMap fun t ↦ s.mul t) = |s.coeff| * trigTermsNorm m := by
  induction m with
  | nil => simp [trigTermsNorm]
  | cons t m ih =>
    rw [List.flatMap_cons, trigTermsNorm_append, ih, trigTermsNorm_cons, trigTermsNorm_mul,
      mul_add]

theorem trigTermsNorm_trigTermsMul (l m : List TrigTerm) :
    trigTermsNorm (trigTermsMul l m) = trigTermsNorm l * trigTermsNorm m := by
  unfold trigTermsMul
  induction l with
  | nil => simp [trigTermsNorm]
  | cons s l ih =>
    rw [List.flatMap_cons, trigTermsNorm_append, ih, trigTermsNorm_cons, add_mul,
      trigTermsNorm_flatMap_mul]

theorem natAbs_freq_le_of_mem_mul {s t u : TrigTerm} (hu : u ∈ s.mul t) :
    u.freq.natAbs ≤ s.freq.natAbs + t.freq.natAbs := by
  rcases s with ⟨c, f, b⟩
  rcases t with ⟨c', f', b'⟩
  cases b <;> cases b' <;>
    simp only [TrigTerm.mul, List.mem_cons, List.not_mem_nil, or_false] at hu <;>
    rcases hu with rfl | rfl <;> simp <;> omega

/-- `cos² β = 1/2 + cos (2β) / 2` as a list of terms. -/
def cosSqTerms : List TrigTerm := [⟨1 / 2, 0, false⟩, ⟨1 / 2, 2, false⟩]

theorem trigTermsEval_cosSqTerms (θ : ℝ) : trigTermsEval cosSqTerms θ = Real.cos θ ^ 2 := by
  simp only [cosSqTerms, trigTermsEval, TrigTerm.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Bool.false_eq_true, ↓reduceIte]
  push_cast
  rw [Real.cos_sq θ]
  simp
  ring

/-- The terms of `d/dr S(arctan (r / a))` in the variable `β = arctan (r / a)`. -/
def arctanDerivTerms (a : ℚ) (l : List TrigTerm) : List TrigTerm :=
  (trigTermsMul cosSqTerms (l.map TrigTerm.deriv)).map fun t ↦ ⟨t.coeff / a, t.freq, t.isSin⟩

theorem trigTermsEval_map_div (a : ℚ) (l : List TrigTerm) (θ : ℝ) :
    trigTermsEval (l.map fun t ↦ (⟨t.coeff / a, t.freq, t.isSin⟩ : TrigTerm)) θ =
      trigTermsEval l θ / a := by
  induction l with
  | nil => simp [trigTermsEval]
  | cons t l ih =>
    rw [List.map_cons, trigTermsEval_cons, trigTermsEval_cons, ih, add_div]
    congr 1
    unfold TrigTerm.eval
    push_cast
    ring

/-- The chain rule in the compactified variable. -/
theorem hasDerivAt_trigTermsEval_arctan {a : ℚ} (ha : 0 < a) (l : List TrigTerm) (r : ℝ) :
    HasDerivAt (fun r ↦ trigTermsEval l (Real.arctan (r / a)))
      (trigTermsEval (arctanDerivTerms a l) (Real.arctan (r / a))) r := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hβ : HasDerivAt (fun r : ℝ ↦ Real.arctan (r / a)) (1 / (1 + (r / a) ^ 2) * (1 / a)) r := by
    have h1 : HasDerivAt (fun r : ℝ ↦ r / a) (1 / a) r := by
      simpa using (hasDerivAt_id r).div_const (a : ℝ)
    exact (Real.hasDerivAt_arctan (r / a)).comp r h1
  have h := (hasDerivAt_trigTermsEval l (Real.arctan (r / a))).comp r hβ
  refine h.congr_deriv ?_
  rw [arctanDerivTerms, trigTermsEval_map_div, trigTermsEval_trigTermsMul,
    trigTermsEval_cosSqTerms, Real.cos_sq_arctan]
  ring

/-- The terms of the `n`th derivative. -/
def arctanIterTerms (a : ℚ) : ℕ → List TrigTerm → List TrigTerm
  | 0, l => l
  | n + 1, l => arctanDerivTerms a (arctanIterTerms a n l)

theorem iteratedDeriv_trigTermsEval_arctan {a : ℚ} (ha : 0 < a) (l : List TrigTerm) (n : ℕ) :
    iteratedDeriv n (fun r ↦ trigTermsEval l (Real.arctan (r / a))) =
      fun r ↦ trigTermsEval (arctanIterTerms a n l) (Real.arctan (r / a)) := by
  induction n with
  | zero => simp [arctanIterTerms]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext r
    exact (hasDerivAt_trigTermsEval_arctan ha (arctanIterTerms a n l) r).deriv

theorem trigTermsNorm_arctanDerivTerms_le {a : ℚ} (ha : 0 < a) (l : List TrigTerm) :
    trigTermsNorm (arctanDerivTerms a l) ≤ trigTermsDegree l / a * trigTermsNorm l := by
  have hmap : ∀ m : List TrigTerm, trigTermsNorm (m.map fun t ↦ (⟨t.coeff / a, t.freq,
      t.isSin⟩ : TrigTerm)) = trigTermsNorm m / a := by
    intro m
    induction m with
    | nil => simp [trigTermsNorm]
    | cons t m ih =>
      rw [List.map_cons, trigTermsNorm_cons, trigTermsNorm_cons, ih, abs_div, abs_of_pos ha,
        add_div]
  have hcos : trigTermsNorm cosSqTerms = 1 := by norm_num [cosSqTerms, trigTermsNorm]
  have hder : trigTermsNorm (l.map TrigTerm.deriv) ≤ trigTermsDegree l * trigTermsNorm l := by
    have key : ∀ m : List TrigTerm, (∀ t ∈ m, t.freq.natAbs ≤ trigTermsDegree l) →
        trigTermsNorm (m.map TrigTerm.deriv) ≤ trigTermsDegree l * trigTermsNorm m := by
      intro m hm
      induction m with
      | nil => simp [trigTermsNorm]
      | cons t m ih =>
        rw [List.map_cons, trigTermsNorm_cons, trigTermsNorm_cons, mul_add]
        refine add_le_add ?_ (ih fun u hu ↦ hm u (List.mem_cons_of_mem _ hu))
        have hf : (|(t.freq : ℚ)|) ≤ trigTermsDegree l := by
          have := hm t List.mem_cons_self
          rw [← Int.cast_abs, Int.abs_eq_natAbs]
          exact_mod_cast this
        unfold TrigTerm.deriv
        split_ifs
        · simp only [abs_mul]
          rw [mul_comm]; gcongr
        · simp only [abs_neg, abs_mul]
          rw [mul_comm]; gcongr
    exact key l fun t ht ↦ natAbs_freq_le_trigTermsDegree ht
  rw [arctanDerivTerms, hmap, trigTermsNorm_trigTermsMul, hcos, one_mul, div_le_iff₀ ha]
  calc trigTermsNorm (l.map TrigTerm.deriv) ≤ trigTermsDegree l * trigTermsNorm l := hder
    _ = trigTermsDegree l / a * trigTermsNorm l * a := by field_simp

theorem trigTermsDegree_arctanDerivTerms_le (a : ℚ) (l : List TrigTerm) :
    trigTermsDegree (arctanDerivTerms a l) ≤ trigTermsDegree l + 2 := by
  apply trigTermsDegree_le
  intro u hu
  simp only [arctanDerivTerms, List.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  simp only [trigTermsMul, List.mem_flatMap] at hv
  obtain ⟨s, hs, t, ht, hvst⟩ := hv
  have h1 := natAbs_freq_le_of_mem_mul hvst
  have hs2 : s.freq.natAbs ≤ 2 := by
    simp only [cosSqTerms, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  have ht'' : t'.freq.natAbs ≤ trigTermsDegree l := natAbs_freq_le_trigTermsDegree ht'
  have hd : (TrigTerm.deriv t').freq = t'.freq := by unfold TrigTerm.deriv; split_ifs <;> rfl
  simp only
  rw [hd] at h1
  omega

/-- All derivatives of `r ↦ S(arctan (r / a))`. -/
theorem iteratedDerivBoundOn_trigTermsEval_arctan {a : ℚ} (ha : 0 < a) (l : List TrigTerm)
    (s : Set ℝ) :
    IteratedDerivBoundOn (fun r ↦ trigTermsEval l (Real.arctan (r / a))) s
      (fun n ↦ (trigTermsNorm l : ℝ) *
        ∏ j ∈ Finset.range n, (((trigTermsDegree l + 2 * j : ℕ) : ℝ) / a)) := by
  have hnorm : ∀ n, trigTermsNorm (arctanIterTerms a n l) ≤ trigTermsNorm l *
      ∏ j ∈ Finset.range n, (((trigTermsDegree l + 2 * j : ℕ) : ℚ) / a) ∧
      trigTermsDegree (arctanIterTerms a n l) ≤ trigTermsDegree l + 2 * n := by
    intro n
    induction n with
    | zero => simp [arctanIterTerms]
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨?_, ?_⟩
      · change trigTermsNorm (arctanDerivTerms a (arctanIterTerms a n l)) ≤ _
        refine (trigTermsNorm_arctanDerivTerms_le ha _).trans ?_
        have hd : (trigTermsDegree (arctanIterTerms a n l) : ℚ) / a ≤
            ((trigTermsDegree l + 2 * n : ℕ) : ℚ) / a := by
          gcongr
        rw [Finset.prod_range_succ]
        calc _ ≤ ((trigTermsDegree l + 2 * n : ℕ) : ℚ) / a * (trigTermsNorm l *
              ∏ j ∈ Finset.range n, (((trigTermsDegree l + 2 * j : ℕ) : ℚ) / a)) :=
            mul_le_mul hd h1 (trigTermsNorm_nonneg _) (by positivity)
          _ = _ := by ring
      · change trigTermsDegree (arctanDerivTerms a (arctanIterTerms a n l)) ≤ _
        have := trigTermsDegree_arctanDerivTerms_le a (arctanIterTerms a n l)
        omega
  intro n x _
  rw [iteratedDeriv_trigTermsEval_arctan ha]
  refine (abs_trigTermsEval_le _ _).trans ?_
  have := (hnorm n).1
  have h' : ((trigTermsNorm (arctanIterTerms a n l) : ℚ) : ℝ) ≤
      ((trigTermsNorm l * ∏ j ∈ Finset.range n, (((trigTermsDegree l + 2 * j : ℕ) : ℚ) / a) : ℚ) :
        ℝ) := by exact_mod_cast this
  push_cast at h' ⊢
  exact h'

/-! ### Sums given by coefficient sequences -/

/-- The terms `a k cos (kβ) + b k sin (kβ)`, `k < K`. -/
def trigCoeffTerms (K : ℕ) (a b : ℕ → ℚ) : List TrigTerm :=
  (List.range K).flatMap fun k ↦ [⟨a k, k, false⟩, ⟨b k, k, true⟩]

theorem trigTermsEval_trigCoeffTerms (K : ℕ) (a b : ℕ → ℚ) (θ : ℝ) :
    trigTermsEval (trigCoeffTerms K a b) θ =
      ∑ k ∈ Finset.range K, ((a k : ℝ) * Real.cos (k * θ) + (b k : ℝ) * Real.sin (k * θ)) := by
  unfold trigCoeffTerms
  induction K with
  | zero => simp [trigTermsEval]
  | succ K ih =>
    rw [List.range_succ, List.flatMap_append, trigTermsEval_append, ih, Finset.sum_range_succ]
    simp [trigTermsEval, TrigTerm.eval]

theorem trigTermsNorm_trigCoeffTerms (K : ℕ) (a b : ℕ → ℚ) :
    trigTermsNorm (trigCoeffTerms K a b) = ∑ k ∈ Finset.range K, (|a k| + |b k|) := by
  unfold trigCoeffTerms
  induction K with
  | zero => simp [trigTermsNorm]
  | succ K ih =>
    rw [List.range_succ, List.flatMap_append, trigTermsNorm_append, ih, Finset.sum_range_succ]
    simp [trigTermsNorm]

theorem trigTermsDegree_trigCoeffTerms_le (K : ℕ) (a b : ℕ → ℚ) :
    trigTermsDegree (trigCoeffTerms K a b) ≤ K := by
  apply trigTermsDegree_le
  intro t ht
  simp only [trigCoeffTerms, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at ht
  obtain ⟨k, hk, rfl | rfl⟩ := ht <;> simp <;> omega

/-- All derivatives of `r ↦ ∑_{k<K} (a k cos (k β) + b k sin (k β))`, `β = arctan (r / c)`: at
most `∑ (|a k| + |b k|) ∏_{j<n} (K + 2j) / c`. -/
theorem iteratedDerivBoundOn_trigSum_arctan {c : ℚ} (hc : 0 < c) (K : ℕ) (a b : ℕ → ℚ)
    (s : Set ℝ) :
    IteratedDerivBoundOn (fun r ↦ ∑ k ∈ Finset.range K, ((a k : ℝ) *
        Real.cos (k * Real.arctan (r / c)) + (b k : ℝ) * Real.sin (k * Real.arctan (r / c)))) s
      (fun n ↦ (∑ k ∈ Finset.range K, ((|a k| : ℚ) + |b k|) : ℚ) *
        ∏ j ∈ Finset.range n, (((K + 2 * j : ℕ) : ℝ) / c)) := by
  have h := iteratedDerivBoundOn_trigTermsEval_arctan hc (trigCoeffTerms K a b) s
  have hfun : (fun r ↦ trigTermsEval (trigCoeffTerms K a b) (Real.arctan (r / c))) =
      fun r ↦ ∑ k ∈ Finset.range K, ((a k : ℝ) * Real.cos (k * Real.arctan (r / c)) +
        (b k : ℝ) * Real.sin (k * Real.arctan (r / c))) :=
    funext fun r ↦ trigTermsEval_trigCoeffTerms K a b _
  rw [hfun, trigTermsNorm_trigCoeffTerms] at h
  refine h.mono fun n ↦ ?_
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hN : (0 : ℝ) ≤ ((∑ k ∈ Finset.range K, ((|a k| : ℚ) + |b k|) : ℚ) : ℝ) := by
    exact_mod_cast Finset.sum_nonneg fun k _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _)
  gcongr with j _
  exact_mod_cast trigTermsDegree_trigCoeffTerms_le K a b

end PDE.Analysis
