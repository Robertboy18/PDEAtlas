/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.TensorSplineNodes.Evaluation
public import PDE.Numerics.Certificates.TensorSplineNodes.CellEnclosure
public import CAS.Numerics.SquareModels.Taylor

/-!
# Cell polynomials of tensor B-spline fields from exact jets

On a cell `[a, b] × [c, d]` separated from the knots, a multilevel tensor field of order `n + 2`
is the polynomial `∑ₘ ∑ᵢⱼ cₘᵢⱼ pᵢ(x) qⱼ(y)` of its mode pieces, of degree at most `n + 1` in each
variable, and only the modes with an active term contribute. Its derivatives at the lower left
corner are `D_kl = ∑ₘ ∑ᵢⱼ cₘᵢⱼ pᵢ^(k)(a) qⱼ^(l)(c)` with the exact rational jets `jet` of the
pieces, and on the closed cell
`∂ₓⁱ∂ᵧʲ F(a + δ, c + ε) = ∑ₖₗ D_{i+k, j+l} δᵏ εˡ / (k! l!)` (`mixedDeriv_field_eq_corner`).

`levelJets` lists the active modes of one level on one cell edge with their jets rounded to the
grid `2 ^ -Q`; `fixedCornerDeriv` contracts them with the coefficients rounded to `2 ^ -Qc`, in
integers, and `abs_cornerDeriv_sub_fixed_le` bounds the difference to the exact `D_kl`.

## Main definitions

* `cornerDeriv`: the exact corner derivative `D_kl` of the cell polynomial of a multilevel field.
* `levelJets`: the active modes of one level on a cell edge with their rounded jets.
* `fixedCornerDeriv`: the fixed-point corner derivative and its error, in units of
  `2 ^ -(Qc + 2Q)`.
* `SquareModel.ofCornerTable`: the unit-square model of `∂ₓⁱ∂ᵧʲ F` from a table of fixed-point
  corner derivatives.

## Main results

* `polynomialJet_add_eq_sum`: for `p` of degree at most `N`,
  `p^(i)(a + δ) = ∑_{k ≤ N} p^(i+k)(a) δᵏ / k!`.
* `mixedDeriv_field_eq_corner`: on the closed cell,
  `∂ₓⁱ∂ᵧʲ F(a + δ, c + ε) = ∑ₖₗ D_{i+k, j+l} δᵏ εˡ / (k! l!)`.
* `contractPairs_sound`: the fixed-point contraction of rounded jets differs from the exact sum by
  at most its error.
* `abs_cornerDeriv_sub_fixed_le`: `|D_kl - D̂_kl| ≤ e_kl` for the fixed-point corner derivative
  `D̂_kl` and its error `e_kl`.
* `cornerDeriv_eq_zero_of_lt`: `D_kl = 0` when `k` or `l` exceeds the degree `n + 1`.
* `SquareModel.ofCornerTable_encloses`: the corner-table model encloses the expansion of a function
  in its corner derivatives.
* `field_ofCornerTable_encloses`: the corner-table model encloses
  `(s, t) ↦ ∂ₓⁱ∂ᵧʲ F(a + (b - a) s, c + (d - c) t)` for `i, j ≤ n`.
-/

@[expose] public section

namespace CAS.Numerics.TensorSpline

open Finset _root_.Polynomial CAS.Splines

/-- The polynomial Taylor identity at the left end: for `p` of degree at most `N` and `δ ≥ 0`,
`p^(i)(a + δ) = ∑_{k ≤ N} p^(i+k)(a) δᵏ / k!`. -/
theorem polynomialJet_add_eq_sum {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) (i : ℕ) (a : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    polynomialJet i p (a + δ) =
      ∑ k ∈ range (N + 1), polynomialJet (i + k) p a / k.factorial * δ ^ k := by
  have hf : ContDiff ℝ (N + 1) (fun x ↦ polynomialJet i p x) := by
    have : (fun x ↦ polynomialJet i p x) = fun x ↦ (derivative^[i] p).eval x := rfl
    rw [this]
    exact PDE.Analysis.contDiff_polynomial_eval _
  have hjet : ∀ k, iteratedDeriv k (fun x ↦ polynomialJet i p x) = polynomialJet (i + k) p := by
    intro k
    have : (fun x ↦ polynomialJet i p x) = fun x ↦ (derivative^[i] p).eval x := rfl
    rw [this, iteratedDeriv_eval_eq_polynomialJet]
    funext x
    unfold polynomialJet
    rw [← Function.iterate_add_apply, add_comm]
  have h := SquareModel.abs_sub_taylor_le hf (a := a) (x := a + δ) (R := 0) (by linarith)
    (fun y _ ↦ by
      rw [hjet, abs_nonpos_iff]
      exact polynomialJet_eq_zero_of_degree_lt hp (by omega) y)
  simp only [zero_mul, zero_div, abs_nonpos_iff, sub_eq_zero, add_sub_cancel_left, hjet] at h
  exact h

/-- A triple sum over `s × t × u` may be summed with the outer index innermost. -/
private theorem sum_comm₃ {s t u : Finset ℕ} (g : ℕ → ℕ → ℕ → ℝ) :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, g x y z = ∑ y ∈ t, ∑ z ∈ u, ∑ x ∈ s, g x y z := by
  rw [Finset.sum_comm]
  exact sum_congr rfl fun y _ ↦ Finset.sum_comm

/-- The exact corner derivative `D_kl = ∑ₘ ∑ᵢⱼ cₘᵢⱼ pᵢ^(k)(a) qⱼ^(l)(c)` of the cell polynomial of
a multilevel field on `[a, b] × [c, d]`. -/
def cornerDeriv (n L : ℕ) (lv : ℕ → Level) (a b c d : ℚ) (k l : ℕ) : ℚ :=
  ∑ m ∈ range L, ∑ i ∈ range (lv m).rows, ∑ j ∈ range (lv m).cols,
    (lv m).coeff i j * jet n (lv m).xKnots ((lv m).xModes i) a b k a *
      jet n (lv m).yKnots ((lv m).yModes j) c d l c

/-- **The field on a cell from its corner derivatives**: for `δ, ε ≥ 0` with `(a + δ, c + ε)` in
the closed cell and orders `i, j ≤ n`,
`∂ₓⁱ∂ᵧʲ F(a + δ, c + ε) = ∑ₖₗ D_{i+k, j+l} δᵏ εˡ / (k! l!)`. -/
theorem mixedDeriv_field_eq_corner {n L : ℕ} {lv : ℕ → Level} {a b c d : ℚ} (hab : a < b)
    (hcd : c < d)
    (hx : ∀ m < L, ∀ i < (lv m).rows, ∀ τ ∈ (lv m).xModes i,
      τ.Separated n (lv m).xKnots (a : ℝ) (b : ℝ))
    (hy : ∀ m < L, ∀ j < (lv m).cols, ∀ τ ∈ (lv m).yModes j,
      τ.Separated n (lv m).yKnots (c : ℝ) (d : ℝ))
    {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) {δ ε : ℝ} (hδ : 0 ≤ δ) (hδb : (a : ℝ) + δ ≤ b)
    (hε : 0 ≤ ε) (hεd : (c : ℝ) + ε ≤ d) :
    mixedDeriv i j (field n L lv (fun _ ↦ 1)) (a + δ) (c + ε) =
      ∑ k ∈ range (n + 2), ∑ l ∈ range (n + 2),
        (cornerDeriv n L lv a b c d (i + k) (j + l) : ℝ) / (k.factorial * l.factorial) *
          δ ^ k * ε ^ l := by
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hcdR : (c : ℝ) < d := by exact_mod_cast hcd
  rw [mixedDeriv_field_eq (contDiff_const (c := (1 : ℝ))) habR hcdR hx hy hi hj
    ⟨by linarith, hδb⟩ ⟨by linarith, hεd⟩, mixedDeriv_cellField_one]
  have hpx : ∀ m i', polynomialJet i (piece n (lv m).xKnots ((lv m).xModes i') a b) (a + δ) =
      ∑ k ∈ range (n + 2), (jet n (lv m).xKnots ((lv m).xModes i') a b (i + k) a : ℝ) /
        k.factorial * δ ^ k := by
    intro m i'
    rw [polynomialJet_add_eq_sum (N := n + 1) (natDegree_piece_le n _ _ _ _) i _ hδ]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [polynomialJet_piece]
  have hpy : ∀ m j', polynomialJet j (piece n (lv m).yKnots ((lv m).yModes j') c d) (c + ε) =
      ∑ l ∈ range (n + 2), (jet n (lv m).yKnots ((lv m).yModes j') c d (j + l) c : ℝ) /
        l.factorial * ε ^ l := by
    intro m j'
    rw [polynomialJet_add_eq_sum (N := n + 1) (natDegree_piece_le n _ _ _ _) j _ hε]
    refine sum_congr rfl fun l _ ↦ ?_
    rw [polynomialJet_piece]
  simp only [hpx, hpy, cornerDeriv]
  push_cast
  have e1 : ∀ m i', ∑ j' ∈ range (lv m).cols, ((lv m).coeff i' j' : ℝ) *
      (∑ k ∈ range (n + 2), (jet n (lv m).xKnots ((lv m).xModes i') a b (i + k) a : ℝ) /
        k.factorial * δ ^ k) *
      (∑ l ∈ range (n + 2), (jet n (lv m).yKnots ((lv m).yModes j') c d (j + l) c : ℝ) /
        l.factorial * ε ^ l) =
      ∑ k ∈ range (n + 2), ∑ l ∈ range (n + 2), ∑ j' ∈ range (lv m).cols,
        ((lv m).coeff i' j' : ℝ) * (jet n (lv m).xKnots ((lv m).xModes i') a b (i + k) a : ℝ) *
          (jet n (lv m).yKnots ((lv m).yModes j') c d (j + l) c : ℝ) /
            (k.factorial * l.factorial) * δ ^ k * ε ^ l := by
    intro m i'
    rw [← sum_comm₃]
    refine sum_congr rfl fun j' _ ↦ ?_
    rw [mul_assoc, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun l _ ↦ ?_
    field_simp
  simp only [e1]
  rw [sum_congr rfl fun m _ ↦ sum_comm₃ (s := range (lv m).rows) _, sum_comm₃]
  refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
  rw [Finset.sum_div, Finset.sum_mul, Finset.sum_mul]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [Finset.sum_div, Finset.sum_mul, Finset.sum_mul]
  refine sum_congr rfl fun i' _ ↦ ?_
  rw [Finset.sum_div, Finset.sum_mul, Finset.sum_mul]

/-! ### Active modes and the fixed-point contraction -/

/-- The modes of one variable that have an active term on the cell `[A/D, B/D]`. -/
def activeModes (n : ℕ) (N : ℕ → ℤ) (modes : ℕ → List Term) (count : ℕ) (A B : ℤ) : List ℕ :=
  (List.range count).filter fun i ↦ !(modes i).all fun τ ↦ inactiveB n N τ A B

/-- For strictly increasing knot numerators and `D > 0`, a mode `i < count` that is not active on
the cell `[A/D, B/D]` has zero jets there. -/
theorem jet_eq_zero_of_not_mem_activeModes {n : ℕ} {N : ℕ → ℤ} {D : ℕ} (hN : StrictMono N)
    (hD : 0 < D) {modes : ℕ → List Term} {count : ℕ} {A B : ℤ} {i : ℕ} (hi : i < count)
    (h : i ∉ activeModes n N modes count A B) (k : ℕ) (x : ℚ) :
    jet n (ratKnots N D) (modes i) ((A : ℚ) / D) ((B : ℚ) / D) k x = 0 := by
  unfold activeModes at h
  simp only [List.mem_filter, List.mem_range, hi, true_and, Bool.not_eq_true',
    List.all_eq_false, not_exists, not_and, Classical.not_not] at h
  refine jet_eq_zero (strictMono_ratKnots hN hD) (fun τ hτ ↦ ?_) k x
  exact Term.inactive_of_inactiveB hN hD (by simpa using h τ hτ)

/-- The jets of orders `≤ M` of a mode at the left end of `[A/D, B/D]`, rounded down to `2 ^ -Q`. -/
def roundedJets (n M Q : ℕ) (N : ℕ → ℤ) (D : ℕ) (terms : List Term) (A B : ℤ) : Array ℤ :=
  Array.ofFn fun k : Fin (M + 1) ↦
    ⌊jet n (ratKnots N D) terms ((A : ℚ) / D) ((B : ℚ) / D) k ((A : ℚ) / D) * 2 ^ Q⌋

/-- The pair term `(ĉ X̂ Ŷ, |ĉ|(|X̂| + |Ŷ| + 1) + (|X̂| + 1)(|Ŷ| + 1))` of two rounded jets with the
coefficient `ĉ = ⌊c 2^Qc⌋`. -/
def pairTerm (Qc : ℕ) (coeff : ℕ → ℕ → ℚ) (k l : ℕ) (X Y : ℕ × Array ℤ) : ℤ × ℕ :=
  let c := ⌊coeff X.1 Y.1 * 2 ^ Qc⌋
  let x := X.2.getD k 0
  let y := Y.2.getD l 0
  (c * x * y, c.natAbs * (x.natAbs + y.natAbs + 1) + (x.natAbs + 1) * (y.natAbs + 1))

/-- The fixed-point corner derivative and its error, both in units of `2 ^ -(Qc + 2Q)`: the sums of
the pair terms over the active pairs. -/
def contractPairs (Qc : ℕ) (coeff : ℕ → ℕ → ℚ) (xs ys : List (ℕ × Array ℤ)) (k l : ℕ) :
    ℤ × ℕ :=
  xs.foldr (fun X acc ↦ ys.foldr (fun Y acc ↦
    let t := pairTerm Qc coeff k l X Y
    (acc.1 + t.1, acc.2 + t.2)) acc) (0, 0)

/-- The error of one product of rounded factors. -/
theorem abs_mul_mul_sub_le {c x y : ℝ} {C X Y : ℤ} (hc : (C : ℝ) ≤ c ∧ c < C + 1)
    (hx : (X : ℝ) ≤ x ∧ x < X + 1) (hy : (Y : ℝ) ≤ y ∧ y < Y + 1) :
    |c * x * y - C * X * Y| ≤
      (C.natAbs * (X.natAbs + Y.natAbs + 1) + (X.natAbs + 1) * (Y.natAbs + 1) : ℕ) := by
  set γ := c - C
  set ξ := x - X
  set η := y - Y
  have hγ : |γ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hc.1, hc.2]
  have hξ : |ξ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hη : |η| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  have e : c * x * y - C * X * Y = C * X * η + C * ξ * Y + C * ξ * η + γ * X * Y +
      γ * X * η + γ * ξ * Y + γ * ξ * η := by
    simp only [γ, ξ, η]; ring
  have hc' : |(C : ℝ)| = (C.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hx' : |(X : ℝ)| = (X.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hy' : |(Y : ℝ)| = (Y.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [e]
  push_cast
  have h0 : ∀ u v w : ℝ, |u * v * w| = |u| * |v| * |w| := fun u v w ↦ by
    rw [abs_mul, abs_mul]
  have hC := abs_nonneg (C : ℝ)
  have hX := abs_nonneg (X : ℝ)
  have hY := abs_nonneg (Y : ℝ)
  calc |C * X * η + C * ξ * Y + C * ξ * η + γ * X * Y + γ * X * η + γ * ξ * Y +
        γ * ξ * η| ≤ |(C : ℝ)| * |(X : ℝ)| * 1 + |(C : ℝ)| * 1 * |(Y : ℝ)| +
          |(C : ℝ)| * 1 * 1 + 1 * |(X : ℝ)| * |(Y : ℝ)| + 1 * |(X : ℝ)| * 1 +
          1 * 1 * |(Y : ℝ)| + 1 * 1 * 1 := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
            · refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
              · refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
                · refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
                  · rw [h0]; gcongr
                  · rw [h0]; gcongr
                · rw [h0]; gcongr
              · rw [h0]; gcongr
            · rw [h0]; gcongr
          · rw [h0]; gcongr
        · rw [h0]; gcongr
    _ = _ := by rw [hc', hx', hy']; ring

/-- Folding `acc ↦ acc + g a` over a list adds the sums of both components of `g` to `acc`. -/
private theorem foldr_pair {α : Type*} (l : List α) (g : α → ℤ × ℕ) (acc : ℤ × ℕ) :
    l.foldr (fun a acc ↦ (acc.1 + (g a).1, acc.2 + (g a).2)) acc =
      (acc.1 + (l.map fun a ↦ (g a).1).sum, acc.2 + (l.map fun a ↦ (g a).2).sum) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, ih]
    simp only [List.map_cons, List.sum_cons]
    ext <;> simp <;> ring

/-- The fixed-point contraction is the pair of double sums over `xs` and `ys` of the components of
`pairTerm`. -/
theorem contractPairs_eq (Qc : ℕ) (coeff : ℕ → ℕ → ℚ) (xs ys : List (ℕ × Array ℤ)) (k l : ℕ) :
    contractPairs Qc coeff xs ys k l =
      ((xs.map fun X ↦ (ys.map fun Y ↦ (pairTerm Qc coeff k l X Y).1).sum).sum,
        (xs.map fun X ↦ (ys.map fun Y ↦ (pairTerm Qc coeff k l X Y).2).sum).sum) := by
  unfold contractPairs
  have hinner : ∀ X acc, ys.foldr (fun Y acc ↦
      let t := pairTerm Qc coeff k l X Y
      (acc.1 + t.1, acc.2 + t.2)) acc =
      (acc.1 + (ys.map fun Y ↦ (pairTerm Qc coeff k l X Y).1).sum,
        acc.2 + (ys.map fun Y ↦ (pairTerm Qc coeff k l X Y).2).sum) := fun X acc ↦
    foldr_pair ys (pairTerm Qc coeff k l X) acc
  simp only [hinner]
  have h := foldr_pair xs (fun X ↦ ((ys.map fun Y ↦ (pairTerm Qc coeff k l X Y).1).sum,
    (ys.map fun Y ↦ (pairTerm Qc coeff k l X Y).2).sum)) (0, 0)
  simp only [zero_add] at h
  rw [← h]

/-- If each `f b` is within `e b / S` of `g b / S`, then the sum of `f` over the list is within
`(∑ e) / S` of `(∑ g) / S`. -/
theorem abs_list_sum_sub_le {β : Type*} (L : List β) (f : β → ℝ) (g : β → ℤ) (e : β → ℕ)
    {S : ℝ} (h : ∀ b ∈ L, |f b - (g b : ℝ) / S| ≤ (e b : ℝ) / S) :
    |(L.map f).sum - (((L.map g).sum : ℤ) : ℝ) / S| ≤ (((L.map e).sum : ℕ) : ℝ) / S := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Nat.cast_add, add_div]
    have h1 := h b (List.mem_cons_self ..)
    have h2 := ih fun b' hb' ↦ h b' (List.mem_cons_of_mem _ hb')
    calc |f b + (L.map f).sum - ((g b : ℝ) / S + (((L.map g).sum : ℤ) : ℝ) / S)| =
        |(f b - (g b : ℝ) / S) + ((L.map f).sum - (((L.map g).sum : ℤ) : ℝ) / S)| := by
          congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)

/-- **The fixed-point contraction is sound**: with every listed jet rounded down to `2 ^ -Q`
from the exact values `Xe`, `Ye`, the contraction differs from the exact sum of
`c Xe Ye` over the listed pairs by at most its error, in units of `2 ^ -(Qc + 2Q)`. -/
theorem contractPairs_sound (Qc Q : ℕ) (coeff : ℕ → ℕ → ℚ) (xs ys : List (ℕ × Array ℤ))
    (k l : ℕ) (Xe Ye : ℕ → ℝ)
    (hX : ∀ X ∈ xs, ((X.2.getD k 0 : ℤ) : ℝ) ≤ Xe X.1 * 2 ^ Q ∧
      Xe X.1 * 2 ^ Q < (X.2.getD k 0 : ℤ) + 1)
    (hY : ∀ Y ∈ ys, ((Y.2.getD l 0 : ℤ) : ℝ) ≤ Ye Y.1 * 2 ^ Q ∧
      Ye Y.1 * 2 ^ Q < (Y.2.getD l 0 : ℤ) + 1) :
    |(xs.map fun X ↦ (ys.map fun Y ↦ (coeff X.1 Y.1 : ℝ) * Xe X.1 * Ye Y.1).sum).sum -
        ((contractPairs Qc coeff xs ys k l).1 : ℝ) / 2 ^ (Qc + 2 * Q)| ≤
      ((contractPairs Qc coeff xs ys k l).2 : ℝ) / 2 ^ (Qc + 2 * Q) := by
  rw [contractPairs_eq]
  simp only
  have hS : (0 : ℝ) < 2 ^ (Qc + 2 * Q) := by positivity
  have hterm : ∀ X ∈ xs, ∀ Y ∈ ys,
      |(coeff X.1 Y.1 : ℝ) * Xe X.1 * Ye Y.1 - ((pairTerm Qc coeff k l X Y).1 : ℝ) /
        2 ^ (Qc + 2 * Q)| ≤ ((pairTerm Qc coeff k l X Y).2 : ℝ) / 2 ^ (Qc + 2 * Q) := by
    intro X hXm Y hYm
    have hc : ((⌊coeff X.1 Y.1 * 2 ^ Qc⌋ : ℤ) : ℝ) ≤ (coeff X.1 Y.1 : ℝ) * 2 ^ Qc ∧
        (coeff X.1 Y.1 : ℝ) * 2 ^ Qc < ⌊coeff X.1 Y.1 * 2 ^ Qc⌋ + 1 := by
      have h1 := Int.floor_le (coeff X.1 Y.1 * 2 ^ Qc)
      have h2 := Int.lt_floor_add_one (coeff X.1 Y.1 * 2 ^ Qc)
      have e1 : ((coeff X.1 Y.1 * 2 ^ Qc : ℚ) : ℝ) = (coeff X.1 Y.1 : ℝ) * 2 ^ Qc := by
        push_cast; rfl
      constructor
      · rw [← e1]; exact_mod_cast h1
      · rw [← e1]; exact_mod_cast h2
    have h := abs_mul_mul_sub_le hc (hX X hXm) (hY Y hYm)
    unfold pairTerm
    simp only
    have e : (coeff X.1 Y.1 : ℝ) * Xe X.1 * Ye Y.1 -
        ((⌊coeff X.1 Y.1 * 2 ^ Qc⌋ * X.2.getD k 0 * Y.2.getD l 0 : ℤ) : ℝ) / 2 ^ (Qc + 2 * Q) =
        ((coeff X.1 Y.1 : ℝ) * 2 ^ Qc * (Xe X.1 * 2 ^ Q) * (Ye Y.1 * 2 ^ Q) -
          ((⌊coeff X.1 Y.1 * 2 ^ Qc⌋ : ℤ) : ℝ) * ((X.2.getD k 0 : ℤ) : ℝ) *
            ((Y.2.getD l 0 : ℤ) : ℝ)) / 2 ^ (Qc + 2 * Q) := by
      push_cast
      rw [pow_add, show 2 * Q = Q + Q by ring, pow_add]
      field_simp
    rw [e, abs_div, abs_of_pos hS]
    exact div_le_div_of_nonneg_right h hS.le
  have hinner : ∀ X ∈ xs, |(ys.map fun Y ↦ (coeff X.1 Y.1 : ℝ) * Xe X.1 * Ye Y.1).sum -
      (((ys.map fun Y ↦ (pairTerm Qc coeff k l X Y).1).sum : ℤ) : ℝ) / 2 ^ (Qc + 2 * Q)| ≤
      (((ys.map fun Y ↦ (pairTerm Qc coeff k l X Y).2).sum : ℕ) : ℝ) / 2 ^ (Qc + 2 * Q) :=
    fun X hXm ↦ abs_list_sum_sub_le ys _ _ _ (hterm X hXm)
  exact abs_list_sum_sub_le xs _ _ _ hinner

/-! ### The corner derivatives from the active modes -/

/-- The sum of `f` over the elements of `[0, n)` that satisfy `p` is
`∑ i < n, if p i then f i else 0`. -/
theorem list_sum_filter_range (n : ℕ) (p : ℕ → Bool) (f : ℕ → ℝ) :
    (((List.range n).filter p).map f).sum = ∑ i ∈ range n, if p i then f i else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      sum_range_succ]
    cases h : p n <;> simp [h]

/-- The active modes of one level on an edge, with their rounded jets. -/
def levelJets (n M Q : ℕ) (N : ℕ → ℤ) (D : ℕ) (modes : ℕ → List Term) (count : ℕ) (A B : ℤ) :
    List (ℕ × Array ℤ) :=
  (activeModes n N modes count A B).map fun i ↦ (i, roundedJets n M Q N D (modes i) A B)

/-- Every entry of order `k ≤ M` of a listed jet array is the floor of `2 ^ Q` times the exact jet
of its mode at the left end of the cell. -/
theorem mem_levelJets {n M Q : ℕ} {N : ℕ → ℤ} {D : ℕ} {modes : ℕ → List Term} {count : ℕ}
    {A B : ℤ} {X : ℕ × Array ℤ} (h : X ∈ levelJets n M Q N D modes count A B) {k : ℕ}
    (hk : k ≤ M) :
    ((X.2.getD k 0 : ℤ) : ℝ) ≤
        (jet n (ratKnots N D) (modes X.1) ((A : ℚ) / D) ((B : ℚ) / D) k ((A : ℚ) / D) : ℝ) *
          2 ^ Q ∧
      (jet n (ratKnots N D) (modes X.1) ((A : ℚ) / D) ((B : ℚ) / D) k ((A : ℚ) / D) : ℝ) *
          2 ^ Q < (X.2.getD k 0 : ℤ) + 1 := by
  unfold levelJets at h
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
  simp only
  unfold roundedJets
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show k < M + 1 by omega, ↓reduceDIte, Option.getD_some]
  set q := jet n (ratKnots N D) (modes i) ((A : ℚ) / D) ((B : ℚ) / D) k ((A : ℚ) / D) * 2 ^ Q
  have e : ((q : ℚ) : ℝ) = (jet n (ratKnots N D) (modes i) ((A : ℚ) / D) ((B : ℚ) / D) k
      ((A : ℚ) / D) : ℝ) * 2 ^ Q := by simp [q]
  rw [← e]
  constructor
  · exact_mod_cast Int.floor_le q
  · exact_mod_cast Int.lt_floor_add_one q

/-- For `g i 0 = 0`, a sum of `g` over the active modes and their exact jets equals the sum over all
modes `i < count`, the inactive modes having zero jets. -/
theorem sum_levelJets_eq {n M Q : ℕ} {N : ℕ → ℤ} {D : ℕ} (hN : StrictMono N) (hD : 0 < D)
    {modes : ℕ → List Term} {count : ℕ} {A B : ℤ} {k : ℕ} (g : ℕ → ℝ → ℝ)
    (hg : ∀ i, g i 0 = 0) :
    ((levelJets n M Q N D modes count A B).map fun X ↦
        g X.1 (jet n (ratKnots N D) (modes X.1) ((A : ℚ) / D) ((B : ℚ) / D) k ((A : ℚ) / D))).sum =
      ∑ i ∈ range count,
        g i (jet n (ratKnots N D) (modes i) ((A : ℚ) / D) ((B : ℚ) / D) k ((A : ℚ) / D)) := by
  unfold levelJets activeModes
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [list_sum_filter_range]
  refine sum_congr rfl fun i hi ↦ ?_
  split_ifs with h
  · rfl
  · have hz := jet_eq_zero_of_not_mem_activeModes (n := n) (N := N) (D := D) (modes := modes)
      (count := count) (A := A) (B := B) hN hD (mem_range.mp hi) (by
        unfold activeModes; simp [mem_range.mp hi, h]) k ((A : ℚ) / D)
    rw [hz, Rat.cast_zero, hg]

/-- The active pairs of a level with their rounded jets and rounded coefficient `⌊c 2^Qc⌋`. -/
def pairList (Qc : ℕ) (coeff : ℕ → ℕ → ℚ) (xs ys : List (ℕ × Array ℤ)) :
    List (Array ℤ × Array ℤ × ℤ) :=
  xs.flatMap fun X ↦ ys.map fun Y ↦ (X.2, Y.2, ⌊coeff X.1 Y.1 * 2 ^ Qc⌋)

/-- The contraction of a pair list at the orders `(k, l)`. -/
def contractList (Ps : List (Array ℤ × Array ℤ × ℤ)) (k l : ℕ) : ℤ × ℕ :=
  Ps.foldr (fun t acc ↦
    let x := t.1.getD k 0
    let y := t.2.1.getD l 0
    let c := t.2.2
    (acc.1 + c * x * y,
      acc.2 + (c.natAbs * (x.natAbs + y.natAbs + 1) + (x.natAbs + 1) * (y.natAbs + 1)))) (0, 0)

/-- The sum of a `flatMap` is the sum of the sums of the pieces. -/
private theorem sum_flatMap' {α β : Type*} [AddCommMonoid β] (L : List α) (f : α → List β) :
    (L.flatMap f).sum = (L.map fun a ↦ (f a).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- Contracting the precomputed pair list gives the fixed-point contraction `contractPairs`. -/
theorem contractList_pairList (Qc : ℕ) (coeff : ℕ → ℕ → ℚ) (xs ys : List (ℕ × Array ℤ))
    (k l : ℕ) : contractList (pairList Qc coeff xs ys) k l = contractPairs Qc coeff xs ys k l := by
  rw [contractPairs_eq]
  unfold contractList pairList
  have h := foldr_pair (xs.flatMap fun X ↦ ys.map fun Y ↦ (X.2, Y.2, ⌊coeff X.1 Y.1 * 2 ^ Qc⌋))
    (fun t ↦ (t.2.2 * t.1.getD k 0 * t.2.1.getD l 0,
      t.2.2.natAbs * ((t.1.getD k 0).natAbs + (t.2.1.getD l 0).natAbs + 1) +
        ((t.1.getD k 0).natAbs + 1) * ((t.2.1.getD l 0).natAbs + 1))) (0, 0)
  simp only [zero_add] at h
  refine h.trans ?_
  simp only [List.map_flatMap, sum_flatMap', List.map_map, Function.comp_def]
  rfl

/-- The fixed-point corner derivative of a multilevel field from the jet lists `xs m`, `ys m` of
the levels, and its error, in units of `2 ^ -(Qc + 2Q)`. -/
def fixedCornerDeriv (L Qc : ℕ) (lv : ℕ → Level) (xs ys : ℕ → List (ℕ × Array ℤ))
    (k l : ℕ) : ℤ × ℕ :=
  ((List.range L).map fun m ↦ contractPairs Qc (lv m).coeff (xs m) (ys m) k l).foldr
    (fun t acc ↦ (acc.1 + t.1, acc.2 + t.2)) (0, 0)

/-- **The fixed-point corner derivatives are sound.** -/
theorem abs_cornerDeriv_sub_fixed_le {n L M Q Qc : ℕ} {lv : ℕ → Level} {Nx Ny : ℕ → ℕ → ℤ}
    {D : ℕ} (hD : 0 < D) (hNx : ∀ m < L, StrictMono (Nx m)) (hNy : ∀ m < L, StrictMono (Ny m))
    (hKx : ∀ m < L, (lv m).xKnots = ratKnots (Nx m) D)
    (hKy : ∀ m < L, (lv m).yKnots = ratKnots (Ny m) D) (A B C E : ℤ)
    {xs ys : ℕ → List (ℕ × Array ℤ)}
    (hxs : ∀ m < L, xs m = levelJets n M Q (Nx m) D (lv m).xModes (lv m).rows A B)
    (hys : ∀ m < L, ys m = levelJets n M Q (Ny m) D (lv m).yModes (lv m).cols C E) {k l : ℕ}
    (hk : k ≤ M) (hl : l ≤ M) :
    |(cornerDeriv n L lv ((A : ℚ) / D) ((B : ℚ) / D) ((C : ℚ) / D) ((E : ℚ) / D) k l : ℝ) -
        ((fixedCornerDeriv L Qc lv xs ys k l).1 : ℝ) / 2 ^ (Qc + 2 * Q)| ≤
      ((fixedCornerDeriv L Qc lv xs ys k l).2 : ℝ) / 2 ^ (Qc + 2 * Q) := by
  set S : ℝ := 2 ^ (Qc + 2 * Q)
  have hlevel : ∀ m ∈ range L,
      |(∑ i ∈ range (lv m).rows, ∑ j ∈ range (lv m).cols, ((lv m).coeff i j *
          jet n (lv m).xKnots ((lv m).xModes i) ((A : ℚ) / D) ((B : ℚ) / D) k ((A : ℚ) / D) *
          jet n (lv m).yKnots ((lv m).yModes j) ((C : ℚ) / D) ((E : ℚ) / D) l ((C : ℚ) / D) :
            ℝ)) -
        ((contractPairs Qc (lv m).coeff (xs m) (ys m) k l).1 : ℝ) / S| ≤
        ((contractPairs Qc (lv m).coeff (xs m) (ys m) k l).2 : ℝ) / S := by
    intro m hm
    have hm' := mem_range.mp hm
    rw [hKx m hm', hKy m hm', hxs m hm', hys m hm']
    have h := contractPairs_sound Qc Q (lv m).coeff
      (levelJets n M Q (Nx m) D (lv m).xModes (lv m).rows A B)
      (levelJets n M Q (Ny m) D (lv m).yModes (lv m).cols C E) k l
      (fun i ↦ (jet n (ratKnots (Nx m) D) ((lv m).xModes i) ((A : ℚ) / D) ((B : ℚ) / D) k
        ((A : ℚ) / D) : ℝ))
      (fun j ↦ (jet n (ratKnots (Ny m) D) ((lv m).yModes j) ((C : ℚ) / D) ((E : ℚ) / D) l
        ((C : ℚ) / D) : ℝ))
      (fun X hX ↦ mem_levelJets hX hk) (fun Y hY ↦ mem_levelJets hY hl)
    have e : (∑ i ∈ range (lv m).rows, ∑ j ∈ range (lv m).cols, ((lv m).coeff i j *
          jet n (ratKnots (Nx m) D) ((lv m).xModes i) ((A : ℚ) / D) ((B : ℚ) / D) k
            ((A : ℚ) / D) *
          jet n (ratKnots (Ny m) D) ((lv m).yModes j) ((C : ℚ) / D) ((E : ℚ) / D) l
            ((C : ℚ) / D) : ℝ)) =
        ((levelJets n M Q (Nx m) D (lv m).xModes (lv m).rows A B).map fun X ↦
          ((levelJets n M Q (Ny m) D (lv m).yModes (lv m).cols C E).map fun Y ↦
            ((lv m).coeff X.1 Y.1 : ℝ) *
              (jet n (ratKnots (Nx m) D) ((lv m).xModes X.1) ((A : ℚ) / D) ((B : ℚ) / D) k
                ((A : ℚ) / D) : ℝ) *
              (jet n (ratKnots (Ny m) D) ((lv m).yModes Y.1) ((C : ℚ) / D) ((E : ℚ) / D) l
                ((C : ℚ) / D) : ℝ)).sum).sum := by
      rw [sum_levelJets_eq (hNx m hm') hD (fun i x ↦ ((levelJets n M Q (Ny m) D (lv m).yModes
          (lv m).cols C E).map fun Y ↦ ((lv m).coeff i Y.1 : ℝ) * x *
            (jet n (ratKnots (Ny m) D) ((lv m).yModes Y.1) ((C : ℚ) / D) ((E : ℚ) / D) l
              ((C : ℚ) / D) : ℝ)).sum) (fun i ↦ by simp)]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [sum_levelJets_eq (hNy m hm') hD (fun j y ↦ ((lv m).coeff i j : ℝ) *
        (jet n (ratKnots (Nx m) D) ((lv m).xModes i) ((A : ℚ) / D) ((B : ℚ) / D) k
          ((A : ℚ) / D) : ℝ) * y) (fun j ↦ by simp)]
    rw [e]
    exact h
  unfold cornerDeriv fixedCornerDeriv
  have hf : ∀ (l' : List (ℤ × ℕ)), l'.foldr (fun t acc ↦ (acc.1 + t.1, acc.2 + t.2)) (0, 0) =
      ((l'.map fun t ↦ t.1).sum, (l'.map fun t ↦ t.2).sum) := by
    intro l'
    have := foldr_pair l' id (0, 0)
    simpa using this
  rw [hf]
  simp only [List.map_map, Function.comp_def]
  rw [Int.cast_list_sum, Nat.cast_list_sum, List.map_map, List.map_map]
  simp only [Function.comp_def]
  rw [SquareModel.list_sum_range, SquareModel.list_sum_range, Finset.sum_div, Finset.sum_div,
    Rat.cast_sum,
    ← Finset.sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm ↦ ?_)
  have h := hlevel m hm
  push_cast at h ⊢
  exact h

end CAS.Numerics.TensorSpline

namespace CAS.Numerics.TensorSpline

open Finset

/-- The fixed-point corner derivative from precomputed pair lists `Ps m` of the levels. -/
def fixedCornerDerivOfPairs (L : ℕ) (Ps : ℕ → List (Array ℤ × Array ℤ × ℤ)) (k l : ℕ) :
    ℤ × ℕ :=
  ((List.range L).map fun m ↦ contractList (Ps m) k l).foldr
    (fun t acc ↦ (acc.1 + t.1, acc.2 + t.2)) (0, 0)

/-- With pair lists equal to `pairList` on every level `m < L`, the corner derivative from the pair
lists is `fixedCornerDeriv`. -/
theorem fixedCornerDerivOfPairs_eq {L Qc : ℕ} {lv : ℕ → Level} {xs ys : ℕ → List (ℕ × Array ℤ)}
    {Ps : ℕ → List (Array ℤ × Array ℤ × ℤ)}
    (hP : ∀ m < L, Ps m = pairList Qc (lv m).coeff (xs m) (ys m)) (k l : ℕ) :
    fixedCornerDerivOfPairs L Ps k l = fixedCornerDeriv L Qc lv xs ys k l := by
  unfold fixedCornerDerivOfPairs fixedCornerDeriv
  congr 1
  refine List.map_congr_left fun m hm ↦ ?_
  rw [hP m (List.mem_range.mp hm), contractList_pairList]

end CAS.Numerics.TensorSpline

namespace CAS.Numerics.TensorSpline

open Finset _root_.Polynomial CAS.Splines Set

/-- The exact corner derivative `D_kl` vanishes when `k` or `l` exceeds the degree `n + 1` of the
cell pieces. -/
theorem cornerDeriv_eq_zero_of_lt {n L : ℕ} {lv : ℕ → Level} {a b c d : ℚ} {k l : ℕ}
    (h : n + 1 < k ∨ n + 1 < l) : cornerDeriv n L lv a b c d k l = 0 := by
  unfold cornerDeriv
  refine sum_eq_zero fun m _ ↦ sum_eq_zero fun i _ ↦ sum_eq_zero fun j _ ↦ ?_
  have hz : ∀ (K : ℕ → ℚ) (modes : List Term) (a b : ℚ) (k : ℕ), n + 1 < k →
      jet n K modes a b k a = 0 := by
    intro K modes a b k hk
    have h1 := polynomialJet_piece n K modes a b k a
    rw [polynomialJet_eq_zero_of_degree_lt (natDegree_piece_le n _ _ _ _) hk] at h1
    exact_mod_cast h1.symm
  rcases h with h | h
  · rw [hz _ _ _ _ _ h]; ring
  · rw [hz _ _ _ _ _ h]; ring

end CAS.Numerics.TensorSpline

namespace CAS.Numerics.SquareModel

open Finset Set

/-- The model of `∂ₓⁱ∂ᵧʲ F(a + h_x s, c + h_y t)` on the unit square from fixed-point corner
derivatives `Dt` of degree at most `N` in each variable (entry `(N + 1) k + l`, in units of
`2 ^ -S`, with its error): the coefficient of `s^k t^l` is `D_{i+k, j+l} h_xᵏ h_yˡ / (k! l!)`. -/
def ofCornerTable (P S N : ℕ) (Dt : Array (ℤ × ℕ)) (hx hy : ℚ) (i j : ℕ) : SquareModel :=
  let idx := (List.range (N + 1 - i)).flatMap fun k ↦ (List.range (N + 1 - j)).map fun l ↦ (k, l)
  let w (k l : ℕ) : ℚ := hx ^ k * hy ^ l / (k.factorial * l.factorial) * 2 ^ P / 2 ^ S
  { terms := idx.map fun kl ↦
      (kl.1, kl.2, ⌊((Dt.getD ((N + 1) * (i + kl.1) + (j + kl.2)) (0, 0)).1 : ℚ) * w kl.1 kl.2⌋)
    rad := (idx.map fun kl ↦
      ceilNat (((Dt.getD ((N + 1) * (i + kl.1) + (j + kl.2)) (0, 0)).2 : ℚ) *
        w kl.1 kl.2) + 1).sum }

/-- A sum of `f` over the flattened list of pairs `(k, l)`, `k < a`, `l < b`, is the double sum
`∑ k < a, ∑ l < b, f (k, l)`. -/
private theorem list_sum_flatMap_range (a b : ℕ) (f : ℕ × ℕ → ℝ) :
    ((((List.range a).flatMap fun k ↦ (List.range b).map fun l ↦ (k, l)).map f).sum) =
      ∑ k ∈ range a, ∑ l ∈ range b, f (k, l) := by
  rw [List.map_flatMap]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ, List.flatMap_append, List.sum_append, ih, sum_range_succ]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map,
      Function.comp_def]
    rw [list_sum_range]

/-- **The corner-table model encloses the expansion** of a function in the corner derivatives,
when the table approximates them within its errors. -/
theorem ofCornerTable_encloses {P S N : ℕ} {Dt : Array (ℤ × ℕ)} {hx hy : ℚ} (hhx : 0 ≤ hx)
    (hhy : 0 ≤ hy) {i j : ℕ} {D : ℕ → ℕ → ℝ}
    (hD : ∀ k l, k ≤ N → l ≤ N → |D k l - ((Dt.getD ((N + 1) * k + l) (0, 0)).1 : ℝ) / 2 ^ S| ≤
      ((Dt.getD ((N + 1) * k + l) (0, 0)).2 : ℝ) / 2 ^ S)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, f s t =
      ∑ k ∈ range (N + 1 - i), ∑ l ∈ range (N + 1 - j),
        D (i + k) (j + l) / (k.factorial * l.factorial) * ((hx : ℝ) * s) ^ k * ((hy : ℝ) * t) ^ l) :
    (ofCornerTable P S N Dt hx hy i j).Encloses P f := by
  intro s hs t ht
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hS : (0 : ℝ) < 2 ^ S := by positivity
  set w : ℕ → ℕ → ℚ := fun k l ↦ hx ^ k * hy ^ l / (k.factorial * l.factorial) * 2 ^ P / 2 ^ S
  set E : ℕ → ℕ → ℤ × ℕ := fun k l ↦ Dt.getD ((N + 1) * (i + k) + (j + l)) (0, 0)
  have hw : ∀ k l, (0 : ℝ) ≤ (w k l : ℝ) := fun k l ↦ by
    simp only [w]; push_cast; positivity
  have hmid : (ofCornerTable P S N Dt hx hy i j).midEval s t = ∑ k ∈ range (N + 1 - i),
      ∑ l ∈ range (N + 1 - j), ((⌊((E k l).1 : ℚ) * w k l⌋ : ℤ) : ℝ) * s ^ k * t ^ l := by
    unfold midEval ofCornerTable listEval
    simp only [List.map_map, Function.comp_def]
    rw [list_sum_flatMap_range]
    rfl
  have hrad : ((ofCornerTable P S N Dt hx hy i j).rad : ℝ) = ∑ k ∈ range (N + 1 - i),
      ∑ l ∈ range (N + 1 - j), ((ceilNat (((E k l).2 : ℚ) * w k l) + 1 : ℕ) : ℝ) := by
    unfold ofCornerTable
    simp only
    rw [Nat.cast_list_sum, List.map_map]
    simp only [Function.comp_def]
    rw [list_sum_flatMap_range]
  rw [hmid, hrad, hf s hs t ht, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk ↦ ?_)
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l hl ↦ ?_)
  have hsk : 0 ≤ s ^ k := pow_nonneg hs.1 _
  have htl : 0 ≤ t ^ l := pow_nonneg ht.1 _
  have hsk1 : s ^ k ≤ 1 := pow_le_one₀ hs.1 hs.2
  have htl1 : t ^ l ≤ 1 := pow_le_one₀ ht.1 ht.2
  have hfl1 := Int.floor_le (((E k l).1 : ℚ) * w k l)
  have hfl2 := Int.lt_floor_add_one (((E k l).1 : ℚ) * w k l)
  have hce := le_ceilNat (((E k l).2 : ℚ) * w k l)
  have hDk := hD (i + k) (j + l) (by have := mem_range.mp hk; omega)
    (by have := mem_range.mp hl; omega)
  have hwk : (w k l : ℝ) = (hx : ℝ) ^ k * (hy : ℝ) ^ l / (k.factorial * l.factorial) *
      2 ^ P / 2 ^ S := by simp only [w]; push_cast; ring
  set c : ℝ := (hx : ℝ) ^ k * (hy : ℝ) ^ l / (k.factorial * l.factorial)
  have hc : 0 ≤ c := by positivity
  have hwk' : (w k l : ℝ) = c * 2 ^ P / 2 ^ S := hwk
  set e1 : ℝ := ((E k l).1 : ℝ)
  set e2 : ℝ := ((E k l).2 : ℝ)
  set Fl : ℝ := ((⌊((E k l).1 : ℚ) * w k l⌋ : ℤ) : ℝ)
  have hFl1 : Fl ≤ e1 * (w k l : ℝ) := by
    have : ((⌊((E k l).1 : ℚ) * w k l⌋ : ℤ) : ℝ) ≤ (((E k l).1 * w k l : ℚ) : ℝ) := by
      exact_mod_cast hfl1
    simpa [Fl, e1] using this
  have hFl2 : e1 * (w k l : ℝ) < Fl + 1 := by
    have : (((E k l).1 * w k l : ℚ) : ℝ) < ((⌊((E k l).1 : ℚ) * w k l⌋ : ℤ) : ℝ) + 1 := by
      exact_mod_cast hfl2
    simpa [Fl, e1] using this
  have hce' : e2 * (w k l : ℝ) ≤ (ceilNat (((E k l).2 : ℚ) * w k l) : ℝ) := by
    simpa [e2] using hce
  -- the term identity
  have e : D (i + k) (j + l) / (k.factorial * l.factorial) * ((hx : ℝ) * s) ^ k *
        ((hy : ℝ) * t) ^ l - Fl * s ^ k * t ^ l / 2 ^ P =
      (c * (D (i + k) (j + l) - e1 / 2 ^ S) + (e1 * (w k l : ℝ) - Fl) / 2 ^ P) *
        (s ^ k * t ^ l) := by
    rw [hwk']
    simp only [c]
    field_simp
    ring
  rw [e, abs_mul, abs_of_nonneg (mul_nonneg hsk htl)]
  have hb : |c * (D (i + k) (j + l) - e1 / 2 ^ S) + (e1 * (w k l : ℝ) - Fl) / 2 ^ P| ≤
      ((ceilNat (((E k l).2 : ℚ) * w k l) + 1 : ℕ) : ℝ) / 2 ^ P := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hc, abs_div, abs_of_pos hP, Nat.cast_add, Nat.cast_one, add_div]
    refine add_le_add ?_ ?_
    · have h1 : c * |D (i + k) (j + l) - e1 / 2 ^ S| ≤ c * (e2 / 2 ^ S) :=
        mul_le_mul_of_nonneg_left hDk hc
      have h2 : c * (e2 / 2 ^ S) = e2 * (w k l : ℝ) / 2 ^ P := by
        rw [hwk']; field_simp
      rw [h2] at h1
      exact h1.trans (div_le_div_of_nonneg_right hce' hP.le)
    · refine div_le_div_of_nonneg_right ?_ hP.le
      rw [abs_le]; constructor <;> linarith
  calc |c * (D (i + k) (j + l) - e1 / 2 ^ S) + (e1 * (w k l : ℝ) - Fl) / 2 ^ P| * (s ^ k * t ^ l)
      ≤ ((ceilNat (((E k l).2 : ℚ) * w k l) + 1 : ℕ) : ℝ) / 2 ^ P * 1 :=
        mul_le_mul hb ((mul_le_mul hsk1 htl1 htl zero_le_one).trans (by norm_num))
          (mul_nonneg hsk htl) (by positivity)
    _ = _ := mul_one _

end CAS.Numerics.SquareModel

namespace CAS.Numerics.TensorSpline

open Finset Set

/-- **The cell model of a multilevel field**: with a corner table approximating the exact corner
derivatives within its errors, `SquareModel.ofCornerTable` encloses
`(s, t) ↦ ∂ₓⁱ∂ᵧʲ F(a + (b - a) s, c + (d - c) t)` for `i, j ≤ n`. -/
theorem field_ofCornerTable_encloses {n L P S : ℕ} {lv : ℕ → Level} {a b c d : ℚ} (hab : a < b)
    (hcd : c < d)
    (hx : ∀ m < L, ∀ i < (lv m).rows, ∀ τ ∈ (lv m).xModes i,
      τ.Separated n (lv m).xKnots (a : ℝ) (b : ℝ))
    (hy : ∀ m < L, ∀ j < (lv m).cols, ∀ τ ∈ (lv m).yModes j,
      τ.Separated n (lv m).yKnots (c : ℝ) (d : ℝ))
    {Dt : Array (ℤ × ℕ)}
    (hD : ∀ k l, k ≤ n + 1 → l ≤ n + 1 →
      |(cornerDeriv n L lv a b c d k l : ℝ) -
          ((Dt.getD ((n + 2) * k + l) (0, 0)).1 : ℝ) / 2 ^ S| ≤
        ((Dt.getD ((n + 2) * k + l) (0, 0)).2 : ℝ) / 2 ^ S)
    {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    (SquareModel.ofCornerTable P S (n + 1) Dt (b - a) (d - c) i j).Encloses P
      (fun s t ↦
        mixedDeriv i j (field n L lv (fun _ ↦ 1)) (a + (b - a) * s) (c + (d - c) * t)) := by
  have hba : (0 : ℚ) ≤ b - a := by linarith
  have hdc : (0 : ℚ) ≤ d - c := by linarith
  refine SquareModel.ofCornerTable_encloses hba hdc
    (D := fun k l ↦ (cornerDeriv n L lv a b c d k l : ℝ)) hD ?_
  intro s hs t ht
  have hδ : (0 : ℝ) ≤ ((b - a : ℚ) : ℝ) * s := mul_nonneg (by exact_mod_cast hba) hs.1
  have hε : (0 : ℝ) ≤ ((d - c : ℚ) : ℝ) * t := mul_nonneg (by exact_mod_cast hdc) ht.1
  have hδb : (a : ℝ) + ((b - a : ℚ) : ℝ) * s ≤ b := by
    push_cast; nlinarith [hs.2, (by exact_mod_cast hba : (0 : ℝ) ≤ (b : ℝ) - a)]
  have hεd : (c : ℝ) + ((d - c : ℚ) : ℝ) * t ≤ d := by
    push_cast; nlinarith [ht.2, (by exact_mod_cast hdc : (0 : ℝ) ≤ (d : ℝ) - c)]
  have h := mixedDeriv_field_eq_corner hab hcd hx hy hi hj hδ hδb hε hεd
  push_cast at h ⊢
  rw [h]
  have hsplit : ∀ (u : ℕ) (hu : u ≤ n) (F : ℕ → ℝ), (∀ k, n + 1 < u + k → F k = 0) →
      ∑ k ∈ range (n + 2), F k = ∑ k ∈ range (n + 1 + 1 - u), F k := by
    intro u hu F hF
    rw [range_eq_Ico, range_eq_Ico, ← sum_Ico_consecutive F (Nat.zero_le (n + 1 + 1 - u))
      (show n + 1 + 1 - u ≤ n + 2 by omega)]
    rw [sum_eq_zero (s := Ico (n + 1 + 1 - u) (n + 2)) (fun k hk ↦ hF k (by
      have := (mem_Ico.mp hk).1; omega)), add_zero]
  rw [hsplit i hi _ (fun k hk ↦ by
    refine sum_eq_zero fun l _ ↦ ?_
    rw [cornerDeriv_eq_zero_of_lt (Or.inl hk)]; simp)]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [hsplit j hj _ (fun l hl ↦ by rw [cornerDeriv_eq_zero_of_lt (Or.inr hl)]; simp)]

end CAS.Numerics.TensorSpline
