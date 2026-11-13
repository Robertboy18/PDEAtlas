/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.TensorSplineNodes.Jets
public import CAS.Numerics.TensorSplineNodes.Rows

/-!
# Corner derivatives of a multilevel tensor B-spline field

A multilevel tensor field is `f(x, y) = w(y) ∑_m ∑_{i,j} a_m(i, j) X_{m,i}(x) Y_{m,j}(y)`, a sum
over mesh levels `m` of tensor products of modified B-spline modes (`TensorSpline.mode`), with a
weight `w` in the second variable, as the profile representation of Chen and Hou, Part II,
(C.4)-(C.12): three nested levels, odd tangential modes, extrapolated normal modes, and for the
stream function the weight `ρ_p(y) = arctan(1 + y) - arctan 1`. Its cell function on
`Q = [a, b] × [c, d]` (`cellField`) replaces every mode by its cell piece. The cell function is
smooth, equals the field on `Q` when no knot of any level lies inside the cell, and its
derivatives of order at most `n` in each variable equal the field's on all of `Q`
(`mixedDeriv_field_eq`); at order `n + 1` it supplies the one-sided derivatives that the cell
recursion needs.

The node engine evaluates `(b - a)ᵏ (d - c)ˡ ∂ₓᵏ ∂ᵧˡ` of the cell function at the corners with
packed natural-number arithmetic in two stages. For each level the first stage contracts the
coefficient columns of the normal modes active on the row of cells with the scaled normal jets
(one packed row over the tangential index), the second stage combines the active tangential
mode tables with the slots of the first stage (one packed row over the slots of a block of
cells), and `mergeRows` adds the levels. `abs_signedSlot_mergeRows_sub_le` is the soundness
theorem: every slot is within the stated integer error of `2 ^ (pa + pr + pt)` times the scaled
exact corner derivative, given that the inputs are the floors of their scaled exact values, that
the modes outside the windows are inactive on the cells, and that all entries fit their slots.

## Main definitions

* `mixedDeriv`: the mixed derivative `∂ₓᵏ ∂ᵧˡ F` at `(x, y)`.
* `Level`: one mesh level, with knot sequences, modes and the coefficient tensor.
* `field`: the multilevel field `w(y) ∑_{m < L} ∑_{i, j} a_m(i, j) X_{m,i}(x) Y_{m,j}(y)`.
* `cellField`: the cell function of the field on `[a, b] × [c, d]`.
* `weightedJet`: the scaled jet `(d - c)ˡ ∂ᵧˡ (w Y)` of a weighted normal piece at an end.

## Main results

* `mixedDeriv_tensor`: the mixed derivatives of a multilevel tensor sum are the sums of the
  coefficients times the products of the derivatives of the factors.
* `mixedDeriv_cellField`: the scaled mixed derivative of the cell function at a corner is the sum
  of the coefficients times the scaled corner jets and the weighted jets.
* `mixedDeriv_field_eq`: when no knot lies inside the cell, the mixed derivatives of order at
  most `n` in each variable of the field and of its cell function agree on the closed cell.
* `weightedJet_one`: with the weight `1` the weighted jet is the scaled corner jet.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, (C.4)-(C.12).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace CAS.Numerics.TensorSpline

open Finset _root_.Polynomial CAS.Splines

/-- The mixed derivative `∂ₓᵏ ∂ᵧˡ F` at `(x, y)`. -/
noncomputable def mixedDeriv (k l : ℕ) (F : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iteratedDeriv k (fun x' ↦ iteratedDeriv l (F x') y) x

/-- For `Cˡ` factors `h m j`, the `l`-th derivative in `y` of `∑ₘ ∑ᵢⱼ αₘᵢⱼ gₘᵢ(x) hₘⱼ(y)` is
`∑ₘ ∑ᵢⱼ αₘᵢⱼ gₘᵢ(x) hₘⱼ⁽ˡ⁾(y)`. -/
theorem iteratedDeriv_tensor_snd {L : ℕ} {I J : ℕ → ℕ} (α : ℕ → ℕ → ℕ → ℝ)
    (g h : ℕ → ℕ → ℝ → ℝ) {l : ℕ} (hh : ∀ m j, ContDiff ℝ l (h m j)) (x y : ℝ) :
    iteratedDeriv l (fun y ↦ ∑ m ∈ range L, ∑ i ∈ range (I m), ∑ j ∈ range (J m),
        α m i j * g m i x * h m j y) y =
      ∑ m ∈ range L, ∑ i ∈ range (I m), ∑ j ∈ range (J m),
        α m i j * g m i x * iteratedDeriv l (h m j) y := by
  have hj : ∀ m i j, ContDiff ℝ l (fun y ↦ α m i j * g m i x * h m j y) :=
    fun m i j ↦ contDiff_const.mul (hh m j)
  have hi : ∀ m i, ContDiff ℝ l (fun y ↦ ∑ j ∈ range (J m), α m i j * g m i x * h m j y) :=
    fun m i ↦ ContDiff.sum fun j _ ↦ hj m i j
  have hm : ∀ m, ContDiff ℝ l
      (fun y ↦ ∑ i ∈ range (I m), ∑ j ∈ range (J m), α m i j * g m i x * h m j y) :=
    fun m ↦ ContDiff.sum fun i _ ↦ hi m i
  rw [iteratedDeriv_fun_sum fun m _ ↦ (hm m).contDiffAt]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [iteratedDeriv_fun_sum fun i _ ↦ (hi m i).contDiffAt]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [iteratedDeriv_fun_sum fun j _ ↦ (hj m i j).contDiffAt]
  exact sum_congr rfl fun j _ ↦ iteratedDeriv_const_mul_field (α m i j * g m i x) (h m j)

/-- The mixed derivatives of a multilevel tensor sum are the sums of the products of the
derivatives of the factors. -/
theorem mixedDeriv_tensor {L : ℕ} {I J : ℕ → ℕ} (α : ℕ → ℕ → ℕ → ℝ) (g h : ℕ → ℕ → ℝ → ℝ)
    {k l : ℕ} (hg : ∀ m i, ContDiff ℝ k (g m i)) (hh : ∀ m j, ContDiff ℝ l (h m j)) (x y : ℝ) :
    mixedDeriv k l (fun x y ↦ ∑ m ∈ range L, ∑ i ∈ range (I m), ∑ j ∈ range (J m),
        α m i j * g m i x * h m j y) x y =
      ∑ m ∈ range L, ∑ i ∈ range (I m), ∑ j ∈ range (J m),
        α m i j * iteratedDeriv k (g m i) x * iteratedDeriv l (h m j) y := by
  unfold mixedDeriv
  simp_rw [iteratedDeriv_tensor_snd α g h hh]
  have hj : ∀ m i j, ContDiff ℝ k (fun x ↦ α m i j * g m i x * iteratedDeriv l (h m j) y) :=
    fun m i j ↦ (contDiff_const.mul (hg m i)).mul contDiff_const
  have hi : ∀ m i, ContDiff ℝ k
      (fun x ↦ ∑ j ∈ range (J m), α m i j * g m i x * iteratedDeriv l (h m j) y) :=
    fun m i ↦ ContDiff.sum fun j _ ↦ hj m i j
  have hm : ∀ m, ContDiff ℝ k (fun x ↦ ∑ i ∈ range (I m), ∑ j ∈ range (J m),
      α m i j * g m i x * iteratedDeriv l (h m j) y) :=
    fun m ↦ ContDiff.sum fun i _ ↦ hi m i
  rw [iteratedDeriv_fun_sum fun m _ ↦ (hm m).contDiffAt]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [iteratedDeriv_fun_sum fun i _ ↦ (hi m i).contDiffAt]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [iteratedDeriv_fun_sum fun j _ ↦ (hj m i j).contDiffAt]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [iteratedDeriv_mul_const_field (fun x ↦ α m i j * g m i x), iteratedDeriv_const_mul_field]

/-! ### Multilevel fields -/

/-- One mesh level of a tensor B-spline representation: knot sequences and modes in both
variables, the numbers of modes, and the coefficient tensor. -/
structure Level where
  /-- The knots of the first variable. -/
  xKnots : ℕ → ℚ
  /-- The knots of the second variable. -/
  yKnots : ℕ → ℚ
  /-- The modes of the first variable. -/
  xModes : ℕ → List Term
  /-- The modes of the second variable. -/
  yModes : ℕ → List Term
  /-- The number of modes of the first variable. -/
  rows : ℕ
  /-- The number of modes of the second variable. -/
  cols : ℕ
  /-- The coefficient of the product of mode `i` of the first and mode `j` of the second
  variable. -/
  coeff : ℕ → ℕ → ℚ

/-- The field `w(y) ∑_{m < L} ∑_{i, j} a_m(i, j) X_{m,i}(x) Y_{m,j}(y)` of order `n + 2`. -/
noncomputable def field (n L : ℕ) (lv : ℕ → Level) (wt : ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∑ m ∈ range L, ∑ i ∈ range (lv m).rows, ∑ j ∈ range (lv m).cols,
    ((lv m).coeff i j : ℝ) * mode n (lv m).xKnots ((lv m).xModes i) x *
      (wt y * mode n (lv m).yKnots ((lv m).yModes j) y)

/-- The cell function of the field on `[a, b] × [c, d]`: every mode replaced by its cell
piece. -/
noncomputable def cellField (n L : ℕ) (lv : ℕ → Level) (wt : ℝ → ℝ) (a b c d : ℝ) (x y : ℝ) :
    ℝ :=
  ∑ m ∈ range L, ∑ i ∈ range (lv m).rows, ∑ j ∈ range (lv m).cols,
    ((lv m).coeff i j : ℝ) * (piece n (lv m).xKnots ((lv m).xModes i) a b).eval x *
      (wt y * (piece n (lv m).yKnots ((lv m).yModes j) c d).eval y)

/-- The scaled jet `(d - c)ˡ ∂ᵧˡ (w Y)` of a weighted normal piece at an end of `[c, d]`. -/
noncomputable def weightedJet (n : ℕ) (K : ℕ → ℚ) (terms : List Term) (wt : ℝ → ℝ) (c d : ℚ)
    (l : ℕ) (f : Bool) : ℝ :=
  ((d : ℝ) - c) ^ l * iteratedDeriv l (fun y ↦ wt y * (piece n K terms c d).eval y)
    (if f then (d : ℝ) else c)

/-- With the constant weight `1` the weighted jet is the scaled corner jet. -/
theorem weightedJet_one (n : ℕ) (K : ℕ → ℚ) (terms : List Term) (c d : ℚ) (l : ℕ) (f : Bool) :
    weightedJet n K terms (fun _ ↦ 1) c d l f = (cornerJet n K terms c d l f : ℝ) := by
  unfold weightedJet cornerJet
  simp only [one_mul]
  rw [iteratedDeriv_eval_eq_polynomialJet]
  cases f <;> simp [polynomialJet_piece]

/-- **Corner derivatives of the cell function.** The scaled mixed derivative at a corner is
the sum over the levels and modes of the coefficients times the scaled corner jets. -/
theorem mixedDeriv_cellField (n L : ℕ) (lv : ℕ → Level) {wt : ℝ → ℝ} {l : ℕ}
    (hwt : ContDiff ℝ l wt) (a b c d : ℚ) (k : ℕ) (e f : Bool) :
    ((b : ℝ) - a) ^ k * ((d : ℝ) - c) ^ l * mixedDeriv k l
        (cellField n L lv wt a b c d) (if e then (b : ℝ) else a) (if f then (d : ℝ) else c) =
      ∑ m ∈ range L, ∑ i ∈ range (lv m).rows, ∑ j ∈ range (lv m).cols,
        ((lv m).coeff i j : ℝ) * (cornerJet n (lv m).xKnots ((lv m).xModes i) a b k e : ℝ) *
          weightedJet n (lv m).yKnots ((lv m).yModes j) wt c d l f := by
  have h := mixedDeriv_tensor (L := L) (I := fun m ↦ (lv m).rows) (J := fun m ↦ (lv m).cols)
    (fun m i j ↦ ((lv m).coeff i j : ℝ))
    (fun m i x ↦ (piece n (lv m).xKnots ((lv m).xModes i) a b).eval x)
    (fun m j y ↦ wt y * (piece n (lv m).yKnots ((lv m).yModes j) c d).eval y)
    (k := k) (l := l) (fun m i ↦ PDE.Analysis.contDiff_polynomial_eval _)
    (fun m j ↦ hwt.mul (PDE.Analysis.contDiff_polynomial_eval _))
    (if e then (b : ℝ) else a) (if f then (d : ℝ) else c)
  unfold cellField
  rw [h, mul_sum]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  unfold weightedJet cornerJet
  rw [iteratedDeriv_eval_eq_polynomialJet]
  have hx : polynomialJet k (piece n (lv m).xKnots ((lv m).xModes i) (a : ℝ) b)
      (if e then (b : ℝ) else a) =
      (jet n (lv m).xKnots ((lv m).xModes i) a b k (if e then b else a) : ℝ) := by
    cases e <;> simp [polynomialJet_piece]
  rw [hx]
  push_cast
  ring

/-- **The field on a cell.** When no knot of any term of any mode lies inside the cell, the
mixed derivatives of order at most `n` in each variable of the field and of its cell function
agree on the closed cell. -/
theorem mixedDeriv_field_eq {n L : ℕ} {lv : ℕ → Level} {wt : ℝ → ℝ} (hwt : ContDiff ℝ n wt)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hx : ∀ m < L, ∀ i < (lv m).rows, ∀ τ ∈ (lv m).xModes i, τ.Separated n (lv m).xKnots a b)
    (hy : ∀ m < L, ∀ j < (lv m).cols, ∀ τ ∈ (lv m).yModes j, τ.Separated n (lv m).yKnots c d)
    {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n) {x y : ℝ} (hxQ : x ∈ Set.Icc a b)
    (hyQ : y ∈ Set.Icc c d) :
    mixedDeriv k l (field n L lv wt) x y = mixedDeriv k l (cellField n L lv wt a b c d) x y := by
  have hwl : ContDiff ℝ l wt := hwt.of_le (by exact_mod_cast hl)
  have h₁ := mixedDeriv_tensor (L := L) (I := fun m ↦ (lv m).rows) (J := fun m ↦ (lv m).cols)
    (fun m i j ↦ ((lv m).coeff i j : ℝ))
    (fun m i x ↦ mode n (lv m).xKnots ((lv m).xModes i) x)
    (fun m j y ↦ wt y * mode n (lv m).yKnots ((lv m).yModes j) y) (k := k) (l := l)
    (fun m i ↦ (contDiff_mode n _ _).of_le (by exact_mod_cast hk))
    (fun m j ↦ hwl.mul ((contDiff_mode n _ _).of_le (by exact_mod_cast hl))) x y
  have h₂ := mixedDeriv_tensor (L := L) (I := fun m ↦ (lv m).rows) (J := fun m ↦ (lv m).cols)
    (fun m i j ↦ ((lv m).coeff i j : ℝ))
    (fun m i x ↦ (piece n (lv m).xKnots ((lv m).xModes i) a b).eval x)
    (fun m j y ↦ wt y * (piece n (lv m).yKnots ((lv m).yModes j) c d).eval y) (k := k) (l := l)
    (fun m i ↦ PDE.Analysis.contDiff_polynomial_eval _)
    (fun m j ↦ hwl.mul (PDE.Analysis.contDiff_polynomial_eval _)) x y
  unfold field cellField
  rw [h₁, h₂]
  refine sum_congr rfl fun m hm ↦ sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
  have hm' := mem_range.mp hm
  rw [iteratedDeriv_mode_eq hab (hx m hm' i (mem_range.mp hi)) hk hxQ,
    ← iteratedDeriv_eval_eq_polynomialJet]
  congr 1
  have heq : Set.EqOn (fun y ↦ wt y * mode n (lv m).yKnots ((lv m).yModes j) y)
      (fun y ↦ wt y * (piece n (lv m).yKnots ((lv m).yModes j) c d).eval y) (Set.Icc c d) :=
    fun z hz ↦ by
      simp only
      rw [piece_eval (hy m hm' j (mem_range.mp hj)) hz]
  exact PDE.Analysis.iteratedDeriv_eqOn_Icc hcd
    (hwt.mul (contDiff_mode n _ _)) (hwt.mul (PDE.Analysis.contDiff_polynomial_eval _))
    heq hl hyQ

end CAS.Numerics.TensorSpline
