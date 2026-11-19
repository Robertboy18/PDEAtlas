/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.TensorSplineNodes.Field
public import PDE.Analysis.Approximation.CellBounds
public import CAS.Numerics.BinaryGridNatural

/-!
# Cell enclosures of a tensor B-spline field from its corner values

On a cell `Q = [a, b] × [c, d]` the unweighted cell function of a multilevel tensor field is a
polynomial of degree at most `n + 1` in each variable, so its scaled derivatives
`G_kl = (b - a)ᵏ (d - c)ˡ ∂ₓᵏ ∂ᵧˡ P` vanish for `k > n + 1` or `l > n + 1`, and each `G_kl`
satisfies the second-order estimate of Chen and Hou, Part II, (C.13) in two dimensions,
`|G_kl - c₀| ≤ max_corners |G_kl - c₀| + (sup_Q |G_{k+2,l}| + sup_Q |G_{k,l+2}|) / 8` for every
constant `c₀` (`abs_scaledCellDeriv_sub_le`). With the constant shift the estimate encloses
`G_kl` between the smallest and the largest corner value, widened by the same term.

`CellCorners` holds integer approximations of `σ G_kl` at the four corners with their errors,
as the node engine produces them. `CellCorners.bound` solves the recursion of Part II, (C.14),
`A_kl = B_kl + ⌈(A_{k+2,l} + A_{k,l+2}) / 8⌉` from the corner bounds `B_kl`, exactly in
integers, and `CellCorners.lower`, `CellCorners.upper` are the widened corner extremes.
`CellCorners.mem_Icc_of_corners` proves that they enclose `σ G_kl` on the whole cell, for any
family of functions with the one-step estimate and vanishing beyond the top order.

## Main definitions

* `scaledCellDeriv`: the scaled derivative `σ (b - a)ᵏ (d - c)ˡ ∂ₓᵏ ∂ᵧˡ P` of the cell function.
* `CellCorners`: integer corner approximations of the scaled derivatives with their errors.
* `CellCorners.bound`: the solution of `A_kl = B_kl + ⌈(A_{k+2,l} + A_{k,l+2}) / 8⌉`.
* `CellCorners.lower`, `CellCorners.upper`: the widened corner extremes.

## Main results

* `natDegree_piece_le`: the cell piece of a mode has degree at most `n + 1`.
* `mixedDeriv_cellField_eq_zero`: beyond order `n + 1` in either variable the derivatives of the
  cell function vanish.
* `abs_scaledCellDeriv_sub_le`: `|G_kl - c₀| ≤ B + M₁ / 8 + M₂ / 8` on the cell when
  `|G_kl - c₀| ≤ B` at the corners and `M₁`, `M₂` bound `G_{k+2,l}`, `G_{k,l+2}`.
* `mem_Icc_of_corner_step`: corner values in `[lo, hi]` give `f ∈ [lo, hi]` on the rectangle,
  widened by `(M₁ (b - a)² + M₂ (d - c)²) / 8`.
* `CellCorners.abs_le_bound`: `|G_kl| ≤ bound N k l` on the cell.
* `CellCorners.mem_Icc_of_corners`: `lower N k l ≤ G_kl ≤ upper N k l` on the whole cell.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, (C.13)-(C.14).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace CAS.Numerics.TensorSpline

open Finset _root_.Polynomial Set CAS.Splines

/-! ### The unweighted cell function as a polynomial tensor -/

/-- The cell piece of a mode has degree at most `n + 1`. -/
theorem natDegree_piece_le (n : ℕ) (K : ℕ → ℚ) (terms : List Term) (a b : ℝ) :
    (piece n K terms a b).natDegree ≤ n + 1 := by
  unfold piece
  induction terms with
  | nil => simp
  | cons τ terms ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (natDegree_add_le _ _).trans (max_le ?_ ih)
    unfold Term.piece
    refine (natDegree_C_mul_le _ _).trans ?_
    split_ifs
    · refine natDegree_comp_le.trans ?_
      have h1 : (-X : ℝ[X]).natDegree ≤ 1 := by simp
      calc _ ≤ (n + 1) * (-X : ℝ[X]).natDegree :=
            Nat.mul_le_mul_right _ (natDegree_truncatedPowerCellPolynomial_le n _ _)
        _ ≤ (n + 1) * 1 := Nat.mul_le_mul_left _ h1
        _ = n + 1 := by ring
    · exact natDegree_truncatedPowerCellPolynomial_le n _ _

/-- The mixed derivatives of the unweighted cell function: a sum of products of polynomial
jets, at every point of the plane. -/
theorem mixedDeriv_cellField_one (n L : ℕ) (lv : ℕ → Level) (a b c d : ℝ) (k l : ℕ)
    (x y : ℝ) :
    mixedDeriv k l (cellField n L lv (fun _ ↦ 1) a b c d) x y =
      ∑ m ∈ range L, ∑ i ∈ range (lv m).rows, ∑ j ∈ range (lv m).cols,
        ((lv m).coeff i j : ℝ) * polynomialJet k (piece n (lv m).xKnots ((lv m).xModes i) a b) x *
          polynomialJet l (piece n (lv m).yKnots ((lv m).yModes j) c d) y := by
  have h := mixedDeriv_tensor (L := L) (I := fun m ↦ (lv m).rows) (J := fun m ↦ (lv m).cols)
    (fun m i j ↦ ((lv m).coeff i j : ℝ))
    (fun m i x ↦ (piece n (lv m).xKnots ((lv m).xModes i) a b).eval x)
    (fun m j y ↦ (fun _ ↦ (1 : ℝ)) y * (piece n (lv m).yKnots ((lv m).yModes j) c d).eval y)
    (k := k) (l := l) (fun m i ↦ PDE.Analysis.contDiff_polynomial_eval _)
    (fun m j ↦ contDiff_const.mul (PDE.Analysis.contDiff_polynomial_eval _)) x y
  unfold cellField
  rw [h]
  refine sum_congr rfl fun m _ ↦ sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only [one_mul]
  rw [iteratedDeriv_eval_eq_polynomialJet, iteratedDeriv_eval_eq_polynomialJet]

/-- The first variable: `∂ₓ` of `∂ₓᵏ ∂ᵧˡ` of the cell function is `∂ₓᵏ⁺¹ ∂ᵧˡ`. -/
theorem hasDerivAt_mixedDeriv_cellField_fst (n L : ℕ) (lv : ℕ → Level) (a b c d : ℝ)
    (k l : ℕ) (x y : ℝ) :
    HasDerivAt (fun u ↦ mixedDeriv k l (cellField n L lv (fun _ ↦ 1) a b c d) u y)
      (mixedDeriv (k + 1) l (cellField n L lv (fun _ ↦ 1) a b c d) x y) x := by
  simp only [mixedDeriv_cellField_one]
  refine HasDerivAt.fun_sum fun m _ ↦ HasDerivAt.fun_sum fun i _ ↦ HasDerivAt.fun_sum fun j _ ↦ ?_
  exact ((PolynomialSplineData.hasDerivAt_polynomialJet k _ x).const_mul _).mul_const _

/-- The second variable: `∂ᵧ` of `∂ₓᵏ ∂ᵧˡ` of the cell function is `∂ₓᵏ ∂ᵧˡ⁺¹`. -/
theorem hasDerivAt_mixedDeriv_cellField_snd (n L : ℕ) (lv : ℕ → Level) (a b c d : ℝ)
    (k l : ℕ) (x y : ℝ) :
    HasDerivAt (fun v ↦ mixedDeriv k l (cellField n L lv (fun _ ↦ 1) a b c d) x v)
      (mixedDeriv k (l + 1) (cellField n L lv (fun _ ↦ 1) a b c d) x y) y := by
  simp only [mixedDeriv_cellField_one]
  refine HasDerivAt.fun_sum fun m _ ↦ HasDerivAt.fun_sum fun i _ ↦ HasDerivAt.fun_sum fun j _ ↦ ?_
  exact (PolynomialSplineData.hasDerivAt_polynomialJet l _ y).const_mul _

/-- Beyond order `n + 1` in either variable the derivatives of the cell function vanish. -/
theorem mixedDeriv_cellField_eq_zero (n L : ℕ) (lv : ℕ → Level) (a b c d : ℝ) {k l : ℕ}
    (hkl : n + 1 < k ∨ n + 1 < l) (x y : ℝ) :
    mixedDeriv k l (cellField n L lv (fun _ ↦ 1) a b c d) x y = 0 := by
  rw [mixedDeriv_cellField_one]
  refine sum_eq_zero fun m _ ↦ sum_eq_zero fun i _ ↦ sum_eq_zero fun j _ ↦ ?_
  rcases hkl with hk | hl
  · rw [polynomialJet_eq_zero_of_degree_lt (natDegree_piece_le n _ _ a b) hk]
    ring
  · rw [polynomialJet_eq_zero_of_degree_lt (natDegree_piece_le n _ _ c d) hl]
    ring

/-- The scaled derivative `σ (b - a)ᵏ (d - c)ˡ ∂ₓᵏ ∂ᵧˡ P` of the unweighted cell function `P` on
`[a, b] × [c, d]`, with a real factor `σ`. -/
noncomputable def scaledCellDeriv (n L : ℕ) (lv : ℕ → Level) (σ a b c d : ℝ) (k l : ℕ)
    (x y : ℝ) : ℝ :=
  σ * ((b - a) ^ k * (d - c) ^ l *
    mixedDeriv k l (cellField n L lv (fun _ ↦ 1) a b c d) x y)

/-- **The one-step estimate on a cell.** For every constant `c₀`,
`|G_kl - c₀| ≤ B + M₁ / 8 + M₂ / 8` on the cell when `|G_kl - c₀| ≤ B` at the four corners and
`M₁`, `M₂` bound `G_{k+2,l}` and `G_{k,l+2}` on the cell, for the scaled derivatives
`G = scaledCellDeriv`. -/
theorem abs_scaledCellDeriv_sub_le (n L : ℕ) (lv : ℕ → Level) {σ a b c d : ℝ} (hab : a < b)
    (hcd : c < d) {k l : ℕ} {c₀ B M₁ M₂ : ℝ}
    (hcorner : ∀ e f : Bool, |scaledCellDeriv n L lv σ a b c d k l (if e then b else a)
      (if f then d else c) - c₀| ≤ B)
    (h₁ : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, |scaledCellDeriv n L lv σ a b c d (k + 2) l x y| ≤ M₁)
    (h₂ : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, |scaledCellDeriv n L lv σ a b c d k (l + 2) x y| ≤ M₂)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    |scaledCellDeriv n L lv σ a b c d k l x y - c₀| ≤ B + M₁ / 8 + M₂ / 8 := by
  set P := cellField n L lv (fun _ ↦ 1) a b c d
  set s : ℝ := σ * ((b - a) ^ k * (d - c) ^ l) with hs
  have hba : 0 < b - a := sub_pos.mpr hab
  have hdc : 0 < d - c := sub_pos.mpr hcd
  have hG : ∀ k' l' u v, scaledCellDeriv n L lv σ a b c d k' l' u v =
      σ * ((b - a) ^ k' * (d - c) ^ l') * mixedDeriv k' l' P u v := fun _ _ _ _ ↦ by
    unfold scaledCellDeriv; ring
  have hkx : ∀ u v, scaledCellDeriv n L lv σ a b c d (k + 2) l u v =
      (b - a) ^ 2 * (s * mixedDeriv (k + 2) l P u v) := fun u v ↦ by
    rw [hG, hs]; ring
  have hly : ∀ u v, scaledCellDeriv n L lv σ a b c d k (l + 2) u v =
      (d - c) ^ 2 * (s * mixedDeriv k (l + 2) P u v) := fun u v ↦ by
    rw [hG, hs]; ring
  have key := PDE.Analysis.Approximation.abs_le_of_abs_corner_le
    (f := fun u v ↦ s * mixedDeriv k l P u v - c₀)
    (fx := fun u v ↦ s * mixedDeriv (k + 1) l P u v)
    (fxx := fun u v ↦ s * mixedDeriv (k + 2) l P u v)
    (fy := fun u v ↦ s * mixedDeriv k (l + 1) P u v)
    (fyy := fun u v ↦ s * mixedDeriv k (l + 2) P u v)
    (Mx := M₁ / (b - a) ^ 2) (My := M₂ / (d - c) ^ 2) (B := B)
    (fun v _ u _ ↦ (((hasDerivAt_mixedDeriv_cellField_fst n L lv a b c d k l u v).const_mul s
      ).sub_const c₀).continuousAt.continuousWithinAt)
    (fun v _ u _ ↦
      ((hasDerivAt_mixedDeriv_cellField_fst n L lv a b c d k l u v).const_mul s).sub_const c₀)
    (fun v _ u _ ↦ by
      simpa using (hasDerivAt_mixedDeriv_cellField_fst n L lv a b c d (k + 1) l u v).const_mul s)
    (fun v hv u hu ↦ by
      have := h₁ u (Ioo_subset_Icc_self hu) v hv
      rw [hkx, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (b - a) ^ 2)] at this
      rw [le_div_iff₀ (by positivity)]
      linarith)
    (fun u _ v _ ↦ (((hasDerivAt_mixedDeriv_cellField_snd n L lv a b c d k l u v).const_mul s
      ).sub_const c₀).continuousAt.continuousWithinAt)
    (fun u _ v _ ↦
      ((hasDerivAt_mixedDeriv_cellField_snd n L lv a b c d k l u v).const_mul s).sub_const c₀)
    (fun u _ v _ ↦ by
      simpa using (hasDerivAt_mixedDeriv_cellField_snd n L lv a b c d k (l + 1) u v).const_mul s)
    (fun u hu v hv ↦ by
      have := h₂ u hu v (Ioo_subset_Icc_self hv)
      rw [hly, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (d - c) ^ 2)] at this
      rw [le_div_iff₀ (by positivity)]
      linarith)
    (by simpa [hG, hs] using hcorner false false) (by simpa [hG, hs] using hcorner false true)
    (by simpa [hG, hs] using hcorner true false) (by simpa [hG, hs] using hcorner true true)
    hx hy
  have e1 : M₁ / (b - a) ^ 2 * (b - a) ^ 2 / 8 = M₁ / 8 := by field_simp
  have e2 : M₂ / (d - c) ^ 2 * (d - c) ^ 2 / 8 = M₂ / 8 := by field_simp
  rw [e1, e2] at key
  simpa [hG, hs] using key

/-- **The one-step estimate as an enclosure.** If the four corner values of `f` lie in
`[lo, hi]` and `M₁`, `M₂` bound `∂ₓ² f` and `∂ᵧ² f` on the slices of `[a, b] × [c, d]`, then on the
whole rectangle `f` lies in `[lo, hi]` widened by `(M₁ (b - a)² + M₂ (d - c)²) / 8`: Part II,
(C.13) in two dimensions applied to `f - (lo + hi) / 2`. The two directions may use different
derivative functions. -/
theorem mem_Icc_of_corner_step {f fx fxx fy fyy : ℝ → ℝ → ℝ} {a b c d M₁ M₂ lo hi x y : ℝ}
    (hcontX : ∀ v ∈ Icc c d, ContinuousOn (fun u ↦ f u v) (Icc a b))
    (hderivX : ∀ v ∈ Icc c d, ∀ u ∈ Ioo a b, HasDerivAt (fun z ↦ f z v) (fx u v) u)
    (hderivXX : ∀ v ∈ Icc c d, ∀ u ∈ Ioo a b, HasDerivAt (fun z ↦ fx z v) (fxx u v) u)
    (hboundX : ∀ v ∈ Icc c d, ∀ u ∈ Ioo a b, |fxx u v| ≤ M₁)
    (hcontY : ∀ u ∈ Icc a b, ContinuousOn (f u) (Icc c d))
    (hderivY : ∀ u ∈ Icc a b, ∀ v ∈ Ioo c d, HasDerivAt (f u) (fy u v) v)
    (hderivYY : ∀ u ∈ Icc a b, ∀ v ∈ Ioo c d, HasDerivAt (fy u) (fyy u v) v)
    (hboundY : ∀ u ∈ Icc a b, ∀ v ∈ Ioo c d, |fyy u v| ≤ M₂)
    (hcorner : ∀ e e' : Bool, lo ≤ f (if e then b else a) (if e' then d else c) ∧
      f (if e then b else a) (if e' then d else c) ≤ hi)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    lo - (M₁ * (b - a) ^ 2 + M₂ * (d - c) ^ 2) / 8 ≤ f x y ∧
      f x y ≤ hi + (M₁ * (b - a) ^ 2 + M₂ * (d - c) ^ 2) / 8 := by
  set c₀ := (lo + hi) / 2 with hc₀
  have hc : ∀ e e' : Bool, |f (if e then b else a) (if e' then d else c) - c₀| ≤ (hi - lo) / 2 :=
    fun e e' ↦ by
      have := hcorner e e'
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have key := PDE.Analysis.Approximation.abs_le_of_abs_corner_le
    (f := fun u v ↦ f u v - c₀) (fx := fx) (fxx := fxx) (fy := fy) (fyy := fyy)
    (Mx := M₁) (My := M₂) (B := (hi - lo) / 2)
    (fun v hv ↦ (hcontX v hv).sub continuousOn_const)
    (fun v hv u hu ↦ (hderivX v hv u hu).sub_const c₀) hderivXX hboundX
    (fun u hu ↦ (hcontY u hu).sub continuousOn_const)
    (fun u hu v hv ↦ (hderivY u hu v hv).sub_const c₀) hderivYY hboundY
    (by simpa using hc false false) (by simpa using hc false true)
    (by simpa using hc true false) (by simpa using hc true true) hx hy
  rw [abs_le] at key
  constructor <;> nlinarith [key.1, key.2]

/-! ### Enclosures from integer corner data -/

/-- `n / 8 ≤ ⌈n / 8⌉`. -/
theorem div_eight_le_ceilDiv (n : ℕ) : (n : ℝ) / 8 ≤ ceilDiv n 8 := by
  have h' : (n : ℝ) ≤ 8 * (ceilDiv n 8 : ℝ) := by exact_mod_cast le_mul_ceilDiv (by norm_num)
  linarith

/-- Integer corner data of one cell: approximations `val e f k l` of the scaled derivative
`G_kl` at the corner `(e, f)` (`false` the lower and `true` the upper end of each variable) and
bounds `err e f k l` of their errors. -/
structure CellCorners where
  /-- The approximate corner values. -/
  val : Bool → Bool → ℕ → ℕ → ℤ
  /-- The error bounds of the corner values. -/
  err : Bool → Bool → ℕ → ℕ → ℕ

namespace CellCorners

variable (C : CellCorners)

/-- The smallest corner value minus its error. -/
def low (k l : ℕ) : ℤ :=
  min (min (C.val false false k l - C.err false false k l)
      (C.val false true k l - C.err false true k l))
    (min (C.val true false k l - C.err true false k l) (C.val true true k l - C.err true true k l))

/-- The largest corner value plus its error. -/
def high (k l : ℕ) : ℤ :=
  max (max (C.val false false k l + C.err false false k l)
      (C.val false true k l + C.err false true k l))
    (max (C.val true false k l + C.err true false k l) (C.val true true k l + C.err true true k l))

/-- The largest absolute corner value plus its error. -/
def mag (k l : ℕ) : ℕ :=
  max (max ((C.val false false k l).natAbs + C.err false false k l)
      ((C.val false true k l).natAbs + C.err false true k l))
    (max ((C.val true false k l).natAbs + C.err true false k l)
      ((C.val true true k l).natAbs + C.err true true k l))

/-- The cell bounds of the recursion `A_kl = B_kl + ⌈(A_{k+2,l} + A_{k,l+2}) / 8⌉` for
`k, l ≤ N`, with `A = 0` beyond. -/
def bound (N k l : ℕ) : ℕ :=
  if _h : k ≤ N ∧ l ≤ N then C.mag k l + ceilDiv (bound N (k + 2) l + bound N k (l + 2)) 8
  else 0
termination_by 2 * N + 2 - (k + l)
decreasing_by all_goals omega

/-- The widening `⌈(A_{k+2,l} + A_{k,l+2}) / 8⌉` of the corner extremes. -/
def widen (N k l : ℕ) : ℕ := ceilDiv (C.bound N (k + 2) l + C.bound N k (l + 2)) 8

/-- The lower end of the enclosure of `G_kl` on the cell. -/
def lower (N k l : ℕ) : ℤ := C.low k l - C.widen N k l

/-- The upper end of the enclosure of `G_kl` on the cell. -/
def upper (N k l : ℕ) : ℤ := C.high k l + C.widen N k l

/-- Every corner value minus its error is at least `low`. -/
theorem low_le_val (k l : ℕ) (e f : Bool) :
    C.low k l ≤ C.val e f k l - C.err e f k l := by
  unfold low; cases e <;> cases f <;> simp

/-- Every corner value plus its error is at most `high`. -/
theorem val_add_le_high (k l : ℕ) (e f : Bool) :
    C.val e f k l + C.err e f k l ≤ C.high k l := by
  unfold high; cases e <;> cases f <;> simp

/-- Every absolute corner value plus its error is at most `mag`. -/
theorem natAbs_add_le_mag (k l : ℕ) (e f : Bool) :
    (C.val e f k l).natAbs + C.err e f k l ≤ C.mag k l := by
  unfold mag; cases e <;> cases f <;> simp

/-- The enclosure `[lower N k l, upper N k l]` is nonempty. -/
theorem lower_le_upper (N k l : ℕ) : C.lower N k l ≤ C.upper N k l := by
  have h1 := C.low_le_val k l false false
  have h2 := C.val_add_le_high k l false false
  unfold lower upper
  omega

variable {C}

/-- **Cell enclosures from corner data.** Let `G k l` satisfy the one-step estimate on
`[a, b] × [c, d]` for `k, l ≤ N` and vanish beyond, and let the corner data approximate its
corner values within the errors. Then `|G_kl| ≤ bound N k l` and
`lower N k l ≤ G_kl ≤ upper N k l` on the whole cell. -/
theorem abs_le_bound {N : ℕ} {a b c d : ℝ} (G : ℕ → ℕ → ℝ → ℝ → ℝ)
    (hstep : ∀ k l, k ≤ N → l ≤ N → ∀ c₀ B M₁ M₂ : ℝ,
      (∀ e f : Bool, |G k l (if e then b else a) (if f then d else c) - c₀| ≤ B) →
      (∀ x ∈ Icc a b, ∀ y ∈ Icc c d, |G (k + 2) l x y| ≤ M₁) →
      (∀ x ∈ Icc a b, ∀ y ∈ Icc c d, |G k (l + 2) x y| ≤ M₂) →
      ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, |G k l x y - c₀| ≤ B + M₁ / 8 + M₂ / 8)
    (htop : ∀ k l, N < k ∨ N < l → ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, G k l x y = 0)
    (hval : ∀ e f k l, k ≤ N → l ≤ N →
      |(C.val e f k l : ℝ) - G k l (if e then b else a) (if f then d else c)| ≤ C.err e f k l)
    (k l : ℕ) : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, |G k l x y| ≤ C.bound N k l := by
  suffices h : ∀ m k l, 2 * N + 2 - (k + l) ≤ m → ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      |G k l x y| ≤ C.bound N k l from h _ k l le_rfl
  intro m
  induction m with
  | zero =>
    intro k l hm x hx y hy
    rw [htop k l (by omega) x hx y hy, abs_zero]
    exact Nat.cast_nonneg _
  | succ m ih =>
    intro k l hm x hx y hy
    by_cases hkl : k ≤ N ∧ l ≤ N
    · have hb : C.bound N k l =
          C.mag k l + ceilDiv (C.bound N (k + 2) l + C.bound N k (l + 2)) 8 := by
        rw [bound]
        simp only [hkl, and_self, ↓reduceDIte]
      have h₁ := ih (k + 2) l (by omega)
      have h₂ := ih k (l + 2) (by omega)
      have hc : ∀ e f : Bool, |G k l (if e then b else a) (if f then d else c) - 0| ≤
          (C.mag k l : ℝ) := fun e f ↦ by
        have hv := hval e f k l hkl.1 hkl.2
        have hm := C.natAbs_add_le_mag k l e f
        have hm' : ((C.val e f k l).natAbs : ℝ) + C.err e f k l ≤ C.mag k l := by
          exact_mod_cast hm
        have habs : |(C.val e f k l : ℝ)| = ((C.val e f k l).natAbs : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        rw [sub_zero]
        have := abs_sub_abs_le_abs_sub (G k l (if e then b else a) (if f then d else c))
          (C.val e f k l : ℝ)
        rw [abs_sub_comm] at hv
        linarith [abs_sub_comm (G k l (if e then b else a) (if f then d else c))
          (C.val e f k l : ℝ)]
      have hs := hstep k l hkl.1 hkl.2 0 _ _ _ hc h₁ h₂ x hx y hy
      rw [sub_zero] at hs
      rw [hb]
      push_cast
      have := div_eight_le_ceilDiv (C.bound N (k + 2) l + C.bound N k (l + 2))
      push_cast at this
      linarith
    · have : N < k ∨ N < l := by omega
      rw [htop k l this x hx y hy, abs_zero]
      exact Nat.cast_nonneg _

/-- **Cell enclosures between the corner extremes.** Under the hypotheses of `abs_le_bound`,
`lower N k l ≤ G_kl ≤ upper N k l` on the whole cell for `k, l ≤ N`. -/
theorem mem_Icc_of_corners {N : ℕ} {a b c d : ℝ} (G : ℕ → ℕ → ℝ → ℝ → ℝ)
    (hstep : ∀ k l, k ≤ N → l ≤ N → ∀ c₀ B M₁ M₂ : ℝ,
      (∀ e f : Bool, |G k l (if e then b else a) (if f then d else c) - c₀| ≤ B) →
      (∀ x ∈ Icc a b, ∀ y ∈ Icc c d, |G (k + 2) l x y| ≤ M₁) →
      (∀ x ∈ Icc a b, ∀ y ∈ Icc c d, |G k (l + 2) x y| ≤ M₂) →
      ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, |G k l x y - c₀| ≤ B + M₁ / 8 + M₂ / 8)
    (htop : ∀ k l, N < k ∨ N < l → ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, G k l x y = 0)
    (hval : ∀ e f k l, k ≤ N → l ≤ N →
      |(C.val e f k l : ℝ) - G k l (if e then b else a) (if f then d else c)| ≤ C.err e f k l)
    {k l : ℕ} (hk : k ≤ N) (hl : l ≤ N) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    (C.lower N k l : ℝ) ≤ G k l x y ∧ G k l x y ≤ C.upper N k l := by
  set c₀ : ℝ := ((C.low k l : ℝ) + C.high k l) / 2 with hc₀
  have hc : ∀ e f : Bool, |G k l (if e then b else a) (if f then d else c) - c₀| ≤
      ((C.high k l : ℝ) - C.low k l) / 2 := fun e f ↦ by
    have hv := hval e f k l hk hl
    have h1 : ((C.low k l : ℤ) : ℝ) ≤ (C.val e f k l : ℝ) - C.err e f k l := by
      exact_mod_cast C.low_le_val k l e f
    have h2 : (C.val e f k l : ℝ) + C.err e f k l ≤ ((C.high k l : ℤ) : ℝ) := by
      exact_mod_cast C.val_add_le_high k l e f
    rw [abs_le] at hv ⊢
    constructor <;> linarith [hv.1, hv.2, hc₀]
  have hs := hstep k l hk hl c₀ _ _ _ hc (abs_le_bound G hstep htop hval (k + 2) l)
    (abs_le_bound G hstep htop hval k (l + 2)) x hx y hy
  have hw := div_eight_le_ceilDiv (C.bound N (k + 2) l + C.bound N k (l + 2))
  have hw' : (C.widen N k l : ℝ) ≥ ((C.bound N (k + 2) l : ℝ) + C.bound N k (l + 2)) / 8 := by
    unfold widen; push_cast at hw; linarith
  rw [abs_le] at hs
  unfold lower upper
  push_cast
  constructor <;> linarith [hs.1, hs.2, hc₀]

end CellCorners

end CAS.Numerics.TensorSpline
