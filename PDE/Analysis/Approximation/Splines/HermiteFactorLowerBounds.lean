/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteFactorAssembly
import CAS.ExactTactic

/-!
# Lower bounds for assembled Hermite factors

Constant and affine lower Bernstein controls bound the factor on a
closed panel, including interior spline knots. Only derivatives in the open
support are used.
-/

@[expose] public section

noncomputable section

open Set Polynomial

namespace CAS.Splines

/-- A cubic Bernstein polynomial is at least a common lower control bound. -/
theorem le_bernstein_cubic_of_le_controls
    {m z : ℝ} {c : Fin 4 → ℝ} (hz : z ∈ Icc 0 1) (hc : ∀ k, m ≤ c k) :
    m ≤ c 0 * (bernsteinPolynomial ℝ 3 0).eval z +
      c 1 * (bernsteinPolynomial ℝ 3 1).eval z +
      c 2 * (bernsteinPolynomial ℝ 3 2).eval z +
      c 3 * (bernsteinPolynomial ℝ 3 3).eval z := by
  have hn (i : ℕ) : 0 ≤ (bernsteinPolynomial ℝ 3 i).eval z := by
    simp only [bernsteinPolynomial, eval_mul, eval_natCast, eval_pow, eval_X,
      eval_sub, eval_one]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz.1 _))
      (pow_nonneg (sub_nonneg.mpr hz.2) _)
  have hs : (bernsteinPolynomial ℝ 3 0).eval z +
      (bernsteinPolynomial ℝ 3 1).eval z +
      (bernsteinPolynomial ℝ 3 2).eval z +
      (bernsteinPolynomial ℝ 3 3).eval z = 1 := by
    have h := congrArg (fun p : ℝ[X] ↦ p.eval z) (bernsteinPolynomial.sum ℝ 3)
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, eval_add, eval_one] using h
  calc
    m = m * (bernsteinPolynomial ℝ 3 0).eval z +
        m * (bernsteinPolynomial ℝ 3 1).eval z +
        m * (bernsteinPolynomial ℝ 3 2).eval z +
        m * (bernsteinPolynomial ℝ 3 3).eval z := by
      rw [← mul_add, ← mul_add, ← mul_add, hs, mul_one]
    _ ≤ _ := add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right (hc 0) (hn 0))
      (mul_le_mul_of_nonneg_right (hc 1) (hn 1)))
      (mul_le_mul_of_nonneg_right (hc 2) (hn 2)))
      (mul_le_mul_of_nonneg_right (hc 3) (hn 3))

/-- A common lower Bernstein control bounds the factor on a closed panel. -/
theorem HermiteData.le_factor_compactOddProfile_of_controls
    {panels : ℕ} (data : HermiteData (panels + 1))
    (mesh : StrictKnotMesh (panels + 1))
    (hmesh : mesh.knot 0 = 0) (hzero : data.value 0 = 0)
    (κ center m : ℝ) (i : Fin (panels + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (mesh.knot (Fin.last (panels + 1))))
    (hpanel : x ∈ Icc (mesh.panelLeft i) (mesh.panelRight i))
    (hc : ∀ k, m ≤ hermiteFactorControl κ (mesh.panelLeft i - center)
      (mesh.panelRight i - mesh.panelLeft i) (data.value i.castSucc) (data.value i.succ)
      (data.slope i.castSucc) (data.slope i.succ) k) :
    m ≤ data.compactOddProfile mesh x -
      κ * (x - center) * deriv (data.compactOddProfile mesh) x := by
  rw [data.compactOddProfile_eq_piece mesh hmesh hzero i hpanel,
    data.deriv_compactOddProfile_eq_panel mesh hmesh hzero i hx hpanel]
  change m ≤ (hermitePolynomial _ _ _ _ _ _).eval x -
    κ * (x - center) * polynomialJet 1 (hermitePolynomial _ _ _ _ _ _) x
  rw [hermitePolynomial_factor_eq_bernstein _ _ _ _ _ _ _ _ _
    (sub_pos.mpr (mesh.panelLeft_lt_panelRight i)).ne']
  apply le_bernstein_cubic_of_le_controls _ hc
  constructor
  · exact div_nonneg (sub_nonneg.mpr hpanel.1)
      (sub_nonneg.mpr (mesh.panelLeft_lt_panelRight i).le)
  · exact (div_le_one (sub_pos.mpr (mesh.panelLeft_lt_panelRight i))).mpr
      (sub_le_sub_right hpanel.2 _)


/-- Cubic Bernstein controls of an affine function reproduce that function. -/
theorem bernstein_cubic_affine (s r left h z : ℝ) :
    (s * left + r) * (bernsteinPolynomial ℝ 3 0).eval z +
      (s * (left + h / 3) + r) * (bernsteinPolynomial ℝ 3 1).eval z +
      (s * (left + 2 * h / 3) + r) * (bernsteinPolynomial ℝ 3 2).eval z +
      (s * (left + h) + r) * (bernsteinPolynomial ℝ 3 3).eval z =
        s * (left + h * z) + r := by
  simp only [bernsteinPolynomial, eval_mul, eval_natCast, eval_pow, eval_X,
    eval_sub, eval_one]
  norm_num
  cas

/-- An affine lower bound on all four controls holds throughout the panel. -/
theorem affine_le_bernstein_cubic
    {s r left h z : ℝ} {c : Fin 4 → ℝ}
    (hz : z ∈ Icc 0 1)
    (hc : ∀ k : Fin 4, s * (left + (k.val : ℝ) * h / 3) + r ≤ c k) :
    s * (left + h * z) + r ≤
      c 0 * (bernsteinPolynomial ℝ 3 0).eval z +
      c 1 * (bernsteinPolynomial ℝ 3 1).eval z +
      c 2 * (bernsteinPolynomial ℝ 3 2).eval z +
      c 3 * (bernsteinPolynomial ℝ 3 3).eval z := by
  have hn (i : ℕ) : 0 ≤ (bernsteinPolynomial ℝ 3 i).eval z := by
    simp only [bernsteinPolynomial, eval_mul, eval_natCast, eval_pow, eval_X,
      eval_sub, eval_one]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz.1 _))
      (pow_nonneg (sub_nonneg.mpr hz.2) _)
  rw [← bernstein_cubic_affine s r left h z]
  apply add_le_add (add_le_add (add_le_add _ _) _) _
  · apply mul_le_mul_of_nonneg_right _ (hn 0)
    simpa using hc 0
  · apply mul_le_mul_of_nonneg_right _ (hn 1)
    simpa using hc 1
  · apply mul_le_mul_of_nonneg_right _ (hn 2)
    simpa using hc 2
  · apply mul_le_mul_of_nonneg_right _ (hn 3)
    convert hc 3 using 1
    norm_num

/-- A compact Hermite profile inherits an affine factor lower bound from its
panel controls, including at an interior spline knot. -/
theorem HermiteData.affine_le_factor_compactOddProfile_of_controls
    {panels : ℕ} (data : HermiteData (panels + 1))
    (mesh : StrictKnotMesh (panels + 1))
    (hmesh : mesh.knot 0 = 0) (hzero : data.value 0 = 0)
    (κ center s r : ℝ) (i : Fin (panels + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (mesh.knot (Fin.last (panels + 1))))
    (hpanel : x ∈ Icc (mesh.panelLeft i) (mesh.panelRight i))
    (hc : ∀ k : Fin 4,
      s * (mesh.panelLeft i + (k.val : ℝ) *
        (mesh.panelRight i - mesh.panelLeft i) / 3) + r ≤
      hermiteFactorControl κ (mesh.panelLeft i - center)
        (mesh.panelRight i - mesh.panelLeft i) (data.value i.castSucc) (data.value i.succ)
        (data.slope i.castSucc) (data.slope i.succ) k) :
    s * x + r ≤ data.compactOddProfile mesh x -
      κ * (x - center) * deriv (data.compactOddProfile mesh) x := by
  have hh := sub_pos.mpr (mesh.panelLeft_lt_panelRight i)
  rw [data.compactOddProfile_eq_piece mesh hmesh hzero i hpanel,
    data.deriv_compactOddProfile_eq_panel mesh hmesh hzero i hx hpanel]
  change s * x + r ≤ (hermitePolynomial _ _ _ _ _ _).eval x -
    κ * (x - center) * polynomialJet 1 (hermitePolynomial _ _ _ _ _ _) x
  rw [hermitePolynomial_factor_eq_bernstein _ _ _ _ _ _ _ _ _ hh.ne']
  have hz : (x - mesh.panelLeft i) / (mesh.panelRight i - mesh.panelLeft i) ∈ Icc 0 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hpanel.1) hh.le,
      (div_le_one hh).mpr (sub_le_sub_right hpanel.2 _)⟩
  have he := affine_le_bernstein_cubic hz hc
  rw [mul_div_cancel₀ _ hh.ne', add_sub_cancel] at he
  exact he


end CAS.Splines
