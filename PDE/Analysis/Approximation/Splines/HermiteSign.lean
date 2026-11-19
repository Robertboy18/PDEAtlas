/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteCompactProfile
public import PDE.Analysis.Approximation.Splines.NormalizedBasis
import CAS.ExactTactic

/-!
# Sign certificates for assembled cubic Hermite profiles

The two interior Bernstein coefficients control overshoot between nodes.
Nonpositive control coefficients and a negative endpoint value force strict
negativity in the open panel. Assembly checks the shared knots separately.
-/

@[expose] public section

noncomputable section

open Set Polynomial

namespace CAS.Splines

/-- The Hermite panel expressed in Mathlib's cubic Bernstein basis. -/
theorem hermiteValue_eq_bernstein (h a b da db z : ℝ) :
    hermiteValue h a b da db z =
      a * (bernsteinPolynomial ℝ 3 0).eval z +
      (a + h * da / 3) * (bernsteinPolynomial ℝ 3 1).eval z +
      (b - h * db / 3) * (bernsteinPolynomial ℝ 3 2).eval z +
      b * (bernsteinPolynomial ℝ 3 3).eval z := by
  simp only [bernsteinPolynomial, eval_mul, eval_natCast, eval_pow, eval_X,
    eval_sub, eval_one]
  norm_num
  unfold hermiteValue
  cas

/-- On a closed panel, increasing the left slope and decreasing the right
slope increases the Hermite interpolant. -/
theorem hermiteValue_mono_slopes {h a b da db lo hi z : ℝ}
    (hh : 0 ≤ h) (hlo : lo ≤ da) (hhi : db ≤ hi) (hz : z ∈ Icc 0 1) :
    hermiteValue h a b lo hi z ≤ hermiteValue h a b da db z := by
  rw [hermiteValue_eq_bernstein, hermiteValue_eq_bernstein]
  have hn (i : ℕ) : 0 ≤ (bernsteinPolynomial ℝ 3 i).eval z :=
    bernsteinPolynomial_eval_nonneg 3 i hz.1 hz.2
  have hleft : a + h * lo / 3 ≤ a + h * da / 3 := by gcongr
  have hright : b - h * hi / 3 ≤ b - h * db / 3 := by gcongr
  exact add_le_add
    (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hleft (hn 1)))
      (mul_le_mul_of_nonneg_right hright (hn 2))) le_rfl

/-- Nonpositive Bernstein coefficients bound the entire closed Hermite panel. -/
theorem hermiteValue_nonpos_of_controls {h a b da db z : ℝ}
    (ha : a ≤ 0) (hb : b ≤ 0) (hleft : a + h * da / 3 ≤ 0)
    (hright : b - h * db / 3 ≤ 0) (hz : z ∈ Icc 0 1) :
    hermiteValue h a b da db z ≤ 0 := by
  rw [hermiteValue_eq_bernstein]
  have hn (i : ℕ) : 0 ≤ (bernsteinPolynomial ℝ 3 i).eval z :=
    bernsteinPolynomial_eval_nonneg 3 i hz.1 hz.2
  exact add_nonpos
    (add_nonpos (add_nonpos (mul_nonpos_of_nonpos_of_nonneg ha (hn 0))
      (mul_nonpos_of_nonpos_of_nonneg hleft (hn 1)))
      (mul_nonpos_of_nonpos_of_nonneg hright (hn 2)))
    (mul_nonpos_of_nonpos_of_nonneg hb (hn 3))

/-- A negative endpoint coefficient makes the open panel strictly negative.
Node signs alone do not supply the two control inequalities. -/
theorem hermiteValue_neg_of_controls {h a b da db z : ℝ}
    (ha : a ≤ 0) (hb : b ≤ 0) (hleft : a + h * da / 3 ≤ 0)
    (hright : b - h * db / 3 ≤ 0) (hstrict : a < 0 ∨ b < 0)
    (hz : z ∈ Ioo 0 1) : hermiteValue h a b da db z < 0 := by
  rw [hermiteValue_eq_bernstein]
  have hn (i : ℕ) : 0 ≤ (bernsteinPolynomial ℝ 3 i).eval z :=
    bernsteinPolynomial_eval_nonneg 3 i hz.1.le hz.2.le
  have hfirst : 0 < (bernsteinPolynomial ℝ 3 0).eval z := by
    simpa [bernsteinPolynomial] using pow_pos (sub_pos.mpr hz.2) 3
  have hlast : 0 < (bernsteinPolynomial ℝ 3 3).eval z := by
    simpa [bernsteinPolynomial] using pow_pos hz.1 3
  have h₁ := mul_nonpos_of_nonpos_of_nonneg hleft (hn 1)
  have h₂ := mul_nonpos_of_nonpos_of_nonneg hright (hn 2)
  rcases hstrict with ha' | hb'
  · have h₀ := mul_neg_of_neg_of_pos ha' hfirst
    have h₃ := mul_nonpos_of_nonpos_of_nonneg hb (hn 3)
    linarith
  · have h₀ := mul_nonpos_of_nonpos_of_nonneg ha (hn 0)
    have h₃ := mul_neg_of_neg_of_pos hb' hlast
    linarith

namespace HermiteData

/-- Nonpositive Bernstein controls and strictly negative interior nodal values
certify negativity of the compact odd assembly throughout its positive half.
At least two panels ensure every panel has an interior node as an endpoint. -/
theorem compactOddProfile_neg_of_controls
    {n : ℕ} (data : HermiteData (n + 2)) (mesh : StrictKnotMesh (n + 2))
    (hmesh : mesh.knot 0 = 0) (hzero : data.value 0 = 0)
    (hend : data.value (Fin.last (n + 2)) = 0)
    (hnodes : ∀ i : Fin (n + 3), i ≠ 0 → i ≠ Fin.last (n + 2) → data.value i < 0)
    (hleft : ∀ i : Fin (n + 2), data.value i.castSucc +
      (mesh.panelRight i - mesh.panelLeft i) * data.slope i.castSucc / 3 ≤ 0)
    (hright : ∀ i : Fin (n + 2), data.value i.succ -
      (mesh.panelRight i - mesh.panelLeft i) * data.slope i.succ / 3 ≤ 0)
    {x : ℝ} (hx : x ∈ Ioo 0 (mesh.knot (Fin.last (n + 2)))) :
    data.compactOddProfile mesh x < 0 := by
  have hnonpos (i : Fin (n + 3)) : data.value i ≤ 0 := by
    by_cases hi : i = 0
    · simp [hi, hzero]
    by_cases hl : i = Fin.last (n + 2)
    · simp [hl, hend]
    exact (hnodes i hi hl).le
  obtain ⟨i, hi⟩ := mesh.exists_mem_panel_of_mem_Icc (by omega)
    (show x ∈ Icc (mesh.knot 0) (mesh.knot (Fin.last (n + 2))) by
      rw [hmesh]
      exact ⟨hx.1.le, hx.2.le⟩)
  rw [data.compactOddProfile_eq_piece mesh hmesh hzero i hi]
  by_cases hxl : x = mesh.panelLeft i
  · change polynomialJet 0 ((data.polynomialData mesh).piece i) x < 0
    rw [hxl, data.value_left]
    apply hnodes i.castSucc ?_ (Fin.castSucc_ne_last i)
    intro heq
    have hx0 : x = 0 := by
      simpa only [StrictKnotMesh.panelLeft, heq, hmesh] using hxl
    linarith [hx.1]
  by_cases hxr : x = mesh.panelRight i
  · change polynomialJet 0 ((data.polynomialData mesh).piece i) x < 0
    rw [hxr, data.value_right]
    apply hnodes i.succ (Fin.succ_ne_zero i)
    intro heq
    have hxe : x = mesh.knot (Fin.last (n + 2)) := by
      simpa only [StrictKnotMesh.panelRight, heq] using hxr
    linarith [hx.2]
  have hlx : mesh.panelLeft i < x := lt_of_le_of_ne hi.1 (Ne.symm hxl)
  have hxr' : x < mesh.panelRight i := lt_of_le_of_ne hi.2 hxr
  have hwidth := sub_pos.mpr (mesh.panelLeft_lt_panelRight i)
  have hstrict : data.value i.castSucc < 0 ∨ data.value i.succ < 0 := by
    by_cases hi0 : i.castSucc = 0
    · right
      apply hnodes i.succ (Fin.succ_ne_zero i)
      intro hilast
      have hival := congrArg Fin.val hi0
      have hlastval := congrArg Fin.val hilast
      simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_succ, Fin.val_last] at *
      omega
    · exact Or.inl (hnodes i.castSucc hi0 (Fin.castSucc_ne_last i))
  change (hermitePolynomial (mesh.panelLeft i) (mesh.panelRight i - mesh.panelLeft i)
    (data.value i.castSucc) (data.value i.succ)
    (data.slope i.castSucc) (data.slope i.succ)).eval x < 0
  rw [hermitePolynomial_eval]
  apply hermiteValue_neg_of_controls (hnonpos _) (hnonpos _) (hleft i) (hright i) hstrict
  exact ⟨div_pos (sub_pos.mpr hlx) hwidth,
    (div_lt_one hwidth).mpr (by linarith)⟩

end HermiteData

end CAS.Splines
