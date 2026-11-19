/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Analysis.Approximation.Splines.Hermite
import CAS.ExactTactic

/-!
# Second derivative matching for cubic Hermite splines

Matching the second derivatives of adjacent Hermite panels is equivalent to a
tridiagonal equation for their nodal slopes. On a uniform mesh its coefficients are
`1, 4, 1`. Solving these equations upgrades the shared first jets to a cubic `C²`
spline; arbitrary nodal slopes only provide `C¹` matching.

The natural condition at the left endpoint and the backward-difference condition
at the right are kept separate. The latter need not give zero right curvature.
They are the end conditions of the spline of Chen, Hou and Huang (Section 4.1, step (2)) on
`[0, L]`: there the odd extension of the grid values to `[−L, L]` gives zero curvature at `0`,
and the slope at `L` is the three-point backward difference.

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  Section 4.1, step (2). <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

noncomputable section

namespace CAS.Splines

open _root_.Polynomial

/-- The left second jet in physical coordinates, including both slope coefficients. -/
theorem hermitePolynomial_second_left (left h a b da db : ℝ) (hh : h ≠ 0) :
    polynomialJet 2 (hermitePolynomial left h a b da db) left =
      6 * (b - a) / h ^ 2 - (4 * da + 2 * db) / h := by
  simp only [polynomialJet_succ, polynomialJet_zero, hermitePolynomial, map_mul, one_div,
    neg_mul, map_sub, map_add, map_neg, derivative_C, derivative_mul, zero_mul, mul_zero,
    add_zero, derivative_X, sub_zero, one_mul, zero_add, neg_zero, sub_self, derivative_pow,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, eval_add, eval_mul, eval_C, eval_sub, eval_neg, eval_X]
  cas using hh

/-- The right second jet in physical coordinates. -/
theorem hermitePolynomial_second_right (left h a b da db : ℝ) (hh : h ≠ 0) :
    polynomialJet 2 (hermitePolynomial left h a b da db) (left + h) =
      6 * (a - b) / h ^ 2 + (2 * da + 4 * db) / h := by
  simp only [polynomialJet_succ, polynomialJet_zero, hermitePolynomial, map_mul, one_div,
    neg_mul, map_sub, map_add, map_neg, derivative_C, derivative_mul, zero_mul, mul_zero,
    add_zero, derivative_X, sub_zero, one_mul, zero_add, neg_zero, sub_self, derivative_pow,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, eval_add, eval_mul, eval_C, eval_sub, eval_neg, eval_X]
  cas using hh

/-- The first matrix row is the natural condition at the left endpoint. -/
theorem hermitePolynomial_second_left_eq_zero_iff
    (left h a b da db : ℝ) (hh : h ≠ 0) :
    polynomialJet 2 (hermitePolynomial left h a b da db) left = 0 ↔
      2 * da + db = 3 * (b - a) / h := by
  rw [hermitePolynomial_second_left _ _ _ _ _ _ hh]
  have hid :
      6 * (b - a) / h ^ 2 - (4 * da + 2 * db) / h =
        (-2 / h) * (2 * da + db - 3 * (b - a) / h) := by
    cas using hh
  have hscale : (-2 : ℝ) / h ≠ 0 := div_ne_zero (by norm_num) hh
  rw [hid]
  simp only [mul_eq_zero, hscale, false_or, sub_eq_zero]

/-- With the backward-difference slope at the right end, the right curvature of the panel is
`2 (h da + previous - a) / h²`, which need not vanish. -/
theorem hermitePolynomial_second_right_backward_slope
    (left h previous a b da : ℝ) (hh : h ≠ 0) :
    polynomialJet 2
      (hermitePolynomial left h a b da ((3 * b - 4 * a + previous) / (2 * h)))
      (left + h) = 2 * (h * da + previous - a) / h ^ 2 := by
  rw [hermitePolynomial_second_right _ _ _ _ _ _ hh]
  cas using hh

/-- Second jets match precisely when the nonuniform tridiagonal slope equation holds. -/
theorem hermitePolynomial_second_match_iff
    (left hL hR a b c da db dc : ℝ) (hL0 : hL ≠ 0) (hR0 : hR ≠ 0) :
    polynomialJet 2 (hermitePolynomial left hL a b da db) (left + hL) =
        polynomialJet 2 (hermitePolynomial (left + hL) hR b c db dc) (left + hL) ↔
      hR * da + 2 * (hL + hR) * db + hL * dc =
        3 * (hR * (b - a) / hL + hL * (c - b) / hR) := by
  rw [hermitePolynomial_second_right _ _ _ _ _ _ hL0,
    hermitePolynomial_second_left _ _ _ _ _ _ hR0, ← sub_eq_zero]
  have hid :
      (6 * (a - b) / hL ^ 2 + (2 * da + 4 * db) / hL) -
          (6 * (c - b) / hR ^ 2 - (4 * db + 2 * dc) / hR) =
        (2 / (hL * hR)) * (hR * da + 2 * (hL + hR) * db + hL * dc -
          3 * (hR * (b - a) / hL + hL * (c - b) / hR)) := by
    cas using hL0
  have hscale : (2 : ℝ) / (hL * hR) ≠ 0 :=
    div_ne_zero (by norm_num) (mul_ne_zero hL0 hR0)
  rw [hid]
  simp only [mul_eq_zero, hscale, false_or, sub_eq_zero]

/-- On an exact uniform grid the interior coefficients are `1, 4, 1`. -/
theorem hermitePolynomial_second_match_uniform_iff
    (left h a b c da db dc : ℝ) (hh : h ≠ 0) :
    polynomialJet 2 (hermitePolynomial left h a b da db) (left + h) =
        polynomialJet 2 (hermitePolynomial (left + h) h b c db dc) (left + h) ↔
      da + 4 * db + dc = 3 * (c - a) / h := by
  rw [hermitePolynomial_second_right _ _ _ _ _ _ hh,
    hermitePolynomial_second_left _ _ _ _ _ _ hh, ← sub_eq_zero]
  have hid :
      (6 * (a - b) / h ^ 2 + (2 * da + 4 * db) / h) -
          (6 * (c - b) / h ^ 2 - (4 * db + 2 * dc) / h) =
        (2 / h) * (da + 4 * db + dc - 3 * (c - a) / h) := by
    cas using hh
  have hscale : (2 : ℝ) / h ≠ 0 := div_ne_zero (by norm_num) hh
  rw [hid]
  simp only [mul_eq_zero, hscale, false_or, sub_eq_zero]

namespace HermiteData

variable {panels : ℕ}

/-- Exact interior equations on the panel lengths of the supplied strict mesh. -/
def C2SlopeEquations (data : HermiteData panels) (mesh : StrictKnotMesh panels) : Prop :=
  ∀ (i : Fin panels) (hi : i.val + 1 < panels),
    let j := StrictKnotMesh.rightNeighbor i hi
    let hL := mesh.panelRight i - mesh.panelLeft i
    let hR := mesh.panelRight j - mesh.panelLeft j
    hR * data.slope i.castSucc + 2 * (hL + hR) * data.slope i.succ +
        hL * data.slope j.succ =
      3 * (hR * (data.value i.succ - data.value i.castSucc) / hL +
        hL * (data.value j.succ - data.value i.succ) / hR)

/-- The second left jet of each reconstructed panel. -/
theorem second_left (data : HermiteData panels) (mesh : StrictKnotMesh panels)
    (i : Fin panels) :
    polynomialJet 2 ((data.polynomialData mesh).piece i) (mesh.panelLeft i) =
      6 * (data.value i.succ - data.value i.castSucc) /
          (mesh.panelRight i - mesh.panelLeft i) ^ 2 -
        (4 * data.slope i.castSucc + 2 * data.slope i.succ) /
          (mesh.panelRight i - mesh.panelLeft i) :=
  hermitePolynomial_second_left _ _ _ _ _ _
    (sub_pos.mpr (mesh.panelLeft_lt_panelRight i)).ne'

/-- The second right jet of each reconstructed panel. -/
theorem second_right (data : HermiteData panels) (mesh : StrictKnotMesh panels)
    (i : Fin panels) :
    polynomialJet 2 ((data.polynomialData mesh).piece i) (mesh.panelRight i) =
      6 * (data.value i.castSucc - data.value i.succ) /
          (mesh.panelRight i - mesh.panelLeft i) ^ 2 +
        (2 * data.slope i.castSucc + 4 * data.slope i.succ) /
          (mesh.panelRight i - mesh.panelLeft i) := by
  have hh := (sub_pos.mpr (mesh.panelLeft_lt_panelRight i)).ne'
  simpa [polynomialData] using hermitePolynomial_second_right (mesh.panelLeft i) _
    (data.value i.castSucc) (data.value i.succ)
    (data.slope i.castSucc) (data.slope i.succ) hh

/-- Exact slope equations upgrade the shared value and slope data to a cubic C² spline. -/
def toC2Spline (data : HermiteData panels) (mesh : StrictKnotMesh panels)
    (heq : data.C2SlopeEquations mesh) : PolynomialSpline mesh 3 2 where
  toPolynomialSplineData := data.polynomialData mesh
  matchesJets := by
    intro i hi order horder
    by_cases hone : order ≤ 1
    · exact (data.toSpline mesh).matchesJets i hi order hone
    have htwo : order = 2 := by omega
    subst order
    let j := StrictKnotMesh.rightNeighbor i hi
    have hnode : i.succ = j.castSucc := by
      apply Fin.ext
      rfl
    have hboundary : mesh.panelLeft i + (mesh.panelRight i - mesh.panelLeft i) =
        mesh.panelRight i := by cas
    have hleft : mesh.panelLeft j = mesh.panelRight i :=
      (mesh.panelRight_eq_panelLeft_rightNeighbor i hi).symm
    have hL0 := (sub_pos.mpr (mesh.panelLeft_lt_panelRight i)).ne'
    have hR0 := (sub_pos.mpr (mesh.panelLeft_lt_panelRight j)).ne'
    have hmatch := (hermitePolynomial_second_match_iff (mesh.panelLeft i)
      (mesh.panelRight i - mesh.panelLeft i) (mesh.panelRight j - mesh.panelLeft j)
      (data.value i.castSucc) (data.value i.succ) (data.value j.succ)
      (data.slope i.castSucc) (data.slope i.succ) (data.slope j.succ) hL0 hR0).mpr
      (heq i hi)
    rw [hboundary] at hmatch
    change polynomialJet 2 ((data.polynomialData mesh).piece i) (mesh.panelRight i) =
      polynomialJet 2 ((data.polynomialData mesh).piece j) (mesh.panelRight i)
    simpa only [polynomialData, hnode, hleft] using hmatch

/-- The interior `1, 4, 1` slope equations on an exact uniform mesh of step `h`. -/
def UniformSlopeEquations (data : HermiteData panels) (h : ℝ) : Prop :=
  ∀ (i : Fin panels) (hi : i.val + 1 < panels),
    let j := StrictKnotMesh.rightNeighbor i hi
    data.slope i.castSucc + 4 * data.slope i.succ + data.slope j.succ =
      3 * (data.value j.succ - data.value i.castSucc) / h

/-- Equal exact panel lengths reduce the nonuniform system to the uniform `1, 4, 1` equations. -/
theorem c2SlopeEquations_iff_uniform
    (data : HermiteData panels) (mesh : StrictKnotMesh panels) (h : ℝ)
    (hmesh : ∀ i, mesh.panelRight i - mesh.panelLeft i = h) :
    data.C2SlopeEquations mesh ↔ data.UniformSlopeEquations h := by
  unfold C2SlopeEquations UniformSlopeEquations
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  dsimp only
  rw [hmesh i, hmesh (StrictKnotMesh.rightNeighbor i hi)]
  have hh : h ≠ 0 := by
    rw [← hmesh i]
    exact (sub_pos.mpr (mesh.panelLeft_lt_panelRight i)).ne'
  exact (hermitePolynomial_second_match_iff 0 h h (data.value i.castSucc)
    (data.value i.succ) (data.value (StrictKnotMesh.rightNeighbor i hi).succ)
    (data.slope i.castSucc) (data.slope i.succ)
    (data.slope (StrictKnotMesh.rightNeighbor i hi).succ) hh hh).symm.trans
    (hermitePolynomial_second_match_uniform_iff 0 h (data.value i.castSucc)
      (data.value i.succ) (data.value (StrictKnotMesh.rightNeighbor i hi).succ)
      (data.slope i.castSucc) (data.slope i.succ)
      (data.slope (StrictKnotMesh.rightNeighbor i hi).succ) hh)

/-- A solution of the uniform interior `1, 4, 1` equations certifies a cubic C² spline. -/
def toUniformC2Spline (data : HermiteData panels) (mesh : StrictKnotMesh panels) (h : ℝ)
    (hmesh : ∀ i, mesh.panelRight i - mesh.panelLeft i = h)
    (heq : data.UniformSlopeEquations h) : PolynomialSpline mesh 3 2 :=
  data.toC2Spline mesh ((data.c2SlopeEquations_iff_uniform mesh h hmesh).mpr heq)

/-- The first row `2 m₀ + m₁ = 3 (v₁ - v₀) / h` certifies zero curvature at the first knot. -/
theorem second_origin_eq_zero (data : HermiteData (panels + 1))
    (mesh : StrictKnotMesh (panels + 1))
    (heq : 2 * data.slope 0 + data.slope 1 =
      3 * (data.value 1 - data.value 0) / (mesh.panelRight 0 - mesh.panelLeft 0)) :
    polynomialJet 2 ((data.polynomialData mesh).piece 0) (mesh.panelLeft 0) = 0 :=
  (hermitePolynomial_second_left_eq_zero_iff _ _ _ _ _ _
    (sub_pos.mpr (mesh.panelLeft_lt_panelRight 0)).ne').mpr heq

end HermiteData

end CAS.Splines
