/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.NormalizedBasis
import CAS.ExactTactic

/-!
# Finite Bernstein certificates for polynomial nonnegativity

A polynomial identity after an affine change of variable, together with
finitely many nonnegative Bernstein controls, certifies the entire closed
cell. The certificate does not contain a pointwise nonnegativity assumption.
-/

@[expose] public section

noncomputable section

open Set Polynomial
open scoped BigOperators

namespace CAS.Splines

/-- A polynomial Bernstein identity and finitely many control signs certify a closed cell. -/
theorem eval_nonneg_of_bernstein_identity {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (n : ℕ) (controls : Fin (n + 1) → ℝ)
    (hidentity : p.comp (C a + C (b - a) * X) =
      ∑ i : Fin (n + 1), C (controls i) * bernsteinPolynomial ℝ n i)
    (hcontrols : ∀ i, 0 ≤ controls i) {x : ℝ} (hx : x ∈ Icc a b) :
    0 ≤ p.eval x := by
  have hz : panelCoordinate a b x ∈ Icc (0 : ℝ) 1 :=
    ⟨panelCoordinate_nonneg hab hx.1, panelCoordinate_le_one hab hx.2⟩
  have heval := congrArg (fun q : ℝ[X] ↦ q.eval (panelCoordinate a b x)) hidentity
  simp only [eval_comp, eval_add, eval_C, eval_mul, eval_X, eval_finsetSum] at heval
  conv_lhs at heval =>
    arg 1
    unfold panelCoordinate
    cas_nf using (sub_pos.mpr hab).ne'
  rw [heval]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hcontrols i)
    (bernsteinPolynomial_eval_nonneg n i hz.1 hz.2)

/-- Finite certificate data: one polynomial identity and a finite list of nonnegative controls. -/
def HasNonnegativeBernsteinCertificate (p : ℝ[X]) (a b : ℝ) : Prop :=
  ∃ (n : ℕ) (controls : Fin (n + 1) → ℝ),
    p.comp (C a + C (b - a) * X) =
      ∑ i : Fin (n + 1), C (controls i) * bernsteinPolynomial ℝ n i ∧
    ∀ i, 0 ≤ controls i

/-- Finite Bernstein certificates imply nonnegativity everywhere in their closed cell. -/
theorem HasNonnegativeBernsteinCertificate.nonneg
    {p : ℝ[X]} {a b : ℝ} (h : HasNonnegativeBernsteinCertificate p a b)
    (hab : a < b) {x : ℝ} (hx : x ∈ Icc a b) : 0 ≤ p.eval x := by
  obtain ⟨n, controls, hidentity, hcontrols⟩ := h
  exact eval_nonneg_of_bernstein_identity hab n controls hidentity hcontrols hx

end CAS.Splines
