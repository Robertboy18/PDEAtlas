/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.HornerJets
public import PDE.Analysis.Approximation.Splines.PolynomialBranchGluing

/-!
# Spline regularity from checked polynomial jets

Checked coefficient conversion identifies both adjacent Cox–de Boor branches.
Exact jet comparison then applies the polynomial-spline gluing theorem.
The resulting regularity transfers to the basis on the open union of the
neighboring cells, including their shared knot. The cells may have nonconsecutive
indices: repeated knots can separate the two nonempty cells by zero-width cells.
-/

@[expose] public section
namespace CAS.Splines
open CAS.Polynomial Set

/-- Exact matching jets make the two Horner polynomial branches continuously differentiable. -/
theorem contDiff_if_hornerJetMatch (left right : List ℚ) (cut : ℚ) (smoothness : ℕ)
    (hmatch : ∀ k ≤ smoothness, hornerJetMatchCheck left right cut k = true) :
    ContDiff ℝ smoothness (fun x : ℝ ↦ if x ≤ (cut : ℝ) then
      listHornerEval x (left.map Rat.cast) else listHornerEval x (right.map Rat.cast)) := by
  have hzero := hmatch 0 (Nat.zero_le _)
  unfold hornerJetMatchCheck at hzero
  cases hl : hornerPolynomial? left with
  | none => simp [hl] at hzero
  | some a =>
      cases hr : hornerPolynomial? right with
      | none => simp [hr] at hzero
      | some b =>
          have hleft : (fun x : ℝ ↦ listHornerEval x (left.map Rat.cast)) =
              Sparse.evalReal a := funext fun x ↦ (hornerPolynomial?_eval left a hl x).symm
          have hright : (fun x : ℝ ↦ listHornerEval x (right.map Rat.cast)) =
              Sparse.evalReal b := funext fun x ↦ (hornerPolynomial?_eval right b hr x).symm
          have hjets : ∀ k ≤ smoothness,
              iteratedDeriv k (Sparse.evalReal a) (cut : ℝ) =
                iteratedDeriv k (Sparse.evalReal b) (cut : ℝ) := by
            intro k hk
            simpa only [hleft, hright] using
              hornerJetMatchCheck_sound left right cut k (hmatch k hk)
          have h := contDiff_if_sparse_iteratedDeriv_eq a b cut smoothness hjets
          simpa only [← hleft, ← hright] using h

/-- Exact polynomial data for a finite family of basis functions across a knot.
The certificate contains branch conversion and jet checks, not analytic regularity.
The two cells share an endpoint even when repeated knots separate their indices. -/
structure CoxDeBoorJetCertificate (q : ℕ → ℚ)
    (leftCell rightCell degree count smoothness : ℕ) where
  /-- The right endpoint of the left cell is the left endpoint of the right cell. -/
  shared_knot : q (leftCell + 1) = q rightCell
  /-- Horner coefficients on the left cell. -/
  left : Fin count → List ℚ
  /-- Horner coefficients on the right cell. -/
  right : Fin count → List ℚ
  /-- Exact conversion from the left Cox–de Boor branch. -/
  left_checked : ∀ i, branchHornerCheck q leftCell degree i.val 0 (left i) = true
  /-- Exact conversion from the right Cox–de Boor branch. -/
  right_checked : ∀ i, branchHornerCheck q rightCell degree i.val 0 (right i) = true
  /-- Equality of branch derivatives through the requested order at the shared knot. -/
  jets_match : ∀ i k, k ≤ smoothness →
    hornerJetMatchCheck (left i) (right i) (q rightCell) k = true

/-- Checked branch coefficients and jets prove finite regularity of the basis,
including the shared knot. No value equality or smoothness of the basis is assumed. -/
theorem CoxDeBoorJetCertificate.contDiffAt_basis
    {q : ℕ → ℚ} {leftCell rightCell degree count smoothness : ℕ}
    (cert : CoxDeBoorJetCertificate q leftCell rightCell degree count smoothness)
    (knots : KnotSequence) (hknots : ∀ i, knots i = (q i : ℝ))
    (i : Fin count) (n : ℕ) (hn : n ≤ smoothness)
    {x : ℝ} (hx : x ∈ Ioo (knots leftCell) (knots (rightCell + 1))) :
    ContDiffAt ℝ n (coxDeBoorBasis knots degree i.val) x := by
  let left := cert.left i
  let right := cert.right i
  have hcut : knots (leftCell + 1) = knots rightCell := by
    simp only [hknots, cert.shared_knot]
  have hmatch (k : ℕ) (hk : k ≤ n) :
      hornerJetMatchCheck left right (q rightCell) k = true :=
    cert.jets_match i k (hk.trans hn)
  have hevalLeft (y : ℝ) : listHornerEval y (left.map Rat.cast) =
      coxDeBoorBranch knots leftCell degree i.val y := by
    simpa using branchHornerCheck_sound q knots hknots leftCell degree i.val 0
      left (cert.left_checked i) y
  have hevalRight (y : ℝ) : listHornerEval y (right.map Rat.cast) =
      coxDeBoorBranch knots rightCell degree i.val y := by
    simpa using branchHornerCheck_sound q knots hknots rightCell degree i.val 0
      right (cert.right_checked i) y
  have hvalues : listHornerEval (knots rightCell) (left.map Rat.cast) =
      listHornerEval (knots rightCell) (right.map Rat.cast) := by
    simpa only [iteratedDeriv_zero, hknots] using
      hornerJetMatchCheck_sound left right (q rightCell) 0 (hmatch 0 (Nat.zero_le _))
  have hregular :=
    (contDiff_if_hornerJetMatch left right (q rightCell) n hmatch).contDiffAt (x := x)
  apply hregular.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  rw [← hknots rightCell]
  rcases lt_trichotomy y (knots rightCell) with hlt | heq | hgt
  · simp only [ite_eq_left hlt.le]
    exact (coxDeBoorBasis_eq_branch knots leftCell degree i.val
      ⟨hy.1.le, hcut ▸ hlt⟩).trans (hevalLeft y).symm
  · subst y
    simp only [le_refl, ite_true]
    exact (coxDeBoorBasis_eq_branch knots rightCell degree i.val ⟨le_rfl, hy.2⟩).trans
        ((hevalRight _).symm.trans hvalues.symm)
  · simp only [ite_eq_right (not_le_of_gt hgt)]
    exact (coxDeBoorBasis_eq_branch knots rightCell degree i.val ⟨hgt.le, hy.2⟩).trans
      (hevalRight y).symm

end CAS.Splines
