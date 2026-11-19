/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Analysis.Approximation.Splines.PiecewisePolynomial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Assembling a polynomial spline on its whole mesh

The assembled evaluator starts with the first panel polynomial and adds the change
at each successive knot. Each change is the adjacent evaluator minus its left
polynomial. Thus matching jets through order `k` makes the finite sum `C^k`.
On each closed panel the corrections telescope to that panel's polynomial.

The first and last polynomials extend beyond the knot interval. An empty mesh has
the zero evaluator. The construction uses only the polynomial pieces and their
matching jets.
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators Polynomial

namespace CAS.Splines

namespace StrictKnotMesh

/-- Every point between the outer knots of a nonempty mesh belongs to a closed panel. -/
theorem exists_mem_panel_of_mem_Icc
    {panels : ℕ} (mesh : StrictKnotMesh panels) (hpanels : 0 < panels) {x : ℝ}
    (hx : x ∈ Icc (mesh.knot 0) (mesh.knot (Fin.last panels))) :
    ∃ panel : Fin panels, x ∈ Icc (mesh.panelLeft panel) (mesh.panelRight panel) := by
  classical
  cases panels with
  | zero => omega
  | succ n =>
      let candidates := Finset.univ.filter (fun p : Fin (n + 1) ↦ x ≤ mesh.panelRight p)
      have hnonempty : candidates.Nonempty := by
        refine ⟨Fin.last n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        exact hx.2
      obtain ⟨panel, hmem, hmin⟩ := Finset.exists_min_image candidates id hnonempty
      refine ⟨panel, ?_, (Finset.mem_filter.mp hmem).2⟩
      by_cases hp : panel.val = 0
      · have heq : panel.castSucc = 0 := Fin.ext hp
        simpa only [panelLeft, heq] using hx.1
      · let prev : Fin (n + 1) := ⟨panel.val - 1, by omega⟩
        have hprev : mesh.panelRight prev = mesh.panelLeft panel := by
          apply congrArg mesh.knot
          apply Fin.ext
          change panel.val - 1 + 1 = panel.val
          omega
        by_contra hleft
        have hprevmem : prev ∈ candidates := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [hprev]
          exact (lt_of_not_ge hleft).le
        have horder := hmin prev hprevmem
        change panel.val ≤ panel.val - 1 at horder
        omega

end StrictKnotMesh

private theorem sum_differences_before
    {n : ℕ} (values : Fin (n + 1) → ℝ) (panel : Fin (n + 1)) :
    values 0 + ∑ i : Fin n,
      (if i.val < panel.val then values i.succ - values i.castSucc else 0) =
        values panel := by
  induction n with
  | zero =>
      have hp : panel = 0 := by apply Fin.ext; omega
      simp [hp]
  | succ n ih =>
      refine Fin.cases ?_ (fun panel ↦ ?_) panel
      · simp
      · have h := ih (fun i ↦ values i.succ) panel
        have hzero : (0 : Fin (n + 1)).castSucc = 0 := rfl
        have hswap (i : Fin n) : i.succ.castSucc = i.castSucc.succ := rfl
        simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ,
          ite_true, Nat.add_lt_add_iff_right, hzero, hswap] at *
        convert h using 1
        abel

namespace PolynomialSplineData

/-- Assemble all panels by adding the polynomial changes at successive knots.
The outside tails continue the first and last polynomials; no-panel data evaluates to zero. -/
def assembledEvaluator {degree : ℕ} :
    {panels : ℕ} → {mesh : StrictKnotMesh panels} →
      PolynomialSplineData mesh degree → ℝ → ℝ
  | 0, _, _, _ => 0
  | n + 1, _, data, x =>
      (data.piece 0).eval x + ∑ i : Fin n,
        (data.adjacentEvaluator i.castSucc (Nat.succ_lt_succ i.isLt) x -
          (data.piece i.castSucc).eval x)

variable {panels degree smoothness : ℕ} {mesh : StrictKnotMesh panels}

private theorem adjacent_correction_eq
    {n : ℕ} {mesh : StrictKnotMesh (n + 1)}
    {data : PolynomialSplineData mesh degree}
    (hmatch : data.MatchesJetsThrough smoothness)
    (panel : Fin (n + 1)) (i : Fin n) {x : ℝ}
    (hx : x ∈ Icc (mesh.panelLeft panel) (mesh.panelRight panel)) :
    data.adjacentEvaluator i.castSucc (Nat.succ_lt_succ i.isLt) x -
        (data.piece i.castSucc).eval x =
      if i.val < panel.val then
        (data.piece i.succ).eval x - (data.piece i.castSucc).eval x else 0 := by
  have hneighbor :
      StrictKnotMesh.rightNeighbor i.castSucc (Nat.succ_lt_succ i.isLt) = i.succ := rfl
  by_cases hi : i.val < panel.val
  · have hleft : mesh.panelRight i.castSucc ≤ mesh.panelLeft panel := by
      apply mesh.strictMono_knot.monotone
      change i.val + 1 ≤ panel.val
      omega
    have hcut : mesh.panelRight i.castSucc ≤ x := hleft.trans hx.1
    by_cases hle : x ≤ mesh.panelRight i.castSucc
    · have heq : x = mesh.panelRight i.castSucc := le_antisymm hle hcut
      have hvalue := data.value_eq_of_matchesJetsThrough hmatch i.castSucc
        (Nat.succ_lt_succ i.isLt)
      simp only [hneighbor] at hvalue
      simp [adjacentEvaluator, hi, heq, Polynomial.aeval_def,
        Algebra.algebraMap_self, Polynomial.eval₂_id, hvalue]
    · simp [adjacentEvaluator, hi, hle, hneighbor, Polynomial.aeval_def,
        Algebra.algebraMap_self, Polynomial.eval₂_id]
  · have hright : mesh.panelRight panel ≤ mesh.panelRight i.castSucc := by
      apply mesh.strictMono_knot.monotone
      change panel.val + 1 ≤ i.val + 1
      omega
    have hle : x ≤ mesh.panelRight i.castSucc := hx.2.trans hright
    simp [adjacentEvaluator, hi, hle, Polynomial.aeval_def,
      Algebra.algebraMap_self, Polynomial.eval₂_id]

/-- The assembled function evaluates the polynomial on every closed panel.
At a shared endpoint both neighboring formulas agree by their zeroth matched jet. -/
theorem assembledEvaluator_eq_piece
    {data : PolynomialSplineData mesh degree}
    (hmatch : data.MatchesJetsThrough smoothness)
    (panel : Fin panels) {x : ℝ}
    (hx : x ∈ Icc (mesh.panelLeft panel) (mesh.panelRight panel)) :
    data.assembledEvaluator x = (data.piece panel).eval x := by
  cases panels with
  | zero => exact Fin.elim0 panel
  | succ n =>
      change (data.piece 0).eval x + ∑ i : Fin n,
        (data.adjacentEvaluator i.castSucc (Nat.succ_lt_succ i.isLt) x -
          (data.piece i.castSucc).eval x) = (data.piece panel).eval x
      simp_rw [adjacent_correction_eq hmatch panel _ hx]
      exact sum_differences_before (fun i ↦ (data.piece i).eval x) panel

/-- Matched jets assemble into a globally `C^smoothness` function, including every knot.
The polynomial tails also give ordinary two-sided regularity at the outer endpoints. -/
theorem contDiff_assembledEvaluator
    {data : PolynomialSplineData mesh degree}
    (hmatch : data.MatchesJetsThrough smoothness) :
    ContDiff ℝ smoothness data.assembledEvaluator := by
  have hpoly (p : ℝ[X]) : ContDiff ℝ smoothness p.eval := by
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using
      p.contDiff_aeval (𝕜 := ℝ) smoothness
  cases panels with
  | zero =>
      exact contDiff_const
  | succ n =>
      change ContDiff ℝ smoothness (fun x ↦
        (data.piece 0).eval x + ∑ i : Fin n,
          (data.adjacentEvaluator i.castSucc (Nat.succ_lt_succ i.isLt) x -
            (data.piece i.castSucc).eval x))
      apply (hpoly (data.piece 0)).add
      apply ContDiff.sum
      intro i _
      exact (data.contDiff_adjacentEvaluator hmatch i.castSucc (Nat.succ_lt_succ i.isLt)).sub
        (hpoly (data.piece i.castSucc))

/-- Regularity on the entire closed knot interval, including every interior junction. -/
theorem contDiffOn_assembledEvaluator
    {data : PolynomialSplineData mesh degree}
    (hmatch : data.MatchesJetsThrough smoothness) :
    ContDiffOn ℝ smoothness data.assembledEvaluator
      (Icc (mesh.knot 0) (mesh.knot (Fin.last panels))) :=
  (data.contDiff_assembledEvaluator hmatch).contDiffOn

/-- On the whole knot interval of a nonempty mesh, assembly selects a containing panel
and evaluates that panel's polynomial. -/
theorem exists_panel_assembledEvaluator_eq
    {data : PolynomialSplineData mesh degree}
    (hmatch : data.MatchesJetsThrough smoothness)
    (hpanels : 0 < panels) {x : ℝ}
    (hx : x ∈ Icc (mesh.knot 0) (mesh.knot (Fin.last panels))) :
    ∃ panel : Fin panels,
      x ∈ Icc (mesh.panelLeft panel) (mesh.panelRight panel) ∧
        data.assembledEvaluator x = (data.piece panel).eval x := by
  obtain ⟨panel, hpanel⟩ := mesh.exists_mem_panel_of_mem_Icc hpanels hx
  exact ⟨panel, hpanel, data.assembledEvaluator_eq_piece hmatch panel hpanel⟩

end PolynomialSplineData

namespace PolynomialSpline

variable {panels degree smoothness : ℕ} {mesh : StrictKnotMesh panels}

/-- The assembled evaluator of a spline with certified matching jets. -/
def assembledEvaluator (spline : PolynomialSpline mesh degree smoothness) : ℝ → ℝ :=
  spline.toPolynomialSplineData.assembledEvaluator

/-- A bundled spline evaluates its own polynomial on each closed panel. -/
theorem assembledEvaluator_eq_piece
    (spline : PolynomialSpline mesh degree smoothness) (panel : Fin panels) {x : ℝ}
    (hx : x ∈ Icc (mesh.panelLeft panel) (mesh.panelRight panel)) :
    spline.assembledEvaluator x = (spline.piece panel).eval x :=
  spline.toPolynomialSplineData.assembledEvaluator_eq_piece spline.matchesJets panel hx

/-- A bundled spline assembles into a globally smooth function. -/
theorem contDiff_assembledEvaluator (spline : PolynomialSpline mesh degree smoothness) :
    ContDiff ℝ smoothness spline.assembledEvaluator :=
  spline.toPolynomialSplineData.contDiff_assembledEvaluator spline.matchesJets

/-- In particular, the assembled spline is smooth on the entire closed mesh interval. -/
theorem contDiffOn_assembledEvaluator (spline : PolynomialSpline mesh degree smoothness) :
    ContDiffOn ℝ smoothness spline.assembledEvaluator
      (Icc (mesh.knot 0) (mesh.knot (Fin.last panels))) :=
  spline.contDiff_assembledEvaluator.contDiffOn

end PolynomialSpline

end CAS.Splines
