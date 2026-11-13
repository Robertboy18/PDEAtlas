/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import FloatLib.Numerics.Enclosure.Expression.BackendsProof
public import PDE.Analysis.Approximation.Splines.ClosedTensorCells

/-!
# Checked finite covers of radial tensor panels

Rational knot comparisons retain every closed piece that can meet coordinate
intervals. A seam touching an interval endpoint remains possible. Repeated knots
have empty open cells, and the exterior branch is retained unless the coordinate
interval lies strictly inside the finite knot span.

The panel checker evaluates the physical coordinate expressions with fixed exact
parameters, validates the retained piece list, and checks every supplied physical
box contains the whole radial panel. These arithmetic checks imply coverage;
coverage is not an input certificate proposition.
-/

@[expose] public section

namespace CAS.Splines

open FloatLib.Numerics Set

/-- Conservative closed-piece intersection test against an exact rational interval.
The exterior includes both tails; a repeated-knot cell is empty and is rejected. -/
def knotPiecePossible (q : ℕ → ℚ) (count : ℕ) (lo hi : ℚ) : Option (Fin count) → Bool
  | none => decide (lo ≤ q 0 ∨ q count ≤ hi)
  | some i => decide (q i < q (i + 1) ∧ lo ≤ q (i + 1) ∧ q i ≤ hi)

attribute [inherit_doc knotPiecePossible] knotPiecePossible.eq_1 knotPiecePossible.eq_2

/-- Every closed knot piece meeting the interval passes the intersection test. -/
theorem knotPiecePossible_of_mem_closure (q : ℕ → ℚ) (knots : KnotSequence)
    (hknots : ∀ i, knots i = (q i : ℝ)) (count : ℕ)
    (lo hi : ℚ) (piece : Option (Fin count)) {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ))
    (hx : x ∈ closure (knotPiece knots count piece)) :
    knotPiecePossible q count lo hi piece = true := by
  cases piece with
  | none =>
      have hsub : knotPiece knots count none ⊆
          Iic (knots 0) ∪ Ici (knots count) := by
        intro y hy
        change ¬(knots 0 ≤ y ∧ y ≤ knots count) at hy
        change y ≤ knots 0 ∨ knots count ≤ y
        by_cases h : y ≤ knots 0
        · exact Or.inl h
        · exact Or.inr (le_of_not_ge (fun h' ↦ hy ⟨(le_of_not_ge h), h'⟩))
      have hm := closure_minimal hsub (isClosed_Iic.union isClosed_Ici) hx
      change x ≤ knots 0 ∨ knots count ≤ x at hm
      simp only [knotPiecePossible, decide_eq_true_eq]
      rcases hm with hm | hm
      · left
        exact_mod_cast hlo.trans (hm.trans_eq (hknots 0))
      · right
        exact_mod_cast ((hknots count).symm.trans_le hm).trans hhi
  | some i =>
      have hlt : knots i < knots (i + 1) := by
        by_contra h
        have he : knotPiece knots count (some i) = ∅ :=
          Ioo_eq_empty_of_le (le_of_not_gt h)
        simp only [he, closure_empty, mem_empty_iff_false] at hx
      have hm : x ∈ Icc (knots i) (knots (i + 1)) :=
        closure_minimal Ioo_subset_Icc_self isClosed_Icc hx
      simp only [knotPiecePossible, decide_eq_true_eq]
      rw [hknots i, hknots (i + 1)] at hlt hm
      exact ⟨by exact_mod_cast hlt, by exact_mod_cast hlo.trans hm.2,
        by exact_mod_cast hm.1.trans hhi⟩

/-- Check that every triple whose closed coordinate pieces may meet the supplied
radial and axial ranges appears in the retained finite set. -/
def tensorPieceCoverCheck {nx ny : ℕ} (qx qy : ℕ → ℚ)
    (radial axial : Interval ℚ)
    (retained : Finset (Option (Fin nx) × Option (Fin nx) × Option (Fin ny))) : Bool :=
  decide (∀ piece : Option (Fin nx) × Option (Fin nx) × Option (Fin ny),
    (knotPiecePossible qx nx radial.lo radial.hi piece.1 &&
      knotPiecePossible qx nx (-radial.hi) (-radial.lo) piece.2.1 &&
      knotPiecePossible qy ny axial.lo axial.hi piece.2.2) = true →
      piece ∈ retained)

/-- A successful finite check cannot omit any closed reflected piece meeting the
coordinate ranges. Continuity transfers physical closure membership to the knots. -/
theorem tensorPieceCoverCheck_mem_of_mem_closure {nx ny : ℕ}
    (qx qy : ℕ → ℚ) (kx ky : KnotSequence)
    (hxknots : ∀ i, kx i = (qx i : ℝ))
    (hyknots : ∀ i, ky i = (qy i : ℝ))
    (coordinate : ℝ → ℝ) (hcoordinate : Continuous coordinate) (translation : ℝ)
    (radial axial : Interval ℚ)
    (retained : Finset (Option (Fin nx) × Option (Fin nx) × Option (Fin ny)))
    (hcheck : tensorPieceCoverCheck qx qy radial axial retained = true)
    (x : ℝ^2) (hradial : radial.ContainsReal some (coordinate (x 0)))
    (haxial : axial.ContainsReal some (coordinate (x 1 + translation)))
    (positive negative : Option (Fin nx)) (height : Option (Fin ny))
    (hmem : x ∈ closure (reflectedTensorPiece coordinate translation kx ky nx ny
      positive negative height)) : (positive, negative, height) ∈ retained := by
  have hpos : coordinate (x 0) ∈ closure (knotPiece kx nx positive) := by
    apply (show Continuous (fun y : ℝ^2 ↦ coordinate (y 0)) by fun_prop).closure_preimage_subset
    exact closure_mono (fun y hy ↦ hy.1) hmem
  have hneg : -coordinate (x 0) ∈ closure (knotPiece kx nx negative) := by
    apply (show Continuous (fun y : ℝ^2 ↦ -coordinate (y 0)) by fun_prop).closure_preimage_subset
    exact closure_mono (fun y hy ↦ hy.2.1) hmem
  have hheight : coordinate (x 1 + translation) ∈ closure (knotPiece ky ny height) := by
    apply (show Continuous (fun y : ℝ^2 ↦ coordinate (y 1 + translation)) by
      fun_prop).closure_preimage_subset
    exact closure_mono (fun y hy ↦ hy.2.2) hmem
  rw [Interval.containsReal_some_iff] at hradial haxial
  have hp := knotPiecePossible_of_mem_closure qx kx hxknots nx _ _ _
    hradial.1 hradial.2 hpos
  have hn := knotPiecePossible_of_mem_closure qx kx hxknots nx
    (-radial.hi) (-radial.lo) negative
    (by simpa only [Rat.cast_neg] using neg_le_neg hradial.2)
    (by simpa only [Rat.cast_neg] using neg_le_neg hradial.1) hneg
  have ha := knotPiecePossible_of_mem_closure qy ky hyknots ny _ _ _
    haxial.1 haxial.2 hheight
  exact (of_decide_eq_true hcheck) (positive, negative, height)
    (by simpa only [Bool.and_eq_true] using And.intro (And.intro hp hn) ha)

/-- The checked retained pieces cover every physical point in the coordinate ranges,
including seams and exterior points. The full closed cover supplies the witness. -/
theorem tensorPieceCoverCheck_covers {nx ny : ℕ}
    (qx qy : ℕ → ℚ) (kx ky : KnotSequence)
    (hxknots : ∀ i, kx i = (qx i : ℝ))
    (hyknots : ∀ i, ky i = (qy i : ℝ))
    (coordinate : ℝ → ℝ) (hcoordinate : Continuous coordinate)
    (hinjective : Function.Injective coordinate) (translation : ℝ)
    (radial axial : Interval ℚ)
    (retained : Finset (Option (Fin nx) × Option (Fin nx) × Option (Fin ny)))
    (hcheck : tensorPieceCoverCheck qx qy radial axial retained = true)
    (x : ℝ^2) (hradial : radial.ContainsReal some (coordinate (x 0)))
    (haxial : axial.ContainsReal some (coordinate (x 1 + translation))) :
    ∃ piece ∈ retained, x ∈ closure (reflectedTensorPiece coordinate translation kx ky nx ny
      piece.1 piece.2.1 piece.2.2) := by
  obtain ⟨positive, negative, height, hm⟩ :=
    exists_mem_closure_reflectedTensorPiece coordinate hinjective translation kx ky nx ny x
  exact ⟨(positive, negative, height), tensorPieceCoverCheck_mem_of_mem_closure
    qx qy kx ky hxknots hyknots coordinate hcoordinate translation radial axial retained
      hcheck x hradial haxial positive negative height hm, hm⟩

/-- Enclose the entire radial panel by interval multiplication, leaving its axial
coordinate unchanged. A reversed panel is rejected. -/
def radialPanelBox? (a b : ℚ) (input : Fin 2 → Interval ℚ) :
    Option (Fin 2 → Interval ℚ) :=
  if a ≤ b then do
    let radial ← Interval.mul? Interval.Internal.rationalOutwardRounding ⟨a, b⟩ (input 0)
    pure ![radial, input 1]
  else none

/-- Successful panel construction encloses every physical point on the panel. -/
theorem radialPanelBox?_sound (a b : ℚ) (input panel : Fin 2 → Interval ℚ)
    (hcheck : radialPanelBox? a b input = some panel)
    (x : ℝ^2) (hx : ∀ i, (input i).ContainsReal some (x i))
    (t : ℝ) (ht : t ∈ Icc (a : ℝ) (b : ℝ)) (i : Fin 2) :
    (panel i).ContainsReal some
      ((EuclideanSpace.single 0 (t * x 0) + EuclideanSpace.single 1 (x 1) : ℝ^2) i) := by
  unfold radialPanelBox? at hcheck
  split at hcheck
  · cases hradial :
        Interval.mul? Interval.Internal.rationalOutwardRounding ⟨a, b⟩ (input 0) with
    | none => simp [hradial] at hcheck
    | some radial =>
        have heq : ![radial, input 1] = panel := by simpa [hradial] using hcheck
        subst panel
        fin_cases i
        · have htime : (⟨a, b⟩ : Interval ℚ).ContainsReal some t :=
            (Interval.containsReal_some_iff _ _).mpr ht
          simpa [Interval.Internal.rationalOutwardRounding] using
            Interval.containsReal_mul? Interval.Internal.rationalOutwardRounding
              hradial htime (hx 0)
        · simpa using hx 1
  · contradiction

/-- Exact endpoint comparison checks inclusion of physical boxes. -/
def boxContainsCheck (outer inner : Fin 2 → Interval ℚ) : Bool :=
  decide (∀ i, (outer i).lo ≤ (inner i).lo ∧ (inner i).hi ≤ (outer i).hi)

/-- A checked box inclusion preserves every enclosed physical coordinate. -/
theorem boxContainsCheck_sound (outer inner : Fin 2 → Interval ℚ)
    (hcheck : boxContainsCheck outer inner = true) (i : Fin 2) {x : ℝ}
    (hx : (inner i).ContainsReal some x) : (outer i).ContainsReal some x := by
  have h := (of_decide_eq_true hcheck) i
  rw [Interval.containsReal_some_iff] at hx ⊢
  have hlo : ((outer i).lo : ℝ) ≤ (inner i).lo := by exact_mod_cast h.1
  have hhi : ((inner i).hi : ℝ) ≤ (outer i).hi := by exact_mod_cast h.2
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

/--
Validate the finite cover and every retained branch's physical box.

The supplied FloatLib expressions use physical coordinates `0, 1`, followed by
the parameter coordinates. Each branch box must contain the whole radial panel;
conditional smaller boxes require additional geometry.
-/
def tensorPanelCoverCheck {nx ny p : ℕ} (config : Interval.Backend.Config)
    (qx qy : ℕ → ℚ) (a b : ℚ) (input : Fin 2 → Interval ℚ)
    (parameterBox : Fin p → Interval ℚ)
    (coordinateExpr : Fin 2 → Interval.Expr)
    (retained : Finset (Option (Fin nx) × Option (Fin nx) × Option (Fin ny)))
    (physicalBox :
      Option (Fin nx) × Option (Fin nx) × Option (Fin ny) → Fin 2 → Interval ℚ) : Bool :=
  match radialPanelBox? a b input with
  | none => false
  | some panel =>
    let env := fun i ↦ if h : i < 2 + p then some (Fin.append panel parameterBox ⟨i, h⟩)
      else none
    match (coordinateExpr 0).eval? (Interval.Backend.rational config) env,
        (coordinateExpr 1).eval? (Interval.Backend.rational config) env with
    | some radial, some axial =>
      tensorPieceCoverCheck qx qy radial axial retained &&
        decide (∀ piece ∈ retained, boxContainsCheck (physicalBox piece) panel = true)
    | _, _ => false

attribute [inherit_doc tensorPanelCoverCheck] tensorPanelCoverCheck.eq_1

/--
Successful FloatLib evaluations and finite checks give a closed cover and valid
physical boxes throughout the radial panel.

The coordinate identity and input containment are mathematical premises.
Coverage, including omitted-piece safety at seams, follows from the finite check.
-/
theorem tensorPanelCoverCheck_sound {nx ny p : ℕ} (config : Interval.Backend.Config)
    (qx qy : ℕ → ℚ) (kx ky : KnotSequence)
    (hxknots : ∀ i, kx i = (qx i : ℝ))
    (hyknots : ∀ i, ky i = (qy i : ℝ))
    (coordinate : ℝ → ℝ) (hcoordinate : Continuous coordinate)
    (hinjective : Function.Injective coordinate) (translation : ℝ)
    (a b : ℚ) (input : Fin 2 → Interval ℚ) (parameterBox : Fin p → Interval ℚ)
    (coordinateExpr : Fin 2 → Interval.Expr) (parameters : Fin p → ℝ)
    (hmap : ∀ y : ℝ^2, ∀ i, (coordinateExpr i).eval
        (fun j ↦ if h : j < 2 + p then Fin.append (fun k ↦ y k) parameters ⟨j, h⟩ else 0) =
      ![coordinate (y 0), coordinate (y 1 + translation)] i)
    (retained : Finset (Option (Fin nx) × Option (Fin nx) × Option (Fin ny)))
    (physicalBox :
      Option (Fin nx) × Option (Fin nx) × Option (Fin ny) → Fin 2 → Interval ℚ)
    (hcheck : tensorPanelCoverCheck config qx qy a b input parameterBox coordinateExpr
      retained physicalBox = true)
    (x : ℝ^2) (hx : ∀ i, (input i).ContainsReal some (x i))
    (hparameters : ∀ i, (parameterBox i).ContainsReal some (parameters i))
    (t : ℝ) (ht : t ∈ Icc (a : ℝ) (b : ℝ)) :
    (∃ piece ∈ retained,
      EuclideanSpace.single 0 (t * x 0) + EuclideanSpace.single 1 (x 1) ∈
        closure (reflectedTensorPiece coordinate translation kx ky nx ny
          piece.1 piece.2.1 piece.2.2)) ∧
    ∀ piece ∈ retained, ∀ i, (physicalBox piece i).ContainsReal some
      ((EuclideanSpace.single 0 (t * x 0) + EuclideanSpace.single 1 (x 1) : ℝ^2) i) := by
  cases hp : radialPanelBox? a b input with
  | none => simp [tensorPanelCoverCheck, hp] at hcheck
  | some panel =>
      simp only [tensorPanelCoverCheck, hp] at hcheck
      let env := fun i ↦
        if h : i < 2 + p then some (Fin.append panel parameterBox ⟨i, h⟩) else none
      change (match (coordinateExpr 0).eval? (Interval.Backend.rational config) env,
          (coordinateExpr 1).eval? (Interval.Backend.rational config) env with
        | some radial, some axial =>
          tensorPieceCoverCheck qx qy radial axial retained &&
            decide (∀ piece ∈ retained, boxContainsCheck (physicalBox piece) panel = true)
        | _, _ => false) = true at hcheck
      cases hr : (coordinateExpr 0).eval? (Interval.Backend.rational config) env with
      | none => simp [hr] at hcheck
      | some radial =>
          cases ha : (coordinateExpr 1).eval? (Interval.Backend.rational config) env with
          | none => simp [hr, ha] at hcheck
          | some axial =>
              simp only [hr, ha, Bool.and_eq_true, decide_eq_true_eq] at hcheck
              let y : ℝ^2 :=
                EuclideanSpace.single 0 (t * x 0) + EuclideanSpace.single 1 (x 1)
              let values := fun j ↦
                if h : j < 2 + p then Fin.append (fun k ↦ y k) parameters ⟨j, h⟩ else 0
              have hy : ∀ i, (panel i).ContainsReal some (y i) :=
                radialPanelBox?_sound a b input panel hp x hx t ht
              have henv : ∀ i I, env i = some I → I.ContainsReal some (values i) := by
                intro i I hi
                dsimp only [env] at hi
                split at hi
                next h =>
                  cases hi
                  dsimp only [values]
                  rw [dite_eq_left h]
                  generalize hk : (⟨i, h⟩ : Fin (2 + p)) = k
                  cases k using Fin.addCases with
                  | left k => simpa using hy k
                  | right k => simpa using hparameters k
                next h => contradiction
              have hradial : radial.ContainsReal some (coordinate (y 0)) := by
                have h := (coordinateExpr 0).containsReal_eval?
                  (Interval.Backend.rational_sound config) henv hr
                simpa only [Interval.Backend.rational, Interval.Backend.ofRounding,
                  Interval.Internal.rationalOutwardRounding, values, hmap,
                  Matrix.cons_val_zero] using h
              have haxial : axial.ContainsReal some (coordinate (y 1 + translation)) := by
                have h := (coordinateExpr 1).containsReal_eval?
                  (Interval.Backend.rational_sound config) henv ha
                simpa only [Interval.Backend.rational, Interval.Backend.ofRounding,
                  Interval.Internal.rationalOutwardRounding, values, hmap,
                  Matrix.cons_val_one, Matrix.cons_val_zero] using h
              refine ⟨tensorPieceCoverCheck_covers qx qy kx ky hxknots hyknots coordinate
                hcoordinate hinjective translation radial axial retained hcheck.1 y
                hradial haxial, ?_⟩
              intro piece hm i
              exact boxContainsCheck_sound _ _ (hcheck.2 piece hm) i (hy i)

end CAS.Splines
