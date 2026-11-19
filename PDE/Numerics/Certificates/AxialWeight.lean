/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.AxialPowerCells

/-!
# Axial-radial weights with comonotone exponents on cells

An `AxialWeight` is a weight `w(x) = ∑ c_k |x₀|^{a_k} |x|^{b_k}` with rational data, `c_k ≥ 0`,
and axial exponents `a_k` and degrees `a_k + b_k` that are comonotone with the normalized polar
exponents of `PDE.Numerics.Certificates.AxialPowerCells`. For such a weight the mean degree
`Γ = x·∇w/w` and the mean axial exponent `B` are increasing in `W = x₀²/|x|²` and in `R = |x|²`,
so on a rectangle of the closed quadrant (`PlaneCell`) they lie between their values at the polar
corners `(W₋, R₋)` and `(W₊, R₊)`. The energy weights of Chen and Hou (Part I, Appendix C.1,
(C.2)-(C.4)) are of this form: their terms with the factor `|x₀|^{-1/2}` are exactly those of the
lowest degrees.

## Main definitions

* `AxialWeight`: a weight with nonnegative coefficients and comonotone axial exponents and degrees.
* `CellRates`, `AxialWeight.cellRates`: the cell bounds of `Γ`, `B`, `x₀ ∂₀w/w` and `x₁ ∂₁w/w`,
  with the check that the polar masses at both corners are positive.
* `AxialWeight.cellMean`: cell bounds of the mean of any statistic of the terms, from masses that
  are bounded termwise on the cell.
* `degreeTermsLower`, `radialTermsUpper`, `degreeTermsUpper`: bounds of a weight through the
  radius alone.
* `transverseNormRateBounds`: bounds of `|x| ∂₁w/w`.

## Main results

* `AxialWeight.degreeRate_mem`, `AxialWeight.axialRate_mem`, `AxialWeight.transverseRate_mem`: on
  a cell with valid rates, `x·∇w/w`, `x₀ ∂₀w/w` and `x₁ ∂₁w/w` lie in the bounds of `cellRates`.
* `AxialWeight.cellRates_valid_of_min`: the rates are valid when one term attains both minima.
* `AxialWeight.cellMean_mem`: the mean of a statistic lies in `cellMean`.
* `AxialWeight.abs_mul_le_of_vanishing`: if `|F| ≤ |x₀|^p |x|^q T` at a point of a cell, then
  `|F| w(x) ≤ u T` with `u` the cell upper bound of the shifted weight.
* `AxialWeight.div_le_of_shift`, `AxialWeight.div_le_mul_of_shift`: cell bounds of a quotient of
  two weights after a shift of the exponents.
* `AxialWeight.normTransverseRate_mem`: `|x| ∂₁w/w` lies in `transverseNormRateBounds`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Appendix C.1,
  (C.2)-(C.4).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

namespace CAS.Numerics

open PDE.Analysis
open CAS.Continuum.RationalInterval (roundDownRel roundUpRel roundDownRel_le le_roundUpRel)

/-! ### Weights with comonotone exponents -/

/-- A weight given by terms with nonnegative coefficients whose axial exponents and degrees are
comonotone, with lower bounds of the axial exponents and of the degrees (in practice their minima)
used to normalize the polar masses. -/
structure AxialWeight where
  /-- The terms. -/
  terms : List AxialTerm
  /-- A lower bound of the axial exponents. -/
  axialMin : ℚ
  /-- A lower bound of the degrees. -/
  degreeMin : ℚ
  /-- The coefficients are nonnegative. -/
  nonneg : AxialTerm.NonnegCoeff terms
  /-- `axialMin` is below every axial exponent. -/
  axialMin_le : ∀ t ∈ terms, axialMin ≤ t.axial
  /-- `degreeMin` is below every degree. -/
  degreeMin_le : ∀ t ∈ terms, degreeMin ≤ t.degree
  /-- The degree is comonotone with the axial exponent and the degree. -/
  degree_comonotone : IsComonotone terms AxialTerm.degree
  /-- The axial exponent is comonotone with the axial exponent and the degree. -/
  axial_comonotone : IsComonotone terms AxialTerm.axial

/-- The cell bounds of the log-derivatives of a weight: the mean degree `Γ = x·∇w/w`, the mean
axial exponent `B`, `x₀ ∂₀w/w` and `x₁ ∂₁w/w`, and the check that they are valid. -/
structure CellRates where
  /-- Bounds of `Γ = x·∇w/w`. -/
  degree : ℚ × ℚ
  /-- Bounds of the mean axial exponent `B`. -/
  axial : ℚ × ℚ
  /-- Bounds of `x₀ ∂₀w/w`. -/
  axialRate : ℚ × ℚ
  /-- Bounds of `x₁ ∂₁w/w`. -/
  transverseRate : ℚ × ℚ
  /-- The polar masses at both corners are bounded below by a positive number. -/
  valid : Bool

namespace AxialWeight

variable (w : AxialWeight)

/-- The value of the weight. -/
noncomputable def value : EuclideanSpace ℝ (Fin 2) → ℝ := axialTermsValue w.terms

/-- The rates of the weight on a cell, from the masses at the two polar corners, each computed
once. -/
def cellRates (C : PlaneCell) (bits : ℕ) : CellRates :=
  let lo := massList w.terms w.axialMin w.degreeMin C.directionLower (C.radiusLower bits) bits
  let hi := massList w.terms w.axialMin w.degreeMin C.directionUpper (C.radiusUpper bits) bits
  let g := ((meanBoundsOf lo AxialTerm.degree).1, (meanBoundsOf hi AxialTerm.degree).2)
  let b := ((meanBoundsOf lo AxialTerm.axial).1, (meanBoundsOf hi AxialTerm.axial).2)
  { degree := g
    axial := b
    axialRate := axialRateBounds b g C.directionLower C.directionUpper
    transverseRate := transverseRateBounds b g C.directionLower C.directionUpper
    valid := decide (0 < totalLower lo) && decide (0 < totalLower hi) }

variable {w} {C : PlaneCell} {bits : ℕ} {x : EuclideanSpace ℝ (Fin 2)}

/-- The rates are valid on every cell when a term with a positive coefficient attains both
normalizing exponents. -/
theorem cellRates_valid_of_min
    (hmin : ∃ t ∈ w.terms, 0 < t.coeff ∧ t.axial = w.axialMin ∧ t.degree = w.degreeMin) :
    (w.cellRates C bits).valid = true := by
  simp only [cellRates, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨totalLower_massList_pos w.nonneg hmin _ _ bits,
    totalLower_massList_pos w.nonneg hmin _ _ bits⟩

/-- On a cell with valid rates the mean degree `Γ` of the weight lies in the degree bounds of
`cellRates`. -/
theorem degree_mem (hC : C.Valid) (hv : (w.cellRates C bits).valid = true) (hx : C.Mem x) :
    (((w.cellRates C bits).degree).1 : ℝ) ≤ axialTermsMean w.terms AxialTerm.degree x ∧
      axialTermsMean w.terms AxialTerm.degree x ≤ ((w.cellRates C bits).degree).2 :=
  axialTermsMean_mem w.nonneg w.degree_comonotone w.axialMin_le w.degreeMin_le hC hv hx

/-- On a cell with valid rates the mean axial exponent `B` of the weight lies in the axial bounds of
`cellRates`. -/
theorem axial_mem (hC : C.Valid) (hv : (w.cellRates C bits).valid = true) (hx : C.Mem x) :
    (((w.cellRates C bits).axial).1 : ℝ) ≤ axialTermsMean w.terms AxialTerm.axial x ∧
      axialTermsMean w.terms AxialTerm.axial x ≤ ((w.cellRates C bits).axial).2 :=
  axialTermsMean_mem w.nonneg w.axial_comonotone w.axialMin_le w.degreeMin_le hC hv hx

/-- **Euler's identity on a cell**: `x·∇w/w` lies in the degree bounds. -/
theorem degreeRate_mem (hC : C.Valid) (hv : (w.cellRates C bits).valid = true)
    (hx : C.Mem x) :
    (((w.cellRates C bits).degree).1 : ℝ) ≤
        (x 0 * (∂[0] w.value) x + x 1 * (∂[1] w.value) x) / w.value x ∧
      (x 0 * (∂[0] w.value) x + x 1 * (∂[1] w.value) x) / w.value x ≤
        ((w.cellRates C bits).degree).2 := by
  rw [value, mul_partialDeriv_add_div w.terms hx.1]
  exact degree_mem hC hv hx

/-- `x₀ ∂₀w/w` lies in the axial-rate bounds on the cell. -/
theorem axialRate_mem (hC : C.Valid) (hv : (w.cellRates C bits).valid = true)
    (hx : C.Mem x) :
    (((w.cellRates C bits).axialRate).1 : ℝ) ≤ x 0 * (∂[0] w.value) x / w.value x ∧
      x 0 * (∂[0] w.value) x / w.value x ≤ ((w.cellRates C bits).axialRate).2 := by
  have hW := C.direction_mem hC hx
  have h1 : (C.directionUpper : ℝ) ≤ 1 := by exact_mod_cast hW.2.2.2
  rw [value, mul_partialDeriv_zero_div w.terms hx.1]
  exact axialRateBounds_mem (axial_mem hC hv hx) (degree_mem hC hv hx) hW.2.1 hW.2.2.1
    (div_nonneg (sq_nonneg _) (sq_nonneg _)) (hW.2.2.1.trans h1)

/-- `x₁ ∂₁w/w` lies in the transverse-rate bounds on the cell. -/
theorem transverseRate_mem (hC : C.Valid) (hv : (w.cellRates C bits).valid = true)
    (hx : C.Mem x) :
    (((w.cellRates C bits).transverseRate).1 : ℝ) ≤ x 1 * (∂[1] w.value) x / w.value x ∧
      x 1 * (∂[1] w.value) x / w.value x ≤ ((w.cellRates C bits).transverseRate).2 := by
  have hW := C.direction_mem hC hx
  have h1 : (C.directionUpper : ℝ) ≤ 1 := by exact_mod_cast hW.2.2.2
  rw [value, mul_partialDeriv_one_div w.terms hx.1]
  exact transverseRateBounds_mem (axial_mem hC hv hx) (degree_mem hC hv hx) hW.2.1 hW.2.2.1
    (hW.2.2.1.trans h1)

/-- The value of the weight lies above `axialTermsLower`. -/
theorem lower_le (hC : C.Valid) (hx : C.Mem x) :
    (axialTermsLower w.terms C bits : ℝ) ≤ w.value x :=
  axialTermsLower_le w.nonneg hC hx bits

/-- The value of the weight lies below `axialTermsUpper` when it exists. -/
theorem le_upper (hC : C.Valid) (hx : C.Mem x) {u : ℚ}
    (hu : axialTermsUpper w.terms C bits = some u) : w.value x ≤ u :=
  le_axialTermsUpper w.nonneg hC hx bits hu

/-! ### Means of any statistic on a cell -/

variable (w C bits) in
/-- The terms with the lower bound of their mass at the lower polar corner `(W₋, R₋)` and the
upper bound at the upper corner `(W₊, R₊)`: every normalized mass is increasing in `W` and in
`R`, so these bound the mass at every point of the cell. -/
def splitMasses : List (AxialTerm × ℚ × ℚ) :=
  w.terms.map fun t ↦
    (t, (t.massBounds w.axialMin w.degreeMin C.directionLower (C.radiusLower bits) bits).1,
      (t.massBounds w.axialMin w.degreeMin C.directionUpper (C.radiusUpper bits) bits).2)

variable (w C bits) in
/-- The bounds on the cell of the mean of a statistic `f` of the terms, with no monotonicity
assumed. -/
def cellMean (f : AxialTerm → ℚ) : ℚ × ℚ :=
  meanBoundsOf (w.splitMasses C bits) f

/-- The normalized mass of a term is increasing in `W` and in `R`. -/
theorem _root_.CAS.Numerics.AxialTerm.polarMass_le_polarMass {t : AxialTerm}
    (ht : 0 ≤ t.coeff) {A G : ℚ} (hA : A ≤ t.axial) (hG : G ≤ t.degree) {W R W' R' : ℝ}
    (hW : 0 ≤ W) (hR : 0 ≤ R) (hWW : W ≤ W') (hRR : R ≤ R') :
    t.polarMass A G W R ≤ t.polarMass A G W' R' := by
  unfold AxialTerm.polarMass
  have hs : (0 : ℝ) ≤ (((t.axial - A) / 2 : ℚ) : ℝ) := by
    push_cast; linarith [(by exact_mod_cast hA : (A : ℝ) ≤ t.axial)]
  have hu : (0 : ℝ) ≤ (((t.degree - G) / 2 : ℚ) : ℝ) := by
    push_cast; linarith [(by exact_mod_cast hG : (G : ℝ) ≤ t.degree)]
  have hc : (0 : ℝ) ≤ t.coeff := by exact_mod_cast ht
  have h1 := Real.rpow_le_rpow hW hWW hs
  have h2 := Real.rpow_le_rpow hR hRR hu
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (Real.rpow_nonneg hR _)
    (Real.rpow_nonneg (hW.trans hWW) _)) hc

/-- The bounds of `splitMasses` hold for the normalized masses at every point of the cell. -/
theorem splitMasses_mem (hC : C.Valid) (hx : C.Mem x) :
    ∀ p ∈ w.splitMasses C bits, (p.2.1 : ℝ) ≤
        p.1.polarMass w.axialMin w.degreeMin (x 0 ^ 2 / ‖x‖ ^ 2) (‖x‖ ^ 2) ∧
      p.1.polarMass w.axialMin w.degreeMin (x 0 ^ 2 / ‖x‖ ^ 2) (‖x‖ ^ 2) ≤ p.2.2 := by
  have hR := C.radius_mem hC hx bits
  have hW := C.direction_mem hC hx
  have hRU : 0 ≤ C.radiusUpper bits := by
    have : (0 : ℝ) ≤ C.radiusUpper bits := (sq_nonneg _).trans hR.2.2
    exact_mod_cast this
  have hWU : 0 ≤ C.directionUpper := by
    have : (0 : ℝ) ≤ C.directionUpper := (div_nonneg (sq_nonneg _) (sq_nonneg _)).trans hW.2.2.1
    exact_mod_cast this
  have hxW : 0 ≤ x 0 ^ 2 / ‖x‖ ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  intro p hp
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hp
  have hlo := AxialTerm.mass_mem (w.nonneg t ht) (A := w.axialMin) (G := w.degreeMin) hW.1 hR.1
    bits
  have hhi := AxialTerm.mass_mem (w.nonneg t ht) (A := w.axialMin) (G := w.degreeMin) hWU hRU
    bits
  exact ⟨hlo.1.trans (AxialTerm.polarMass_le_polarMass (w.nonneg t ht) (w.axialMin_le t ht)
      (w.degreeMin_le t ht) (by exact_mod_cast hW.1) (by exact_mod_cast hR.1) hW.2.1 hR.2.1),
    (AxialTerm.polarMass_le_polarMass (w.nonneg t ht) (w.axialMin_le t ht)
      (w.degreeMin_le t ht) hxW (sq_nonneg _) hW.2.2.1 hR.2.2).trans hhi.2⟩

/-- The total normalized mass at a point of the cell lies between the sums of `splitMasses`. -/
theorem splitMasses_total_mem (hC : C.Valid) (hx : C.Mem x) :
    (totalLower (w.splitMasses C bits) : ℝ) ≤
        (w.terms.map fun t ↦ t.polarMass w.axialMin w.degreeMin (x 0 ^ 2 / ‖x‖ ^ 2)
          (‖x‖ ^ 2)).sum ∧
      (w.terms.map fun t ↦ t.polarMass w.axialMin w.degreeMin (x 0 ^ 2 / ‖x‖ ^ 2)
          (‖x‖ ^ 2)).sum ≤ totalUpper (w.splitMasses C bits) := by
  have hm := w.splitMasses_mem hC hx (bits := bits)
  constructor
  · unfold totalLower; push_cast
    rw [show w.terms.map (fun t ↦ t.polarMass w.axialMin w.degreeMin (x 0 ^ 2 / ‖x‖ ^ 2)
        (‖x‖ ^ 2)) = (w.splitMasses C bits).map (fun p ↦ p.1.polarMass w.axialMin w.degreeMin
          (x 0 ^ 2 / ‖x‖ ^ 2) (‖x‖ ^ 2)) by simp [splitMasses, Function.comp_def], List.map_map]
    exact List.sum_le_sum fun p hp ↦ (hm p hp).1
  · unfold totalUpper; push_cast
    rw [show w.terms.map (fun t ↦ t.polarMass w.axialMin w.degreeMin (x 0 ^ 2 / ‖x‖ ^ 2)
        (‖x‖ ^ 2)) = (w.splitMasses C bits).map (fun p ↦ p.1.polarMass w.axialMin w.degreeMin
          (x 0 ^ 2 / ‖x‖ ^ 2) (‖x‖ ^ 2)) by simp [splitMasses, Function.comp_def], List.map_map]
    exact List.sum_le_sum fun p hp ↦ (hm p hp).2

/-- **The mean of any statistic on a cell** lies in `cellMean`, when the lower masses have a
positive sum. -/
theorem cellMean_mem (hC : C.Valid) (hx : C.Mem x) (hv : 0 < totalLower (w.splitMasses C bits))
    (f : AxialTerm → ℚ) :
    ((w.cellMean C bits f).1 : ℝ) ≤ axialTermsMean w.terms f x ∧
      axialTermsMean w.terms f x ≤ (w.cellMean C bits f).2 := by
  have h := meanBoundsOf_mem
    (fun t ↦ t.polarMass w.axialMin w.degreeMin (x 0 ^ 2 / ‖x‖ ^ 2) (‖x‖ ^ 2))
    (w.splitMasses_mem hC hx (bits := bits)) hv f
  simp only [splitMasses, List.map_map, Function.comp_def] at h
  rw [axialTermsMean, ← polarMean_eq w.terms f w.axialMin w.degreeMin hx.1]
  exact ⟨h.2.1, h.2.2⟩

/-- The lower masses of `splitMasses` have a positive sum when a term with a positive coefficient
attains both normalizing exponents. -/
theorem splitMasses_valid_of_min
    (hmin : ∃ t ∈ w.terms, 0 < t.coeff ∧ t.axial = w.axialMin ∧ t.degree = w.degreeMin) :
    0 < totalLower (w.splitMasses C bits) := by
  have h := totalLower_massList_pos w.nonneg hmin C.directionLower (C.radiusLower bits) bits
  simpa [splitMasses, massList, totalLower, List.map_map, Function.comp_def] using h

/-! ### Products with vanishing factors -/

/-- The weight is nonnegative where `x₀ > 0`. -/
theorem value_nonneg (hx : 0 < x 0) : 0 ≤ w.value x := by
  unfold value axialTermsValue
  exact List.sum_nonneg fun y hy ↦ by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
    exact mul_nonneg (by exact_mod_cast w.nonneg t ht) (axialPower_pos 0 _ _ hx.ne').le

/-- **A singular weight times a vanishing factor**, with any bound `u` of the shifted weight
`|x₀|^p |x|^q w` at the point: if `|F| ≤ |x₀|^p |x|^q T`, then `|F| w(x) ≤ u T`. -/
theorem abs_mul_le_of_shift_le (hx : 0 < x 0) {p q : ℚ} {u : ℝ}
    (hu : axialTermsValue (AxialTerm.shift p q w.terms) x ≤ u) {F T : ℝ}
    (hF : |F| ≤ |x 0| ^ (p : ℝ) * ‖x‖ ^ (q : ℝ) * T) (hT : 0 ≤ T) :
    |F| * w.value x ≤ u * T := by
  rw [axialTermsValue_shift p q w.terms hx] at hu
  calc |F| * w.value x ≤ |x 0| ^ (p : ℝ) * ‖x‖ ^ (q : ℝ) * T * w.value x :=
        mul_le_mul_of_nonneg_right hF (w.value_nonneg hx)
    _ = T * (|x 0| ^ (p : ℝ) * ‖x‖ ^ (q : ℝ) * axialTermsValue w.terms x) := by
        rw [value]; ring
    _ ≤ T * u := mul_le_mul_of_nonneg_left hu hT
    _ = u * T := mul_comm _ _

/-- **A singular weight times a vanishing factor on a cell**: if `|F| ≤ |x₀|^p |x|^q T` at a
point `x` of the cell, then `|F| w(x) ≤ u T` with `u` the upper bound on the cell of the shifted
weight `|x₀|^p |x|^q w`, which is finite on the axis when `p` cancels the axial singularity. -/
theorem abs_mul_le_of_vanishing (hC : C.Valid) (hx : C.Mem x) {p q u : ℚ}
    (hu : axialTermsUpper (AxialTerm.shift p q w.terms) C bits = some u) {F T : ℝ}
    (hF : |F| ≤ |x 0| ^ (p : ℝ) * ‖x‖ ^ (q : ℝ) * T) (hT : 0 ≤ T) :
    |F| * w.value x ≤ u * T :=
  w.abs_mul_le_of_shift_le hx.1 (le_axialTermsUpper (w.nonneg.shift p q) hC hx bits hu) hF hT

/-- **A ratio of weights with a common singular factor**: `w₁/w₂ ≤ u/l` with `u` the upper bound
of `|x₀|^p |x|^q w₁` and `l > 0` the lower bound of `|x₀|^p |x|^q w₂` on the cell. -/
theorem div_le_of_shift (w' : AxialWeight) (hC : C.Valid) (hx : C.Mem x) {p q u : ℚ}
    (hu : axialTermsUpper (AxialTerm.shift p q w.terms) C bits = some u)
    (hl : 0 < axialTermsLower (AxialTerm.shift p q w'.terms) C bits) :
    w.value x / w'.value x ≤ u / axialTermsLower (AxialTerm.shift p q w'.terms) C bits := by
  have hs := le_axialTermsUpper (w.nonneg.shift p q) hC hx bits hu
  have hs' := axialTermsLower_le (w'.nonneg.shift p q) hC hx bits
  rw [axialTermsValue_shift p q _ hx.1] at hs hs'
  have hK : 0 < |x 0| ^ (p : ℝ) * ‖x‖ ^ (q : ℝ) := by
    have h0 := abs_pos.2 hx.1.ne'
    have hn : 0 < ‖x‖ := (abs_pos.2 hx.1.ne').trans_le (by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x 0)
    positivity
  have hl' : (0 : ℝ) < axialTermsLower (AxialTerm.shift p q w'.terms) C bits := by
    exact_mod_cast hl
  have hw : 0 ≤ |x 0| ^ (p : ℝ) * ‖x‖ ^ (q : ℝ) * axialTermsValue w.terms x :=
    mul_nonneg hK.le (w.value_nonneg hx.1)
  rw [value, value, ← mul_div_mul_left _ _ hK.ne']
  exact div_le_div₀ (hw.trans hs) hs hl' hs'

/-- **A ratio with the vanishing factor kept outside the enclosure**:
`w₁/w₂ ≤ |x₀|^p |x|^q (u/l)` with `u` an upper bound of `w₁` and `l > 0` the lower bound of
`|x₀|^p |x|^q w₂` on the cell, so that the factor `|x₀|^p |x|^q` survives into the bound. -/
theorem div_le_mul_of_shift (w' : AxialWeight) (hC : C.Valid) (hx : C.Mem x) {p q u : ℚ}
    (hu : axialTermsUpper w.terms C bits = some u)
    (hl : 0 < axialTermsLower (AxialTerm.shift p q w'.terms) C bits) :
    w.value x / w'.value x ≤ |x 0| ^ (p : ℝ) * ‖x‖ ^ (q : ℝ) *
      (u / axialTermsLower (AxialTerm.shift p q w'.terms) C bits) := by
  have hs := w.le_upper hC hx hu
  have hs' := axialTermsLower_le (w'.nonneg.shift p q) hC hx bits
  rw [axialTermsValue_shift p q _ hx.1] at hs'
  have hK : 0 < |x 0| ^ (p : ℝ) * ‖x‖ ^ (q : ℝ) := by
    have h0 := abs_pos.2 hx.1.ne'
    have hn : 0 < ‖x‖ := (abs_pos.2 hx.1.ne').trans_le (by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x 0)
    positivity
  have hl' : (0 : ℝ) < axialTermsLower (AxialTerm.shift p q w'.terms) C bits := by
    exact_mod_cast hl
  have hw := w.value_nonneg hx.1
  rw [← mul_div_mul_left (w.value x) (w'.value x) hK.ne', mul_div_assoc']
  refine div_le_div₀ (mul_nonneg hK.le (hw.trans hs)) (mul_le_mul_of_nonneg_left hs hK.le) hl' ?_
  rw [value]; exact hs'

end AxialWeight

/-! ### Bounds through the radius alone -/

/-- `c |x|^{a+b} ≤ c |x₀|^a |x|^b` for `a ≤ 0`, since `|x₀| ≤ |x|`. -/
theorem AxialTerm.degree_le_value {t : AxialTerm} (ht : 0 ≤ t.coeff) (ha : t.axial ≤ 0)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : 0 < x 0) :
    (t.coeff : ℝ) * ‖x‖ ^ (t.degree : ℝ) ≤ t.value x := by
  have hn : 0 < ‖x‖ := by rw [norm_pos_iff]; intro h; simp [h] at hx
  have hle : |x 0| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
  have hax : ‖x‖ ^ (t.axial : ℝ) ≤ |x 0| ^ (t.axial : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (abs_pos.2 hx.ne') hle (by exact_mod_cast ha)
  have hc : (0 : ℝ) ≤ t.coeff := by exact_mod_cast ht
  unfold AxialTerm.value axialPower AxialTerm.degree
  push_cast
  rw [Real.rpow_add hn]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hax (Real.rpow_nonneg hn.le _)) hc

/-- A term is at most the weight. -/
theorem AxialTerm.value_le_axialTermsValue {ts : List AxialTerm}
    (hts : AxialTerm.NonnegCoeff ts) {t : AxialTerm} (ht : t ∈ ts)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : 0 < x 0) :
    t.value x ≤ axialTermsValue ts x := by
  have hnn : ∀ s ∈ ts, 0 ≤ s.value x := fun s hs ↦
    mul_nonneg (by exact_mod_cast hts s hs) (axialPower_pos 0 _ _ hx.ne').le
  exact List.single_le_sum (fun y hy ↦ by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy; exact hnn s hs) _ (List.mem_map_of_mem ht)

/-- The lower bound `∑ c (R^{(a+b)/2})₋` of a weight with `a ≤ 0` for `|x|² ∈ [R₀, R₁]`. -/
def degreeTermsLower (ts : List AxialTerm) (R₀ R₁ : ℚ) (bits : ℕ) : ℚ :=
  (ts.map fun t ↦ t.coeff * monoPowLower R₀ R₁ (t.degree / 2) bits).sum

/-- The upper bound `∑ c (R^{b/2})₊` of a radial weight for `|x|² ∈ [R₀, R₁]`, `R₀ > 0`. -/
def radialTermsUpper (ts : List AxialTerm) (R₀ R₁ : ℚ) (bits : ℕ) : ℚ :=
  (ts.map fun t ↦
    t.coeff * (rpowBounds (if 0 ≤ t.radial then R₁ else R₀) (t.radial / 2) bits).2).sum

/-- For nonnegative coefficients and axial exponents `a ≤ 0`, `degreeTermsLower ts R₀ R₁ bits` is a
lower bound of the weight at `x₀ > 0` with `|x|² ∈ [R₀, R₁]`, `R₀ ≥ 0`. -/
theorem degreeTermsLower_le {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts)
    (ha : ∀ t ∈ ts, t.axial ≤ 0) {R₀ R₁ : ℚ} (hR₀ : 0 ≤ R₀) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : 0 < x 0) (h₀ : (R₀ : ℝ) ≤ ‖x‖ ^ 2) (h₁ : ‖x‖ ^ 2 ≤ R₁) (bits : ℕ) :
    (degreeTermsLower ts R₀ R₁ bits : ℝ) ≤ axialTermsValue ts x := by
  have hn := norm_sq_pos_of_pos hx
  unfold degreeTermsLower axialTermsValue
  push_cast
  rw [List.map_map]
  refine List.sum_le_sum fun t ht ↦ ?_
  simp only [Function.comp]
  have hm := monoPowLower_le hR₀ hn h₀ h₁ (t.degree / 2) bits
  have hc : (0 : ℝ) ≤ t.coeff := by exact_mod_cast hts t ht
  refine le_trans ?_ (AxialTerm.degree_le_value (hts t ht) (ha t ht) hx)
  rw [norm_rpow_eq_sq]
  push_cast at hm ⊢
  exact mul_le_mul_of_nonneg_left hm hc

/-- For radial terms with nonnegative coefficients, `radialTermsUpper ts R₀ R₁ bits` is an upper
bound of the weight at `x₀ > 0` with `|x|² ∈ [R₀, R₁]`, `R₀ > 0`. -/
theorem le_radialTermsUpper {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts)
    (ha : ∀ t ∈ ts, t.axial = 0) {R₀ R₁ : ℚ} (hR₀ : 0 < R₀) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : 0 < x 0) (h₀ : (R₀ : ℝ) ≤ ‖x‖ ^ 2) (h₁ : ‖x‖ ^ 2 ≤ R₁) (bits : ℕ) :
    axialTermsValue ts x ≤ radialTermsUpper ts R₀ R₁ bits := by
  have hn := norm_sq_pos_of_pos hx
  have hR₀' : (0 : ℝ) < R₀ := by exact_mod_cast hR₀
  have hR₁ : (0 : ℚ) ≤ R₁ := by
    have : (0 : ℝ) ≤ R₁ := hn.le.trans h₁
    exact_mod_cast this
  unfold radialTermsUpper axialTermsValue
  push_cast
  rw [List.map_map]
  refine List.sum_le_sum fun t ht ↦ ?_
  simp only [Function.comp]
  have hc : (0 : ℝ) ≤ t.coeff := by exact_mod_cast hts t ht
  unfold AxialTerm.value axialPower
  rw [ha t ht, norm_rpow_eq_sq]
  simp only [Rat.cast_zero, Real.rpow_zero, one_mul, Rat.cast_mul]
  refine mul_le_mul_of_nonneg_left ?_ hc
  split_ifs with hr
  · have hr' : (0 : ℝ) ≤ ((t.radial / 2 : ℚ) : ℝ) := by
      push_cast; have : (0 : ℝ) ≤ t.radial := by exact_mod_cast hr
      linarith
    have := (rpowBounds_mem hR₁ (t.radial / 2) bits).2
    push_cast at this hr' ⊢
    exact (Real.rpow_le_rpow hn.le h₁ hr').trans this
  · have hr' : ((t.radial / 2 : ℚ) : ℝ) ≤ 0 := by
      push_cast; have : (t.radial : ℝ) < 0 := by exact_mod_cast not_le.1 hr
      linarith
    have := (rpowBounds_mem hR₀.le (t.radial / 2) bits).2
    push_cast at this hr' ⊢
    exact (Real.rpow_le_rpow_of_nonpos hR₀' h₀ hr').trans this

/-- The upper bound `∑ c (R₁^{(a+b)/2})₊` of a weight whose terms have nonnegative axial
exponents and degrees, for `|x|² ≤ R₁`: `|x₀|^a |x|^b ≤ |x|^{a+b}` for `a ≥ 0`, so the bound is
finite on cells at the origin. -/
def degreeTermsUpper (ts : List AxialTerm) (R₁ : ℚ) (bits : ℕ) : ℚ :=
  (ts.map fun t ↦ t.coeff * (rpowBounds R₁ (t.degree / 2) bits).2).sum

/-- For nonnegative coefficients, axial exponents and degrees, `degreeTermsUpper ts R₁ bits` is an
upper bound of the weight at `x₀ > 0` with `|x|² ≤ R₁`. -/
theorem le_degreeTermsUpper {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts)
    (ha : ∀ t ∈ ts, 0 ≤ t.axial ∧ 0 ≤ t.degree) {R₁ : ℚ} {x : EuclideanSpace ℝ (Fin 2)}
    (hx : 0 < x 0) (h₁ : ‖x‖ ^ 2 ≤ R₁) (bits : ℕ) :
    axialTermsValue ts x ≤ degreeTermsUpper ts R₁ bits := by
  have hn : 0 < ‖x‖ := (abs_pos.2 hx.ne').trans_le (by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x 0)
  have hR₁ : (0 : ℚ) ≤ R₁ := by
    have : (0 : ℝ) ≤ R₁ := (sq_nonneg _).trans h₁
    exact_mod_cast this
  have hle : |x 0| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
  unfold degreeTermsUpper axialTermsValue
  push_cast
  rw [List.map_map]
  refine List.sum_le_sum fun t ht ↦ ?_
  simp only [Function.comp]
  have hc : (0 : ℝ) ≤ t.coeff := by exact_mod_cast hts t ht
  have ha' : (0 : ℝ) ≤ t.axial := by exact_mod_cast (ha t ht).1
  have hd : (0 : ℝ) ≤ ((t.degree / 2 : ℚ) : ℝ) := by
    have := (ha t ht).2; push_cast; have : (0 : ℝ) ≤ t.degree := by exact_mod_cast this
    linarith
  unfold AxialTerm.value axialPower
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ hc
  calc |x 0| ^ (t.axial : ℝ) * ‖x‖ ^ (t.radial : ℝ)
      ≤ ‖x‖ ^ (t.axial : ℝ) * ‖x‖ ^ (t.radial : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) hle ha')
          (Real.rpow_nonneg hn.le _)
    _ = (‖x‖ ^ 2) ^ ((t.degree / 2 : ℚ) : ℝ) := by
        rw [← Real.rpow_add hn, norm_rpow_eq_sq]; congr 1; simp [AxialTerm.degree]
    _ ≤ (R₁ : ℝ) ^ ((t.degree / 2 : ℚ) : ℝ) := Real.rpow_le_rpow (sq_nonneg _) h₁ hd
    _ ≤ _ := (rpowBounds_mem hR₁ _ bits).2

/-- **A singular weight times a vanishing factor at the origin**: if every shifted term of
`|x₀|^p |x|^q w` has nonnegative axial exponent and degree, `|F| ≤ |x₀|^p |x|^q T` and
`|x|² ≤ R₁`, then `|F| w(x) ≤ (∑ c R₁^{(a+b)/2})₊ T`, finite on cells at the origin. -/
theorem AxialWeight.abs_mul_le_of_vanishing_degree (w : AxialWeight) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : 0 < x 0) {p q : ℚ}
    (ha : ∀ t ∈ AxialTerm.shift p q w.terms, 0 ≤ t.axial ∧ 0 ≤ t.degree) {R₁ : ℚ}
    (h₁ : ‖x‖ ^ 2 ≤ R₁) (bits : ℕ) {F T : ℝ} (hF : |F| ≤ |x 0| ^ (p : ℝ) * ‖x‖ ^ (q : ℝ) * T)
    (hT : 0 ≤ T) :
    |F| * w.value x ≤ degreeTermsUpper (AxialTerm.shift p q w.terms) R₁ bits * T :=
  w.abs_mul_le_of_shift_le hx (le_degreeTermsUpper (w.nonneg.shift p q) ha hx h₁ bits) hF hT

/-! ### The transverse rate scaled by the radius -/

/-- **The transverse rate scaled by the radius**: `|x| ∂₁w/w = √(1 - W) (Γ - B)` on the open
quadrant, with `W = x₀²/|x|²`, the mean degree `Γ` and the mean axial exponent `B`; unlike
`x₁ ∂₁w/w / x₁` it has no factor singular on the axis. -/
theorem norm_mul_partialDeriv_one_div (ts : List AxialTerm) {x : EuclideanSpace ℝ (Fin 2)}
    (hx0 : 0 < x 0) (hx1 : 0 < x 1) :
    ‖x‖ * (∂[1] (axialTermsValue ts)) x / axialTermsValue ts x =
      √(1 - x 0 ^ 2 / ‖x‖ ^ 2) *
        (axialTermsMean ts AxialTerm.degree x - axialTermsMean ts AxialTerm.axial x) := by
  have hn := norm_sq_pos_of_pos hx0
  have hn' : 0 < ‖x‖ := (abs_pos.2 hx0.ne').trans_le (by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x 0)
  have h := mul_partialDeriv_one_div ts hx0
  have hW : 1 - x 0 ^ 2 / ‖x‖ ^ 2 = (x 1 / ‖x‖) ^ 2 := by
    rw [div_pow, eq_div_iff hn.ne', sub_mul, one_mul, div_mul_cancel₀ _ hn.ne',
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    ring
  rw [hW, Real.sqrt_sq (div_nonneg hx1.le hn'.le)]
  rw [hW] at h
  have e : ‖x‖ * (∂[1] (axialTermsValue ts)) x / axialTermsValue ts x =
      ‖x‖ / x 1 * (x 1 * (∂[1] (axialTermsValue ts)) x / axialTermsValue ts x) := by
    field_simp
  rw [e, h]
  field_simp

/-- The bounds of `√(1 - W)(Γ - B)` on a cell from the bounds `B ∈ [b₀, b₁]`, `Γ ∈ [g₀, g₁]`,
`W ∈ [w₀, w₁] ⊂ [0, 1]`, with square roots to `s` binary digits. -/
def transverseNormRateBounds (b g : ℚ × ℚ) (w₀ w₁ : ℚ) (s : ℕ) : ℚ × ℚ :=
  let r₀ := (rootBounds (1 - w₁) 2 s).1
  let r₁ := (rootBounds (1 - w₀) 2 s).2
  (min (0 + (g.1 - b.2) * r₀) (0 + (g.1 - b.2) * r₁),
    max (0 + (g.2 - b.1) * r₀) (0 + (g.2 - b.1) * r₁))

/-- `transverseNormRateBounds b g w₀ w₁ s` encloses `√(1 - W)(Γ - B)` for `B ∈ [b₀, b₁]`,
`Γ ∈ [g₀, g₁]` and `w₀ ≤ W ≤ w₁ ≤ 1`. -/
theorem transverseNormRateBounds_mem {b g : ℚ × ℚ} {w₀ w₁ : ℚ} {B Γ W : ℝ}
    (hB : (b.1 : ℝ) ≤ B ∧ B ≤ b.2) (hΓ : (g.1 : ℝ) ≤ Γ ∧ Γ ≤ g.2) (hW₀ : (w₀ : ℝ) ≤ W)
    (hW₁ : W ≤ w₁) (hw₁ : w₁ ≤ 1) (s : ℕ) :
    ((transverseNormRateBounds b g w₀ w₁ s).1 : ℝ) ≤ √(1 - W) * (Γ - B) ∧
      √(1 - W) * (Γ - B) ≤ (transverseNormRateBounds b g w₀ w₁ s).2 := by
  have hw₀ : w₀ ≤ 1 := by
    have : (w₀ : ℝ) ≤ 1 := hW₀.trans (hW₁.trans (by exact_mod_cast hw₁))
    exact_mod_cast this
  have h₀ := rootBounds_mem (sub_nonneg.2 hw₁) (q := 2) (by norm_num) s
  have h₁ := rootBounds_mem (sub_nonneg.2 hw₀) (q := 2) (by norm_num) s
  have e : ∀ v : ℝ, v ^ (2 : ℝ)⁻¹ = √v := fun v ↦ by rw [Real.sqrt_eq_rpow, one_div]
  push_cast at h₀ h₁
  rw [e] at h₀ h₁
  have hs₀ : ((rootBounds (1 - w₁) 2 s).1 : ℝ) ≤ √(1 - W) :=
    h₀.1.trans (Real.sqrt_le_sqrt (by linarith))
  have hs₁ : √(1 - W) ≤ ((rootBounds (1 - w₀) 2 s).2 : ℝ) :=
    (Real.sqrt_le_sqrt (by linarith)).trans h₁.2
  have hS := Real.sqrt_nonneg (1 - W)
  have hl := (affine_mem_minmax (p := 0) (q := (g.1 : ℝ) - b.2) hs₀ hs₁).1
  have hu := (affine_mem_minmax (p := 0) (q := (g.2 : ℝ) - b.1) hs₀ hs₁).2
  unfold transverseNormRateBounds
  push_cast
  constructor
  · refine hl.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left (show (g.1 : ℝ) - b.2 ≤ Γ - B by linarith [hB.2, hΓ.1]) hS]
  · refine le_trans ?_ hu
    nlinarith [mul_le_mul_of_nonneg_left (show Γ - B ≤ (g.2 : ℝ) - b.1 by linarith [hB.1, hΓ.2]) hS]

/-- **The transverse rate scaled by the radius on a cell**: `|x| ∂₁w/w` lies in
`transverseNormRateBounds` of the cell rates. -/
theorem AxialWeight.normTransverseRate_mem (w : AxialWeight) {C : PlaneCell} (hC : C.Valid)
    {bits : ℕ} (hv : (w.cellRates C bits).valid = true) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : C.Mem x) (s : ℕ) :
    ((transverseNormRateBounds (w.cellRates C bits).axial (w.cellRates C bits).degree
        C.directionLower C.directionUpper s).1 : ℝ) ≤ ‖x‖ * (∂[1] w.value) x / w.value x ∧
      ‖x‖ * (∂[1] w.value) x / w.value x ≤
        (transverseNormRateBounds (w.cellRates C bits).axial (w.cellRates C bits).degree
          C.directionLower C.directionUpper s).2 := by
  have hW := C.direction_mem hC hx
  rw [AxialWeight.value, norm_mul_partialDeriv_one_div w.terms hx.1 hx.2.1]
  exact transverseNormRateBounds_mem (w.axial_mem hC hv hx) (w.degree_mem hC hv hx) hW.2.1
    hW.2.2.1 hW.2.2.2 s

end CAS.Numerics
