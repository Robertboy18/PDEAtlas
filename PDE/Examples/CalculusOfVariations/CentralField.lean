/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.SlopeField.Closed
public import PDE.CalculusOfVariations.SlopeField.HamiltonJacobi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Two slope fields of the kinetic integral

## Motivation

Are the premises of the field theory of `PDE.CalculusOfVariations.SlopeField` satisfiable, and
what does the theory say for the simplest integral `J(y) = ∫ ‖y'‖² / 2 dx`?

## The idea

The straight lines through the origin, `y = x c`, cover the half space `x > 0`. Their slope
field is `p(x, y) = y / x`, and `S(x, y) = ‖y‖² / (2 x)` is an eikonal: its differential is
`-(‖y‖² / (2 x²)) dx + ⟪y / x, dy⟫`, which is the form of the field. The integrand is convex in
the slope, so every such line minimizes `J` among the curves in the half space with its
endpoints, corners allowed. The unknown takes values in any real inner product space.

The parallel lines of a fixed slope `c` cover the whole space. The form of their field is
constant, hence closed, on the convex open region `univ`.

## Main results

* `isEikonal_centralField` (one example, every inner product space): the eikonal of the central
  field of the kinetic integral on the half space.
* `integral_kinetic_line_le` (one example): `∫ ‖c‖² / 2 ≤ ∫ ‖y'‖² / 2` for every curve `y` in
  the half space with `y(a) = a c` and `y(b) = b c`, `0 < a ≤ b`.
* `hamiltonJacobi_eikonal` (one example): the eikonal solves
  `S_x + sup_q (S_y q - ‖q‖² / 2) = 0`.
* `exists_isEikonal_parallelField` (one example): the field of parallel lines has an eikonal, by
  the Poincaré lemma.

## Relations

* `integral_kinetic_line_le` is `IsEikonal.integral_le_of_convexOn` for the central field,
  `hamiltonJacobi_eikonal` is `IsEikonal.hamiltonJacobi`, and `exists_isEikonal_parallelField`
  is `exists_isEikonal_of_convex`: each instantiates every premise of the general theorem.

## What stays open

Nothing here is more than an example.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.CalculusOfVariations.SlopeField

namespace PDE.Examples.CentralField

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The kinetic Lagrangian `L(x, y, q) = ‖q‖² / 2`. -/
def kinetic (_z : ℝ × E) (q : E) : ℝ := ‖q‖ ^ 2 / 2

/-- The slope field of the lines through the origin: `p(x, y) = y / x`. -/
def slope (z : ℝ × E) : E := z.1⁻¹ • z.2

/-- The half space `x > 0`. -/
def region : Set (ℝ × E) := {z | 0 < z.1}

/-- The eikonal of the central field: `S(x, y) = ‖y‖² / (2 x)`. -/
def eikonal (z : ℝ × E) : ℝ := ‖z.2‖ ^ 2 / (2 * z.1)

/-- The derivative of the kinetic Lagrangian in the slope is the inner product with the slope. -/
theorem hasFDerivAt_kinetic (z : ℝ × E) (q : E) :
    HasFDerivAt (kinetic z) (innerSL ℝ q) q := by
  have h := ((hasStrictFDerivAt_norm_sq q).hasFDerivAt).const_mul (2⁻¹ : ℝ)
  refine (h.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ ?_)
  · simp [two_smul]
    ring
  · simp only [kinetic]
    ring

/-- The kinetic Lagrangian is convex in the slope. -/
theorem convexOn_kinetic (z : ℝ × E) : ConvexOn ℝ univ (kinetic z) := by
  have h := ((convexOn_univ_norm (E := E)).pow (fun _ _ ↦ norm_nonneg _) 2).smul
    (show (0 : ℝ) ≤ 2⁻¹ by norm_num)
  have heq : kinetic z = (2⁻¹ : ℝ) • (norm ^ 2 : E → ℝ) := by
    funext q
    simp only [kinetic, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
    ring
  rwa [heq]

/-- The momentum of a slope field for the kinetic Lagrangian is the inner product with the
slope. -/
theorem momentum_kinetic (p : ℝ × E → E) (z : ℝ × E) :
    momentum kinetic p z = innerSL ℝ (p z) :=
  (hasFDerivAt_kinetic z (p z)).fderiv

/-- The energy of a slope field for the kinetic Lagrangian is `‖p‖² / 2`. -/
theorem energy_kinetic (p : ℝ × E → E) (z : ℝ × E) :
    energy kinetic p z = ‖p z‖ ^ 2 / 2 := by
  rw [energy, momentum_kinetic, innerSL_apply_apply, real_inner_self_eq_norm_sq, kinetic]
  ring

/-- `S(x, y) = ‖y‖² / (2 x)` is an eikonal of the central field of the kinetic integral on the
half space `x > 0`. -/
theorem isEikonal_centralField :
    IsEikonal (kinetic (E := E)) slope region eikonal := by
  intro z hz
  have hx : (0 : ℝ) < z.1 := hz
  have hden : HasFDerivAt (fun w : ℝ × E ↦ 2 * w.1)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ E) z := (hasFDerivAt_fst (𝕜 := ℝ)).const_mul 2
  have hinv : HasFDerivAt (fun w : ℝ × E ↦ (2 * w.1)⁻¹)
      ((-((2 * z.1) ^ 2)⁻¹) • ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ E)) z :=
    HasDerivAt.comp_hasFDerivAt (h₂ := fun t : ℝ ↦ t⁻¹) z
      (hasDerivAt_inv (by positivity)) hden
  have hnum : HasFDerivAt (fun w : ℝ × E ↦ ‖w.2‖ ^ 2)
      ((2 • innerSL ℝ z.2).comp (ContinuousLinearMap.snd ℝ ℝ E)) z :=
    HasFDerivAt.comp (g := fun y : E ↦ ‖y‖ ^ 2) z
      (hasStrictFDerivAt_norm_sq z.2).hasFDerivAt (hasFDerivAt_snd (𝕜 := ℝ))
  refine ((hnum.mul hinv).congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun w ↦ ?_)
  · rw [beltramiForm_apply, momentum_kinetic, energy_kinetic, slope, innerSL_apply_apply,
      real_inner_smul_left, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hx.le)]
    simp [two_smul]
    field_simp
    ring
  · simp only [eikonal, div_eq_mul_inv, Pi.mul_apply]

/-- The line `y = x c` through the origin is a curve of the half space over `[a, b]`, `a > 0`. -/
theorem isCurveIn_line {a b : ℝ} (ha : 0 < a) (c : E) :
    IsCurveIn (region (E := E)) a b (fun x ↦ x • c) (fun _ ↦ c) where
  continuousOn := (continuous_id.smul continuous_const).continuousOn
  hasDerivAt := ⟨∅, countable_empty, fun x _ ↦ by
    simpa using (hasDerivAt_id x).smul_const c⟩
  mem := fun _ hx ↦ ha.trans_le hx.1

/-- Straight lines through the origin minimize the kinetic integral: for `0 < a ≤ b` and every
curve `y` in the half space `x > 0` with `y(a) = a c` and `y(b) = b c`,
`∫ ‖c‖² / 2 ≤ ∫ ‖y'‖² / 2`. The curve may have corners and its slopes are not restricted; the
kinetic integrand and the integrand of the invariant integral along `y` are assumed interval
integrable. -/
theorem integral_kinetic_line_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c : E) {y y' : ℝ → E}
    (hy : IsCurveIn (region (E := E)) a b y y') (hya : y a = a • c) (hyb : y b = b • c)
    (hLy : IntervalIntegrable (fun x ↦ ‖y' x‖ ^ 2 / 2) volume a b)
    (hint : IntervalIntegrable (fun x ↦ beltramiForm kinetic slope (x, y x) (1, y' x))
      volume a b) :
    ∫ _ in a..b, ‖c‖ ^ 2 / 2 ≤ ∫ x in a..b, ‖y' x‖ ^ 2 / 2 := by
  refine isEikonal_centralField.integral_le_of_convexOn (y₀ := fun x ↦ x • c)
    (y₀' := fun _ ↦ c) hab hy (isCurveIn_line ha c) (fun x hx ↦ ?_) hya hyb hLy hint
    intervalIntegrable_const (fun z _ ↦ convexOn_kinetic z)
    (fun z _ ↦ (hasFDerivAt_kinetic z _).differentiableAt)
  rw [slope, inv_smul_smul₀ (ha.trans hx.1).ne']

/-- The eikonal of the central field solves the Hamilton–Jacobi equation of the kinetic
integral, `S_x + sup_q (S_y q - ‖q‖² / 2) = 0`, on the half space. -/
theorem hamiltonJacobi_eikonal {z : ℝ × E} (hz : z ∈ region (E := E)) :
    fderiv ℝ eikonal z (1, 0) + ⨆ q : E, (fderiv ℝ eikonal z (0, q) - ‖q‖ ^ 2 / 2) = 0 :=
  isEikonal_centralField.hamiltonJacobi hz (convexOn_kinetic z)
    (hasFDerivAt_kinetic z _).differentiableAt

/-- The form of the field of parallel lines of slope `c` is constant. -/
theorem beltramiForm_parallelField (c : E) :
    beltramiForm (kinetic (E := E)) (fun _ ↦ c) = fun _ ↦
      (innerSL ℝ c).comp (ContinuousLinearMap.snd ℝ ℝ E) -
        (‖c‖ ^ 2 / 2) • ContinuousLinearMap.fst ℝ ℝ E := by
  funext z
  rw [beltramiForm, momentum_kinetic, energy_kinetic]

/-- The field of parallel lines of slope `c` has an eikonal on the whole space: its form is
constant, so it is differentiable and closed on the convex open region `univ`. -/
theorem exists_isEikonal_parallelField (c : E) :
    ∃ S, IsEikonal (kinetic (E := E)) (fun _ ↦ c) univ S := by
  refine exists_isEikonal_of_convex convex_univ isOpen_univ ?_ fun z _ u v ↦ ?_
  · rw [beltramiForm_parallelField]
    exact differentiableOn_const _
  · rw [beltramiForm_parallelField]
    simp

end PDE.Examples.CentralField
