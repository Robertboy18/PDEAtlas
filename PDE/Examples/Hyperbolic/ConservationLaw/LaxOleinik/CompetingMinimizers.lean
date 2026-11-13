/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.ConservationLaw.LaxOleinik.AffineFlux
public import PDE.Hyperbolic.ConservationLaw.Riemann.Data
public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Minimizers
import CAS.IntegrationTactic

/-!
# Two competing footpoints for a moving shock

The two-state datum `1, -1` has the concave primitive `-|x|`. For the flux
`p²/2 + a p + b`, its Hopf–Lax value is
`-|x-a t| - t/2 - b t`. At the moving shock `x=a t`, the two minimizing
footpoints are `-t` and `t`. Elsewhere the minimizer is unique.

The value comes from the Lax–Oleinik formula `laxOleinik_formula_of_deriv2_lower_bound`
and the Legendre transform `affineQuadraticFlux_legendre` (`compressive_value`).
`compressive_minimizer_iff` lists all minimizing footpoints, and
`compressive_nonunique_set` shows that the minimizer is not unique exactly at
`x = a t`.
-/

@[expose] public noncomputable section

open MeasureTheory Set HamiltonJacobi.HopfLax PDE.Analysis PDE.Common
open PDE.Hyperbolic.ConservationLaw PDE.Hyperbolic.ConservationLaw.LaxOleinik
open scoped ENNReal NNReal

namespace PDE.Examples.ConservationLaw.LaxOleinik

/-- The affine quadratic flux is `C²`. -/
theorem affineQuadraticFlux_contDiff (a b : ℝ) :
    ContDiff ℝ 2 (affineQuadraticFlux a b) := by
  unfold affineQuadraticFlux
  fun_prop

/-- The second derivative is one for every drift and signed offset. -/
theorem affineQuadraticFlux_deriv2 (a b r : ℝ) :
    deriv (deriv (affineQuadraticFlux a b)) r = 1 := by
  rw [show deriv (affineQuadraticFlux a b) = fun q ↦ q + a from
    funext fun q ↦ (affineQuadraticFlux_hasDerivAt a b q).deriv]
  cas

/-- The compressive step has essential bound one and does not decay at infinity. -/
theorem compressiveData_memLp : MemLp (riemannData (1 : ℝ) (-1)) ∞ volume := by
  apply memLp_top_of_bound (stronglyMeasurable_riemannData _ _).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x ↦ by
    simpa using norm_riemannData_le_max (1 : ℝ) (-1) x

/-- The primitive of the step datum `riemannData 1 (-1)` is `-|x|`. -/
theorem compressiveData_primitive (x : ℝ) :
    (∫ s in (0 : ℝ)..x, riemannData (1 : ℝ) (-1) s) = -|x| := by
  rcases le_total 0 x with hx | hx
  · calc
      _ = ∫ s in (0 : ℝ)..x, (-1 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        intro s hs
        rw [uIoo_of_le hx] at hs
        exact riemannData_of_nonneg _ _ hs.1.le
      _ = -|x| := by rw [abs_of_nonneg hx]; cas
  · calc
      _ = ∫ s in (0 : ℝ)..x, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        intro s hs
        rw [uIoo_of_ge hx] at hs
        exact riemannData_of_neg _ _ hs.2
      _ = -|x| := by rw [abs_of_nonpos hx]; cas

/-- The primitive of the step datum is not convex. -/
theorem compressiveData_primitive_not_convex :
    ¬ ConvexOn ℝ univ (fun x ↦ ∫ s in (0 : ℝ)..x, riemannData (1 : ℝ) (-1) s) := by
  intro h
  have hc := h.2 (show (-1 : ℝ) ∈ univ from mem_univ _)
    (show (1 : ℝ) ∈ univ from mem_univ _)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  norm_num [compressiveData_primitive, smul_eq_mul] at hc

/-- For footpoints `y ≤ 0` the cost is a completed square in `y`. -/
theorem compressive_cost_of_nonpos (a b : ℝ) {t : ℝ} (ht : 0 < t)
    (x y : ℝ) (hy : y ≤ 0) :
    -|y| + t * HopfLax1D.legendreTransform (affineQuadraticFlux a b) ((x - y) / t) =
      (y - (x - a * t - t)) ^ 2 / (2 * t) + (x - a * t) - t / 2 - b * t := by
  rw [affineQuadraticFlux_legendre, abs_of_nonpos hy]
  cas using ht

/-- For footpoints `y ≥ 0` the cost is a completed square in `y`. -/
theorem compressive_cost_of_nonneg (a b : ℝ) {t : ℝ} (ht : 0 < t)
    (x y : ℝ) (hy : 0 ≤ y) :
    -|y| + t * HopfLax1D.legendreTransform (affineQuadraticFlux a b) ((x - y) / t) =
      (y - (x - a * t + t)) ^ 2 / (2 * t) - (x - a * t) - t / 2 - b * t := by
  rw [affineQuadraticFlux_legendre, abs_of_nonneg hy]
  cas using ht

/-- The cost is at least `-|x - a t| - t/2 - b t` for every footpoint `y`. -/
theorem compressive_cost_lower (a b : ℝ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    -|x - a * t| - t / 2 - b * t ≤
      -|y| + t * HopfLax1D.legendreTransform (affineQuadraticFlux a b) ((x - y) / t) := by
  rcases le_total y 0 with hy | hy
  · rw [compressive_cost_of_nonpos a b ht x y hy]
    have hs := div_nonneg (sq_nonneg (y - (x - a * t - t))) (by positivity : 0 ≤ 2 * t)
    linarith only [hs, neg_abs_le (x - a * t)]
  · rw [compressive_cost_of_nonneg a b ht x y hy]
    have hs := div_nonneg (sq_nonneg (y - (x - a * t + t))) (by positivity : 0 ≤ 2 * t)
    linarith only [hs, le_abs_self (x - a * t)]

/-- The Hopf–Lax value is `-|x - a t| - t/2 - b t`, with a cusp at the shock `x = a t`. -/
theorem compressive_value (a b : ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    value (HopfLax1D.legendreTransform (affineQuadraticFlux a b))
      (fun y ↦ ∫ s in (0 : ℝ)..y, riemannData (1 : ℝ) (-1) s) t x =
      -|x - a * t| - t / 2 - b * t := by
  have hF := affineQuadraticFlux_contDiff a b
  have hlower : ∀ r, (1 : ℝ) ≤ deriv (deriv (affineQuadraticFlux a b)) r := by
    intro r
    rw [affineQuadraticFlux_deriv2]
  have hraw := laxOleinik_formula_of_deriv2_lower_bound hF (by norm_num) hlower
    compressiveData_memLp
  have hs := ((hraw.1 t ht).1 x)
  have hh := lipschitzWith_intervalIntegral_of_memLp_top compressiveData_memLp 0
  have hp : (fun y ↦ ∫ s in (0 : ℝ)..y, riemannData (1 : ℝ) (-1) s) =
      fun y ↦ -|y| := funext compressiveData_primitive
  rw [hp] at hh hs ⊢
  have hL := superlinear_scalar_legendre
    (legendreFinite_of_deriv2_lower_bound hF (by norm_num) hlower)
  apply le_antisymm
  · rcases le_total (x - a * t) 0 with hx | hx
    · have h := value_le_fixed_footpoint hL hh ht x (x - a * t - t)
      rw [compressive_cost_of_nonpos a b ht _ _ (by linarith)] at h
      simpa [abs_of_nonpos hx] using h
    · have h := value_le_fixed_footpoint hL hh ht x (x - a * t + t)
      rw [compressive_cost_of_nonneg a b ht _ _ (by linarith)] at h
      simpa [abs_of_nonneg hx] using h
  · rw [hs]
    exact compressive_cost_lower a b ht x _

/-- The complete set of minimizers: the left branch is available when
`x ≤ a t`, the right branch when `a t ≤ x`, and both occur at equality. -/
theorem compressive_minimizer_iff (a b : ℝ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    (value (HopfLax1D.legendreTransform (affineQuadraticFlux a b))
      (fun z ↦ ∫ s in (0 : ℝ)..z, riemannData (1 : ℝ) (-1) s) t x =
      (∫ s in (0 : ℝ)..y, riemannData (1 : ℝ) (-1) s) +
        t * HopfLax1D.legendreTransform (affineQuadraticFlux a b) ((x - y) / t)) ↔
      (y = x - a * t - t ∧ x - a * t ≤ 0) ∨
      (y = x - a * t + t ∧ 0 ≤ x - a * t) := by
  rw [compressive_value a b ht, compressiveData_primitive]
  have ht₂ : 0 < 2 * t := by positivity
  constructor
  · intro heq
    rcases le_total y 0 with hy | hy
    · rw [compressive_cost_of_nonpos a b ht x y hy] at heq
      have hs := div_nonneg (sq_nonneg (y - (x - a * t - t))) ht₂.le
      have hz : (y - (x - a * t - t)) ^ 2 / (2 * t) = 0 := by
        linarith only [heq, hs, neg_abs_le (x - a * t)]
      have hy' := sq_eq_zero_iff.mp ((div_eq_zero_iff.mp hz).resolve_right ht₂.ne')
      exact Or.inl ⟨sub_eq_zero.mp hy', by linarith [abs_nonneg (x - a * t)]⟩
    · rw [compressive_cost_of_nonneg a b ht x y hy] at heq
      have hs := div_nonneg (sq_nonneg (y - (x - a * t + t))) ht₂.le
      have hz : (y - (x - a * t + t)) ^ 2 / (2 * t) = 0 := by
        linarith only [heq, hs, le_abs_self (x - a * t)]
      have hy' := sq_eq_zero_iff.mp ((div_eq_zero_iff.mp hz).resolve_right ht₂.ne')
      exact Or.inr ⟨sub_eq_zero.mp hy', by linarith [abs_nonneg (x - a * t)]⟩
  · rintro (⟨rfl, hx⟩ | ⟨rfl, hx⟩)
    · rw [compressive_cost_of_nonpos a b ht _ _ (by linarith)]
      simp [abs_of_nonpos hx]
    · rw [compressive_cost_of_nonneg a b ht _ _ (by linarith)]
      simp [abs_of_nonneg hx]

/-- The exact exceptional set is a nonempty singleton at each positive time. -/
theorem compressive_nonunique_set (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    {x | ¬ ∃! y,
      value (HopfLax1D.legendreTransform (affineQuadraticFlux a b))
        (fun z ↦ ∫ s in (0 : ℝ)..z, riemannData (1 : ℝ) (-1) s) t x =
        (∫ s in (0 : ℝ)..y, riemannData (1 : ℝ) (-1) s) +
          t * HopfLax1D.legendreTransform (affineQuadraticFlux a b) ((x - y) / t)} =
      {a * t} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff, compressive_minimizer_iff a b ht]
  constructor
  · intro h
    by_contra hx
    apply h
    rcases lt_or_gt_of_ne hx with hx | hx
    · refine ⟨x - a * t - t, Or.inl ⟨rfl, by linarith⟩, ?_⟩
      rintro y (⟨hy, _⟩ | ⟨_, hy⟩)
      · exact hy
      · linarith
    · refine ⟨x - a * t + t, Or.inr ⟨rfl, by linarith⟩, ?_⟩
      rintro y (⟨_, hy⟩ | ⟨hy, _⟩)
      · linarith
      · exact hy
  · rintro rfl ⟨y, _, hunique⟩
    have hl := hunique (-t) (Or.inl ⟨by simp, by simp⟩)
    have hr := hunique t (Or.inr ⟨by simp, by simp⟩)
    linarith

/-- Left of the shock, the value has derivative one. -/
theorem compressive_value_hasDerivAt_left (a b : ℝ) {t x : ℝ}
    (ht : 0 < t) (hx : x < a * t) :
    HasDerivAt (value (HopfLax1D.legendreTransform (affineQuadraticFlux a b))
      (fun y ↦ ∫ s in (0 : ℝ)..y, riemannData (1 : ℝ) (-1) s) t) 1 x := by
  have hd : HasDerivAt (fun z : ℝ ↦ z - a * t - t / 2 - b * t) 1 x := by
    cas
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds hx] with z hz
  rw [compressive_value a b ht, abs_of_nonpos (sub_nonpos.mpr hz.le), neg_neg]

/-- Right of the shock, the value has derivative minus one. -/
theorem compressive_value_hasDerivAt_right (a b : ℝ) {t x : ℝ}
    (ht : 0 < t) (hx : a * t < x) :
    HasDerivAt (value (HopfLax1D.legendreTransform (affineQuadraticFlux a b))
      (fun y ↦ ∫ s in (0 : ℝ)..y, riemannData (1 : ℝ) (-1) s) t) (-1) x := by
  have hd : HasDerivAt (fun z : ℝ ↦ -(z - a * t) - t / 2 - b * t) (-1) x := by
    cas
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
  rw [compressive_value a b ht, abs_of_nonneg (sub_nonneg.mpr hz.le)]

end PDE.Examples.ConservationLaw.LaxOleinik
