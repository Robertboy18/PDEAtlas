/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.OpenPos
import PDE.Analysis.Convex.Real.TwoPoint
import PDE.Analysis.MeasureTheory.Integral.Substitution

/-!
# Polarization: the two-point rearrangement

Fix `a` and let `σ = mirror a` be the reflection in the hyperplane of the points at equal
distance from `0` and `a`. The polarization `polarize a u` compares the two values `u x` and
`u (σ x)` and puts the larger one at the point of the pair that is closer to the origin. It
moves the mass of a function towards the origin without changing its distribution and without
raising its difference energies. Iterating it and passing to a limit gives the symmetric
decreasing rearrangement (`exists_radial_antitone`), which is the route to the Pólya–Szegő
inequality and to Talenti's sharp Sobolev constant. This module proves what one polarization
preserves and what it does not increase. The results hold for real functions of any sign,
except `polarize_eq_zero_of_lt`: a nonnegative function that vanishes outside a ball still
vanishes there after polarization.

## Main results

* `mirror`, with `mirror_apply_eq`, `norm_mirror`, `mirror_dist_sq` and `exists_mirror_eq`: the
  reflection in every real inner product space and for every `a`, its formula,
  `|σ x| = |x - a|`, the identity that compares `|x - σ y|` with `|x - y|`, and a reflection
  that maps `x` to a given `y` with `|x| ≠ |y|`. `mirror a` is Mathlib's
  `EuclideanGeometry.reflection` in `AffineSubspace.perpBisector 0 a`, as an isometry.
* `polarize` and `polarize_pair`: on every pair `{x, σ x}` the polarization of a real function
  takes the same two values as the function. `LipschitzWith.polarize`: the Lipschitz constant
  does not increase. `lintegral_comp_polarize`: on a finite-dimensional space the integral of
  `ψ (u x)` does not change, for all measurable `u` and `ψ`.
* `diffEnergy_polarize_le`: the difference energy `∬_{|x - y| ≤ t} j (u x - u y) dx dy` does not
  increase, for every measurable `u`, every convex `j ≥ 0` on the line and every `t`.
* `secondMoment_polarize_le` and `le_of_secondMoment_le_secondMoment_polarize`: for every
  continuous `u` with compact support the second moment `∫ u(x) |x|² dx` does not increase, and
  equality forces `u (σ x) ≤ u x` on the side of the origin.

## How it works

Nothing changes but the values on each pair `{x, σ x}`, which are swapped or not. So every fact
follows by looking at one pair, or at two pairs, at a time. The integral of `ψ (u x)` sums `ψ`
over the two values of each pair. For the difference energy, two points on the same side of the
hyperplane are closer to each other than one of them is to the mirror image of the other
(`mirror_dist_sq`), and for a convex `j` it is cheaper to pair the larger values with each other
(`four_point_le`). For the second moment, the larger value moves to the point of smaller norm.

## References

* F. Brock and A. Yu. Solynin, "An approach to symmetrization via polarization",
  *Trans. Amer. Math. Soc.* 352 (2000), 1759-1796: polarization, and what it preserves.
  <https://doi.org/10.1090/S0002-9947-99-02558-1>
* A. Baernstein II, "A unified approach to symmetrization", in *Partial differential equations
  of elliptic type* (Cortona, 1992), Symposia Mathematica 35, Cambridge University Press, 1994,
  47-91: the two-point inequality for convex costs.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Metric Function
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace PDE.Analysis.Rearrangement

/-! ## The reflection that swaps `0` and `a` -/

section Mirror

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The reflection of `E` in the hyperplane of the points at equal distance from `0` and `a`:
Mathlib's `EuclideanGeometry.reflection` in the perpendicular bisector of `0` and `a`, as an
isometry. It swaps `0` and `a`. For `a = 0` it is the identity. -/
def mirror (a : E) : E ≃ᵢ E :=
  (EuclideanGeometry.reflection (AffineSubspace.perpBisector (0 : E) a)).toIsometryEquiv

/-- `mirror a` is the reflection in the perpendicular bisector of `0` and `a`. -/
theorem mirror_apply (a x : E) :
    mirror a x = EuclideanGeometry.reflection (AffineSubspace.perpBisector (0 : E) a) x := rfl

/-- The reflection `mirror a` is an involution. -/
@[simp]
theorem mirror_mirror (a x : E) : mirror a (mirror a x) = x :=
  EuclideanGeometry.reflection_reflection _ x

/-- The reflection `mirror a` maps the origin to `a`. -/
@[simp]
theorem mirror_apply_zero (a : E) : mirror a 0 = a :=
  EuclideanGeometry.reflection_perpBisector_left 0 a

/-- The reflection `mirror a` maps `a` to the origin. -/
@[simp]
theorem mirror_apply_self (a : E) : mirror a a = 0 :=
  EuclideanGeometry.reflection_perpBisector_right a 0

/-- The image of `x` is as far from the origin as `x` is from `a`. -/
theorem norm_mirror (a x : E) : ‖mirror a x‖ = ‖x - a‖ := by
  have h := (mirror a).dist_eq x a
  rwa [mirror_apply_self, dist_zero_right, dist_eq_norm] at h

/-- The reflection in coordinates: `mirror a x = x + (1 - 2 ⟪a, x⟫ / |a|²) a`. The point
`x - c a` with `c = ⟪a, x⟫ / |a|² - 1/2` lies on the hyperplane and `c a` is orthogonal to
it. -/
theorem mirror_apply_eq (a x : E) : mirror a x = x + (1 - 2 * ⟪a, x⟫ / ‖a‖ ^ 2) • a := by
  have hp : x - (⟪a, x⟫ / ‖a‖ ^ 2 - 1 / 2) • a ∈ AffineSubspace.perpBisector (0 : E) a := by
    rw [AffineSubspace.mem_perpBisector_iff_inner_eq]
    simp only [vsub_eq_sub, sub_zero, dist_zero_left]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm a x]
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · have hA : ‖a‖ ^ 2 ≠ 0 := by positivity
      field_simp
      ring
  have hv : (⟪a, x⟫ / ‖a‖ ^ 2 - 1 / 2) • a ∈
      (AffineSubspace.perpBisector (0 : E) a).directionᗮ := by
    rw [AffineSubspace.direction_perpBisector, vsub_eq_sub, sub_zero]
    exact Submodule.le_orthogonal_orthogonal _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a))
  have h := EuclideanGeometry.reflection_orthogonal_vadd hp hv
  rw [vadd_eq_add, vadd_eq_add, add_sub_cancel] at h
  rw [mirror_apply, h]
  module

/-- For `a = 0` the reflection is the identity. -/
@[simp]
theorem mirror_zero (x : E) : mirror (0 : E) x = x := by
  simp [mirror_apply_eq]

/-- The identity behind every comparison of distances: `|a|² (|x - σ y|² - |x - y|²) =
(|σ x|² - |x|²) (|σ y|² - |y|²)`. The right side is positive when `x` and `y` lie strictly on
the same side of the hyperplane, and negative when they lie on different sides. -/
theorem mirror_dist_sq (a x y : E) :
    ‖a‖ ^ 2 * (dist x (mirror a y) ^ 2 - dist x y ^ 2) =
      (‖mirror a x‖ ^ 2 - ‖x‖ ^ 2) * (‖mirror a y‖ ^ 2 - ‖y‖ ^ 2) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hA : ‖a‖ ^ 2 ≠ 0 := by positivity
  have h1 : dist x (mirror a y) ^ 2 = dist x y ^ 2
      - 2 * (1 - 2 * ⟪a, y⟫ / ‖a‖ ^ 2) * (⟪a, x⟫ - ⟪a, y⟫)
      + (1 - 2 * ⟪a, y⟫ / ‖a‖ ^ 2) ^ 2 * ‖a‖ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, mirror_apply_eq, ← sub_sub, norm_sub_sq_real,
      real_inner_smul_right, inner_sub_left, real_inner_comm a x, real_inner_comm a y, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have h2 (z : E) : ‖mirror a z‖ ^ 2 = ‖z‖ ^ 2 - 2 * ⟪a, z⟫ + ‖a‖ ^ 2 := by
    rw [norm_mirror, norm_sub_sq_real, real_inner_comm a z]
  rw [h1, h2 x, h2 y]
  field_simp
  ring

/-- Two points on different sides of the hyperplane: reflecting one of them brings it closer
to the other. -/
theorem dist_mirror_le {a x y : E}
    (h : (‖mirror a x‖ - ‖x‖) * (‖mirror a y‖ - ‖y‖) ≤ 0) :
    dist x (mirror a y) ≤ dist x y := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hA : 0 < ‖a‖ ^ 2 := by positivity
  have h' : (‖mirror a x‖ ^ 2 - ‖x‖ ^ 2) * (‖mirror a y‖ ^ 2 - ‖y‖ ^ 2) ≤ 0 := by
    have e : (‖mirror a x‖ ^ 2 - ‖x‖ ^ 2) * (‖mirror a y‖ ^ 2 - ‖y‖ ^ 2) =
        (‖mirror a x‖ - ‖x‖) * (‖mirror a y‖ - ‖y‖) *
          ((‖mirror a x‖ + ‖x‖) * (‖mirror a y‖ + ‖y‖)) := by ring
    rw [e]
    exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)
  rw [← mirror_dist_sq] at h'
  have h'' : dist x (mirror a y) ^ 2 ≤ dist x y ^ 2 := by
    by_contra hc
    exact absurd h' (not_le.mpr (mul_pos hA (sub_pos.mpr (not_le.mp hc))))
  exact (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).mp h''

/-- Two points on the same side of the hyperplane: reflecting one of them takes it farther
from the other. This is `dist_mirror_le` for `x` and the mirror image of `y`. -/
theorem dist_le_dist_mirror {a x y : E}
    (h : 0 ≤ (‖mirror a x‖ - ‖x‖) * (‖mirror a y‖ - ‖y‖)) :
    dist x y ≤ dist x (mirror a y) := by
  have h' := dist_mirror_le (a := a) (x := x) (y := mirror a y)
    (by rw [mirror_mirror]; linarith)
  rwa [mirror_mirror] at h'

/-- A point as far from the origin as its mirror image lies on the hyperplane. -/
theorem mirror_eq_self_of_norm_eq {a x : E} (h : ‖mirror a x‖ = ‖x‖) : mirror a x = x := by
  rw [mirror_apply, EuclideanGeometry.reflection_eq_self_iff,
    AffineSubspace.mem_perpBisector_iff_dist_eq, dist_zero_right, dist_eq_norm, ← norm_mirror a x,
    h]

/-- The distance from a mirror image to a point is the distance from the point's mirror image
to the original. -/
theorem dist_mirror_left (a x y : E) : dist (mirror a x) y = dist x (mirror a y) :=
  (EuclideanGeometry.dist_reflection _ x y).symm

/-- For two points `x`, `y` at different distances from the origin there is a reflection
`mirror a` that maps `x` to `y`: its hyperplane is the perpendicular bisector of `x` and `y`. -/
theorem exists_mirror_eq {x y : E} (h : ‖x‖ ≠ ‖y‖) : ∃ a : E, mirror a x = y := by
  have hxy : y - x ≠ 0 := fun e ↦ h (by rw [sub_eq_zero.mp e])
  have hd0 : ‖y - x‖ ^ 2 ≠ 0 := by positivity
  have hk : ‖y‖ ^ 2 - ‖x‖ ^ 2 ≠ 0 := fun e ↦
    h ((sq_eq_sq₀ (norm_nonneg x) (norm_nonneg y)).mp (sub_eq_zero.mp e).symm)
  have key : ‖y‖ ^ 2 - ‖x‖ ^ 2 - 2 * ⟪y - x, x⟫ = ‖y - x‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm x y]
    ring
  refine ⟨((‖y‖ ^ 2 - ‖x‖ ^ 2) / ‖y - x‖ ^ 2) • (y - x), ?_⟩
  have hs : (1 - 2 * ((‖y‖ ^ 2 - ‖x‖ ^ 2) / ‖y - x‖ ^ 2 * ⟪y - x, x⟫) /
      (((‖y‖ ^ 2 - ‖x‖ ^ 2) / ‖y - x‖ ^ 2) ^ 2 * ‖y - x‖ ^ 2)) *
        ((‖y‖ ^ 2 - ‖x‖ ^ 2) / ‖y - x‖ ^ 2) = 1 := by
    field_simp
    linear_combination key
  rw [mirror_apply_eq, real_inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    smul_smul, hs, one_smul]
  abel

section Measure

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The reflection `mirror a` preserves the volume: it is a linear isometry followed by the
translation by `a`. -/
theorem measurePreserving_mirror (a : E) : MeasurePreserving (mirror a) (volume : Measure E) := by
  have e : ⇑(mirror a) = (· + a) ∘ (EuclideanGeometry.reflection
      (AffineSubspace.perpBisector (0 : E) a)).linearIsometryEquiv := by
    funext x
    have h := (EuclideanGeometry.reflection (AffineSubspace.perpBisector (0 : E) a)).map_vadd
      (0 : E) x
    rwa [vadd_eq_add, add_zero, vadd_eq_add, EuclideanGeometry.reflection_perpBisector_left] at h
  rw [e]
  exact (measurePreserving_add_right volume a).comp (LinearIsometryEquiv.measurePreserving _)

end Measure

end Mirror

/-! ## Polarization -/

section Polarize

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {a x : E} {u : E → ℝ}

/-- The polarization (two-point rearrangement) of `u` with respect to `a`: on each pair
`{x, mirror a x}` the larger of the two values of `u` goes to the point closer to the origin. -/
def polarize (a : E) (u : E → ℝ) (x : E) : ℝ :=
  if ‖x‖ ≤ ‖mirror a x‖ then max (u x) (u (mirror a x)) else min (u x) (u (mirror a x))

/-- At a point that is at least as close to the origin as its mirror image, the polarization
is the larger of the two values. -/
theorem polarize_of_le (h : ‖x‖ ≤ ‖mirror a x‖) :
    polarize a u x = max (u x) (u (mirror a x)) := ite_eq_left h

/-- At a point that is farther from the origin than its mirror image, the polarization is the
smaller of the two values. -/
theorem polarize_of_lt (h : ‖mirror a x‖ < ‖x‖) :
    polarize a u x = min (u x) (u (mirror a x)) := ite_eq_right (not_le.mpr h)

/-- If `x` is at least as close to the origin as its mirror image, the polarization takes the
smaller of the two values at the mirror image. -/
theorem polarize_mirror_of_le (h : ‖x‖ ≤ ‖mirror a x‖) :
    polarize a u (mirror a x) = min (u x) (u (mirror a x)) := by
  rcases h.eq_or_lt with h | h
  · have hx := mirror_eq_self_of_norm_eq h.symm
    rw [hx, polarize_of_le (by rw [hx]), hx, max_self, min_self]
  · rw [polarize_of_lt (by rwa [mirror_mirror]), mirror_mirror, min_comm]

/-- If `x` is farther from the origin than its mirror image, the polarization takes the larger
of the two values at the mirror image. -/
theorem polarize_mirror_of_lt (h : ‖mirror a x‖ < ‖x‖) :
    polarize a u (mirror a x) = max (u x) (u (mirror a x)) := by
  rw [polarize_of_le (by rw [mirror_mirror]; exact h.le), mirror_mirror, max_comm]

/-- On each pair `{x, mirror a x}` the polarization takes the same two values as `u`. -/
theorem polarize_pair (a : E) (u : E → ℝ) (x : E) :
    (polarize a u x = u x ∧ polarize a u (mirror a x) = u (mirror a x)) ∨
      (polarize a u x = u (mirror a x) ∧ polarize a u (mirror a x) = u x) := by
  rcases le_or_gt ‖x‖ ‖mirror a x‖ with h | h
  · rw [polarize_of_le h, polarize_mirror_of_le h]
    rcases le_total (u x) (u (mirror a x)) with h' | h'
    · exact Or.inr ⟨max_eq_right h', min_eq_left h'⟩
    · exact Or.inl ⟨max_eq_left h', min_eq_right h'⟩
  · rw [polarize_of_lt h, polarize_mirror_of_lt h]
    rcases le_total (u x) (u (mirror a x)) with h' | h'
    · exact Or.inl ⟨min_eq_left h', max_eq_right h'⟩
    · exact Or.inr ⟨min_eq_right h', max_eq_left h'⟩

/-- The values of the polarization are values of `u`. -/
theorem polarize_mem {s : Set ℝ} (h : ∀ x, u x ∈ s) (a x : E) : polarize a u x ∈ s := by
  rcases polarize_pair a u x with h' | h' <;> rw [h'.1] <;> exact h _

/-- A nonnegative function that vanishes outside the closed ball of radius `R` keeps this
property: polarization moves mass towards the origin. -/
theorem polarize_eq_zero_of_lt {R : ℝ} (h0 : ∀ x, 0 ≤ u x) (hR : ∀ x, R < ‖x‖ → u x = 0) (a : E)
    (hx : R < ‖x‖) : polarize a u x = 0 := by
  rcases le_or_gt ‖x‖ ‖mirror a x‖ with h | h
  · rw [polarize_of_le h, hR x hx, hR _ (hx.trans_le h), max_self]
  · rw [polarize_of_lt h, hR x hx, min_eq_left (h0 _)]

/-- Polarization is continuous for pointwise convergence of functions. -/
theorem continuous_polarize (a : E) : Continuous (polarize a : (E → ℝ) → E → ℝ) := by
  refine continuous_pi fun x ↦ ?_
  rcases le_or_gt ‖x‖ ‖mirror a x‖ with h | h
  · have e : (fun u : E → ℝ ↦ polarize a u x) = fun u ↦ max (u x) (u (mirror a x)) :=
      funext fun u ↦ polarize_of_le h
    rw [e]
    exact (continuous_apply x).max (continuous_apply _)
  · have e : (fun u : E → ℝ ↦ polarize a u x) = fun u ↦ min (u x) (u (mirror a x)) :=
      funext fun u ↦ polarize_of_lt h
    rw [e]
    exact (continuous_apply x).min (continuous_apply _)

/-- The polarization of a continuous function is continuous: on the hyperplane the two
branches of the definition agree. -/
theorem _root_.Continuous.polarize (hu : Continuous u) (a : E) : Continuous (polarize a u) := by
  refine Continuous.if_le (hu.max (hu.comp (mirror a).continuous))
    (hu.min (hu.comp (mirror a).continuous)) continuous_norm
    (continuous_norm.comp (mirror a).continuous) fun x hx ↦ ?_
  rw [mirror_eq_self_of_norm_eq hx.symm, max_self, min_self]

/-- The polarization of a function with compact support has compact support. -/
theorem _root_.HasCompactSupport.polarize (hu : HasCompactSupport u) (a : E) :
    HasCompactSupport (polarize a u) := by
  refine HasCompactSupport.intro (hu.isCompact.union (hu.isCompact.image (mirror a).continuous))
    fun x hx ↦ ?_
  have h1 : u x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (Or.inl h)
  have h2 : u (mirror a x) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (Or.inr ⟨_, h, mirror_mirror a x⟩)
  rcases polarize_pair a u x with h | h <;> rw [h.1] <;> assumption

/-- Polarization does not increase the Lipschitz constant. -/
theorem _root_.LipschitzWith.polarize {L : ℝ≥0} (hu : LipschitzWith L u) (a : E) :
    LipschitzWith L (polarize a u) := by
  -- the mixed case: `x` on the side of the origin, `y` strictly on the other side
  have mixed {x y : E} (hx : ‖x‖ ≤ ‖mirror a x‖) (hy : ‖mirror a y‖ < ‖y‖) :
      |max (u x) (u (mirror a x)) - min (u y) (u (mirror a y))| ≤ L * dist x y := by
    have hd : dist x (mirror a y) ≤ dist x y :=
      dist_mirror_le (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx) (sub_nonpos.mpr hy.le))
    have h1 := hu.dist_le_mul x y
    have h2 := hu.dist_le_mul (mirror a x) (mirror a y)
    have h3 : dist (u x) (u (mirror a y)) ≤ L * dist x y :=
      (hu.dist_le_mul x (mirror a y)).trans (by gcongr)
    have h4 : dist (u (mirror a x)) (u y) ≤ L * dist x y :=
      (hu.dist_le_mul (mirror a x) y).trans (by rw [dist_mirror_left]; gcongr)
    rw [(mirror a).dist_eq] at h2
    rw [Real.dist_eq] at h1 h2 h3 h4
    rcases max_choice (u x) (u (mirror a x)) with h | h <;>
      rcases min_choice (u y) (u (mirror a y)) with h' | h' <;> rw [h, h'] <;> assumption
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have h1 := hu.dist_le_mul x y
  have h2 := hu.dist_le_mul (mirror a x) (mirror a y)
  rw [(mirror a).dist_eq] at h2
  rw [Real.dist_eq] at h1 h2 ⊢
  rcases le_or_gt ‖x‖ ‖mirror a x‖ with hx | hx <;> rcases le_or_gt ‖y‖ ‖mirror a y‖ with hy | hy
  · rw [polarize_of_le hx, polarize_of_le hy]
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le h1 h2)
  · rw [polarize_of_le hx, polarize_of_lt hy]
    exact mixed hx hy
  · rw [polarize_of_lt hx, polarize_of_le hy, abs_sub_comm, dist_comm]
    exact mixed hy hx
  · rw [polarize_of_lt hx, polarize_of_lt hy]
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le h1 h2)

/-- The two maps `id` and `mirror a`, indexed by `Bool`. -/
def mirrorPow (a : E) : Bool → E → E
  | true => mirror a
  | false => id

/-- The map with the index `true` is the reflection. -/
@[simp] theorem mirrorPow_true (a x : E) : mirrorPow a true x = mirror a x := rfl

/-- The map with the index `false` is the identity. -/
@[simp] theorem mirrorPow_false (a x : E) : mirrorPow a false x = x := rfl

variable [MeasurableSpace E] [BorelSpace E]

/-- The polarization of a measurable function is measurable. -/
theorem _root_.Measurable.polarize (hu : Measurable u) (a : E) : Measurable (polarize a u) :=
  Measurable.ite (measurableSet_le measurable_norm
      (measurable_norm.comp (mirror a).continuous.measurable))
    (hu.max (hu.comp (mirror a).continuous.measurable))
    (hu.min (hu.comp (mirror a).continuous.measurable))

variable [FiniteDimensional ℝ E]

/-- Both maps `id` and `mirror a` preserve the volume. -/
theorem measurePreserving_mirrorPow (a : E) (b : Bool) :
    MeasurePreserving (mirrorPow a b) (volume : Measure E) := by
  cases b
  · exact MeasurePreserving.id _
  · exact measurePreserving_mirror a

/-- **Polarization is a rearrangement.** For measurable `u` and `ψ`, the integral of
`ψ (u x)` over the whole space does not change under polarization. -/
theorem lintegral_comp_polarize (a : E) (hu : Measurable u) {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ x, ψ (polarize a u x) = ∫⁻ x, ψ (u x) := by
  refine lintegral_eq_of_sum_comp_eq (measurePreserving_mirrorPow a) (hψ.comp (hu.polarize a))
    (hψ.comp hu) fun x ↦ ?_
  simp only [Fintype.sum_bool, mirrorPow_true, mirrorPow_false]
  rcases polarize_pair a u x with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, add_comm]

end Polarize

/-! ## The difference energy -/

section Energy

variable {j : ℝ → ℝ}

/-- The four-point inequality with both pairs sorted the same way. The weight `κ₁` of the
pairs `(a, c)`, `(b, d)` is at least the weight `κ₂` of the pairs `(a, d)`, `(b, c)`. -/
theorem four_point_le (hj : ConvexOn ℝ univ j) (hj0 : ∀ s, 0 ≤ j s) (a b c d : ℝ)
    {κ₁ κ₂ : ℝ≥0∞} (hκ : κ₂ ≤ κ₁) :
    κ₁ * (ENNReal.ofReal (j (max a b - max c d)) + ENNReal.ofReal (j (min a b - min c d))) +
        κ₂ * (ENNReal.ofReal (j (max a b - min c d)) + ENNReal.ofReal (j (min a b - max c d))) ≤
      κ₁ * (ENNReal.ofReal (j (a - c)) + ENNReal.ofReal (j (b - d))) +
        κ₂ * (ENNReal.ofReal (j (a - d)) + ENNReal.ofReal (j (b - c))) := by
  have hA : ENNReal.ofReal (j (max a b - max c d)) + ENNReal.ofReal (j (min a b - min c d)) ≤
      ENNReal.ofReal (j (a - c)) + ENNReal.ofReal (j (b - d)) := by
    rw [← ENNReal.ofReal_add (hj0 _) (hj0 _), ← ENNReal.ofReal_add (hj0 _) (hj0 _)]
    exact ENNReal.ofReal_le_ofReal
      (hj.map_max_sub_max_add_map_min_sub_min_le (mem_univ _) (mem_univ _))
  have hsum : ENNReal.ofReal (j (max a b - max c d)) + ENNReal.ofReal (j (min a b - min c d)) +
      (ENNReal.ofReal (j (max a b - min c d)) + ENNReal.ofReal (j (min a b - max c d))) =
      ENNReal.ofReal (j (a - c)) + ENNReal.ofReal (j (b - d)) +
        (ENNReal.ofReal (j (a - d)) + ENNReal.ofReal (j (b - c))) := by
    rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd <;>
      simp only [max_eq_right, max_eq_left, min_eq_left, min_eq_right, hab, hcd] <;> abel
  obtain ⟨δ, rfl⟩ := exists_add_of_le hκ
  calc _ = κ₂ * (ENNReal.ofReal (j (max a b - max c d)) +
          ENNReal.ofReal (j (min a b - min c d)) +
          (ENNReal.ofReal (j (max a b - min c d)) + ENNReal.ofReal (j (min a b - max c d)))) +
        δ * (ENNReal.ofReal (j (max a b - max c d)) +
          ENNReal.ofReal (j (min a b - min c d))) := by ring
    _ ≤ κ₂ * (ENNReal.ofReal (j (a - c)) + ENNReal.ofReal (j (b - d)) +
          (ENNReal.ofReal (j (a - d)) + ENNReal.ofReal (j (b - c)))) +
        δ * (ENNReal.ofReal (j (a - c)) + ENNReal.ofReal (j (b - d))) := by
      rw [hsum]
      gcongr
    _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

/-- The weight of the difference energy: `1` on the pairs of points at distance at most `t`,
and `0` on the others. -/
def nearWeight (t : ℝ) (x y : E) : ℝ≥0∞ := if dist x y ≤ t then 1 else 0

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The weight of the pair `(σ x, y)` is the weight of the pair `(x, σ y)`. -/
theorem nearWeight_mirror_left (t : ℝ) (a x y : E) :
    nearWeight t (mirror a x) y = nearWeight t x (mirror a y) := by
  simp only [nearWeight, dist_mirror_left]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A closer pair has the larger weight. -/
theorem nearWeight_mono {t : ℝ} {x y x' y' : E} (h : dist x y ≤ dist x' y') :
    nearWeight t x' y' ≤ nearWeight t x y := by
  by_cases h1 : dist x' y' ≤ t
  · simp [nearWeight, h1, h.trans h1]
  · simp [nearWeight, h1]

/-- The weight is measurable on the product. -/
theorem measurable_nearWeight (t : ℝ) : Measurable fun z : E × E ↦ nearWeight t z.1 z.2 :=
  Measurable.ite (measurableSet_le (measurable_fst.dist measurable_snd) measurable_const)
    measurable_const measurable_const

/-- The difference energy of `u` at scale `t` with the cost `j`: the integral of
`j (u x - u y)` over the pairs of points at distance at most `t`. -/
def diffEnergy (j : ℝ → ℝ) (t : ℝ) (u : E → ℝ) : ℝ≥0∞ :=
  ∫⁻ z : E × E, nearWeight t z.1 z.2 * ENNReal.ofReal (j (u z.1 - u z.2))
    ∂((volume : Measure E).prod volume)

/-- The integrand of the difference energy is measurable. -/
theorem measurable_diffEnergy_integrand (hj : Measurable j) (t : ℝ) {u : E → ℝ}
    (hu : Measurable u) :
    Measurable fun z : E × E ↦ nearWeight t z.1 z.2 * ENNReal.ofReal (j (u z.1 - u z.2)) :=
  (measurable_nearWeight t).mul (ENNReal.measurable_ofReal.comp
    (hj.comp ((hu.comp measurable_fst).sub (hu.comp measurable_snd))))

/-- **Polarization does not increase the difference energy.** For a convex cost `j ≥ 0`, every
scale `t` and every measurable `u`. The proof compares, for each `x` and `y`, the four pairs
made of `x` or its mirror image and `y` or its mirror image. -/
theorem diffEnergy_polarize_le (hj : ConvexOn ℝ univ j) (hj0 : ∀ s, 0 ≤ j s) (t : ℝ) (a : E)
    {u : E → ℝ} (hu : Measurable u) :
    diffEnergy j t (polarize a u) ≤ diffEnergy j t u := by
  have hjm : Measurable j :=
    (continuousOn_univ.mp (hj.continuousOn isOpen_univ)).measurable
  refine lintegral_le_of_sum_comp_le
    (T := fun b : Bool × Bool ↦ Prod.map (mirrorPow a b.1) (mirrorPow a b.2))
    (fun b ↦ (measurePreserving_mirrorPow a b.1).prod (measurePreserving_mirrorPow a b.2))
    (measurable_diffEnergy_integrand hjm t (hu.polarize a))
    (measurable_diffEnergy_integrand hjm t hu) ?_
  rintro ⟨x, y⟩
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mirrorPow_true, mirrorPow_false,
    Prod.map_apply, nearWeight_mirror_left, mirror_mirror]
  -- the weight of the pairs on the same level against the weight of the crossed pairs
  have same (h : 0 ≤ (‖mirror a x‖ - ‖x‖) * (‖mirror a y‖ - ‖y‖)) :
      nearWeight t x (mirror a y) ≤ nearWeight t x y := nearWeight_mono (dist_le_dist_mirror h)
  have diff (h : (‖mirror a x‖ - ‖x‖) * (‖mirror a y‖ - ‖y‖) ≤ 0) :
      nearWeight t x y ≤ nearWeight t x (mirror a y) := nearWeight_mono (dist_mirror_le h)
  rcases le_or_gt ‖x‖ ‖mirror a x‖ with hx | hx <;> rcases le_or_gt ‖y‖ ‖mirror a y‖ with hy | hy
  · rw [polarize_of_le hx, polarize_of_le hy, polarize_mirror_of_le hx, polarize_mirror_of_le hy]
    have h := four_point_le hj hj0 (u x) (u (mirror a x)) (u y) (u (mirror a y))
      (same (mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)))
    calc _ = _ := by ring
      _ ≤ _ := h
      _ = _ := by ring
  · rw [polarize_of_le hx, polarize_of_lt hy, polarize_mirror_of_le hx, polarize_mirror_of_lt hy]
    have h := four_point_le hj hj0 (u x) (u (mirror a x)) (u (mirror a y)) (u y)
      (diff (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx) (sub_nonpos.mpr hy.le)))
    rw [max_comm (u (mirror a y)), min_comm (u (mirror a y))] at h
    calc _ = _ := by ring
      _ ≤ _ := h
      _ = _ := by ring
  · rw [polarize_of_lt hx, polarize_of_le hy, polarize_mirror_of_lt hx, polarize_mirror_of_le hy]
    have h := four_point_le hj hj0 (u x) (u (mirror a x)) (u (mirror a y)) (u y)
      (diff (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.le) (sub_nonneg.mpr hy)))
    rw [max_comm (u (mirror a y)), min_comm (u (mirror a y))] at h
    calc _ = _ := by ring
      _ ≤ _ := h
      _ = _ := by ring
  · rw [polarize_of_lt hx, polarize_of_lt hy, polarize_mirror_of_lt hx, polarize_mirror_of_lt hy]
    have h := four_point_le hj hj0 (u x) (u (mirror a x)) (u y) (u (mirror a y))
      (same (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx.le) (sub_nonpos.mpr hy.le)))
    calc _ = _ := by ring
      _ ≤ _ := h
      _ = _ := by ring

end Energy

/-! ## The second moment -/

section Moment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {a : E} {u : E → ℝ}

/-- The gain of the second moment on a pair: `(u x - (polarize a u) x) (|x|² - |σ x|²)`. It is
nonnegative, and its integral is twice the decrease of the second moment
(`integral_secondMoment_gain`). -/
theorem secondMoment_gain_nonneg (a : E) (u : E → ℝ) (x : E) :
    0 ≤ (u x - polarize a u x) * (‖x‖ ^ 2 - ‖mirror a x‖ ^ 2) := by
  rcases le_or_gt ‖x‖ ‖mirror a x‖ with h | h
  · rw [polarize_of_le h]
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (le_max_left _ _))
      (sub_nonpos.mpr (pow_le_pow_left₀ (norm_nonneg _) h 2))
  · rw [polarize_of_lt h]
    exact mul_nonneg (sub_nonneg.mpr (min_le_left _ _))
      (sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) h.le 2))

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The second moment `∫ u(x) |x|² dx` of a function. -/
def secondMoment (u : E → ℝ) : ℝ := ∫ x, u x * ‖x‖ ^ 2

/-- The integral of the gain on a pair is twice the decrease of the second moment. -/
theorem integral_secondMoment_gain (a : E) (hu : Continuous u) (hc : HasCompactSupport u) :
    ∫ x, (u x - polarize a u x) * (‖x‖ ^ 2 - ‖mirror a x‖ ^ 2) =
      2 * (secondMoment u - secondMoment (polarize a u)) := by
  have hn : Continuous fun x : E ↦ ‖x‖ ^ 2 := continuous_norm.pow 2
  have hi1 : Integrable fun x ↦ u x * ‖x‖ ^ 2 :=
    (hu.mul hn).integrable_of_hasCompactSupport hc.mul_right
  have hi2 : Integrable fun x ↦ polarize a u x * ‖x‖ ^ 2 :=
    ((hu.polarize a).mul hn).integrable_of_hasCompactSupport (hc.polarize a).mul_right
  have hg : Integrable fun x ↦ (u x - polarize a u x) * ‖x‖ ^ 2 :=
    ((hu.sub (hu.polarize a)).mul hn).integrable_of_hasCompactSupport
      (hc.sub (hc.polarize a)).mul_right
  have hpair (x : E) : (u x - polarize a u x) * (‖x‖ ^ 2 - ‖mirror a x‖ ^ 2) =
      (u x - polarize a u x) * ‖x‖ ^ 2 +
        (u (mirror a x) - polarize a u (mirror a x)) * ‖mirror a x‖ ^ 2 := by
    rcases polarize_pair a u x with h | h <;> rw [h.1, h.2] <;> ring
  have hcomp : ∫ x, (u (mirror a x) - polarize a u (mirror a x)) * ‖mirror a x‖ ^ 2 =
      ∫ x, (u x - polarize a u x) * ‖x‖ ^ 2 :=
    (measurePreserving_mirror a).integral_comp (mirror a).toHomeomorph.measurableEmbedding
      fun x ↦ (u x - polarize a u x) * ‖x‖ ^ 2
  have hg' : Integrable fun x ↦
      (u (mirror a x) - polarize a u (mirror a x)) * ‖mirror a x‖ ^ 2 :=
    (measurePreserving_mirror a).integrable_comp_of_integrable hg
  simp only [hpair]
  rw [integral_add hg hg', hcomp]
  simp only [sub_mul]
  rw [integral_sub hi1 hi2, secondMoment, secondMoment]
  ring

/-- **Polarization does not increase the second moment** of a continuous function with compact
support. -/
theorem secondMoment_polarize_le (a : E) (hu : Continuous u) (hc : HasCompactSupport u) :
    secondMoment (polarize a u) ≤ secondMoment u := by
  have h := integral_nonneg (μ := (volume : Measure E))
    (f := fun x ↦ (u x - polarize a u x) * (‖x‖ ^ 2 - ‖mirror a x‖ ^ 2))
    (secondMoment_gain_nonneg a u)
  rw [integral_secondMoment_gain a hu hc] at h
  linarith

/-- **Rigidity.** If polarization does not decrease the second moment of a continuous function
with compact support, the function is already polarized: `u (σ x) ≤ u x` whenever `x` is
closer to the origin than its mirror image `σ x`. -/
theorem le_of_secondMoment_le_secondMoment_polarize (hu : Continuous u) (hc : HasCompactSupport u)
    (h : secondMoment u ≤ secondMoment (polarize a u)) {x : E} (hx : ‖x‖ < ‖mirror a x‖) :
    u (mirror a x) ≤ u x := by
  have hn : Continuous fun x : E ↦ ‖x‖ ^ 2 := continuous_norm.pow 2
  have hD : Continuous fun x ↦ (u x - polarize a u x) * (‖x‖ ^ 2 - ‖mirror a x‖ ^ 2) :=
    (hu.sub (hu.polarize a)).mul (hn.sub (hn.comp (mirror a).continuous))
  have hDc : HasCompactSupport fun x ↦
      (u x - polarize a u x) * (‖x‖ ^ 2 - ‖mirror a x‖ ^ 2) :=
    (hc.sub (hc.polarize a)).mul_right
  have h0 : ∫ x, (u x - polarize a u x) * (‖x‖ ^ 2 - ‖mirror a x‖ ^ 2) = 0 := by
    have := secondMoment_polarize_le a hu hc
    rw [integral_secondMoment_gain a hu hc]
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg (secondMoment_gain_nonneg a u)
    (hD.integrable_of_hasCompactSupport hDc)).mp h0
  have hall : (u x - polarize a u x) * (‖x‖ ^ 2 - ‖mirror a x‖ ^ 2) = 0 :=
    congrFun ((hD.ae_eq_iff_eq volume continuous_zero).mp hae) x
  rw [polarize_of_le hx.le] at hall
  have hne : ‖x‖ ^ 2 - ‖mirror a x‖ ^ 2 ≠ 0 :=
    (sub_neg.mpr (pow_lt_pow_left₀ hx (norm_nonneg _) two_ne_zero)).ne
  have hz : u x - max (u x) (u (mirror a x)) = 0 := by
    simpa [hne] using hall
  linarith [le_max_right (u x) (u (mirror a x))]

end Moment

end PDE.Analysis.Rearrangement
