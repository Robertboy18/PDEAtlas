/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.AbsolutelyContinuous.FiniteDimension
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Variational
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The path-space action and the Hopf–Lax formula

For a convex Lagrangian in any finite-dimensional real normed space, Jensen's
inequality and the fundamental theorem of calculus show that the straight
path minimizes action between fixed endpoints. Consequently

`inf_γ (g(γ(0)) + ∫ s in 0..t, L(deriv γ s))`

equals `value L g t x`, the Hopf–Lax infimum over velocities, and hence its
usual footpoint formula. The competitors are absolutely continuous
paths with terminal point `x`. Their action is required to be integrable
because the infimum here is real-valued; this is the finite-action problem.

Superlinearity and Lipschitz data supply the lower bound and compact
attainment. In particular, all results apply to Euclidean space in arbitrary dimension.

This is Theorem 4 of Evans, §3.3.2, which defines the value (17) as an infimum over `C¹` paths
and proves the footpoint formula (21) by Jensen's inequality; Evans leaves the attainment of the
minimum as an exercise. Our competitors are absolutely continuous instead.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), definition (17) and Theorem 4 with its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

open MeasureTheory Set PDE.Analysis

set_option linter.missingDocs true

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An absolutely continuous path with prescribed terminal point and finite
Lagrangian action. The derivative is the vector derivative of `curve`. -/
structure AdmissiblePath (L : E → ℝ) (t : ℝ) (x : E) where
  /-- The path, defined on the real line and used on `[0,t]`. -/
  curve : ℝ → E
  /-- Absolute continuity on the time interval. -/
  absolutelyContinuous : AbsolutelyContinuousOnInterval curve 0 t
  /-- The prescribed terminal point. -/
  terminal : curve t = x
  /-- Finiteness of the integral action. -/
  actionIntegrable : IntervalIntegrable (fun s ↦ L (deriv curve s)) volume 0 t

/-- The integral action of a path, including its initial cost. -/
def pathCost (L g : E → ℝ) {t : ℝ} {x : E} (γ : AdmissiblePath L t x) : ℝ :=
  g (γ.curve 0) + ∫ s in (0 : ℝ)..t, L (deriv γ.curve s)

/-- The infimum over all absolutely continuous paths of finite action ending
at `x` at time `t`. -/
def variationalValue (L g : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  sInf (Set.range (pathCost L g : AdmissiblePath L t x → ℝ))

private theorem deriv_affine (y q : E) (s : ℝ) :
    deriv (fun r : ℝ ↦ y + r • q) s = q := by
  simpa using (((hasDerivAt_id s).smul_const q).const_add y).deriv

/-- The constant-speed path from `y` to `x` during a positive time `t`. -/
def straightPath (L : E → ℝ) {t : ℝ} {x : E} (ht : 0 < t) (y : E) :
    AdmissiblePath L t x where
  curve := fun s ↦ y + s • (t⁻¹ • (x - y))
  absolutelyContinuous := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
  terminal := by simp [smul_smul, ne_of_gt ht]
  actionIntegrable := by
    simpa only [deriv_affine] using
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ ↦ L (t⁻¹ • (x - y))) volume 0 t)

/-- The straight path is affine with its displacement divided by time. -/
@[simp] theorem straightPath_curve (L : E → ℝ) {t : ℝ} {x : E}
    (ht : 0 < t) (y : E) (s : ℝ) :
    (straightPath L (x := x) ht y).curve s = y + s • (t⁻¹ • (x - y)) := rfl

/-- The straight path starts at the specified footpoint. -/
theorem straightPath_start (L : E → ℝ) {t : ℝ} {x : E}
    (ht : 0 < t) (y : E) :
    (straightPath L (x := x) ht y).curve 0 = y := by simp

/-- The straight path has constant vector velocity. -/
@[simp] theorem deriv_straightPath (L : E → ℝ) {t : ℝ} {x : E}
    (ht : 0 < t) (y : E) (s : ℝ) :
    deriv (straightPath L (x := x) ht y).curve s = t⁻¹ • (x - y) :=
  deriv_affine _ _ _

/-- Integrating the constant velocity gives precisely the footpoint cost
in the Hopf–Lax formula. -/
theorem pathCost_straightPath (L g : E → ℝ) {t : ℝ} {x : E} (ht : 0 < t) (y : E) :
    pathCost L g (straightPath L (x := x) ht y) = g y + t * L (t⁻¹ • (x - y)) := by
  simp [pathCost, smul_eq_mul]

variable [FiniteDimensional ℝ E]

/-- Jensen's inequality bounds the integral action below by the action of
the constant mean velocity. The vector FTC identifies that mean velocity
with displacement divided by time. -/
theorem lagrangian_displacement_le_action {L : E → ℝ} (hconv : ConvexOn ℝ Set.univ L)
    (hcont : Continuous L) {t : ℝ} {x : E} (ht : 0 < t) (γ : AdmissiblePath L t x) :
    t * L (t⁻¹ • (x - γ.curve 0)) ≤ ∫ s in (0 : ℝ)..t, L (deriv γ.curve s) := by
  have hvol : volume.real (Ioc (0 : ℝ) t) = t := by simp [ht.le]
  have hJensen := hconv.map_set_average_le hcont.continuousOn isClosed_univ
    (by simp [ht] : volume (Ioc (0 : ℝ) t) ≠ 0) (by simp) (by simp)
    (by simpa [uIoc_of_le ht.le] using intervalIntegrable_iff.mp
          (intervalIntegrable_deriv_of_absolutelyContinuous γ.absolutelyContinuous))
    (by simpa [uIoc_of_le ht.le, Function.comp_def] using
          intervalIntegrable_iff.mp γ.actionIntegrable)
  rw [setAverage_eq, setAverage_eq, hvol, ← intervalIntegral.integral_of_le ht.le,
    ← intervalIntegral.integral_of_le ht.le,
    integral_deriv_eq_sub_of_absolutelyContinuous γ.absolutelyContinuous, γ.terminal,
    smul_eq_mul, ← div_eq_inv_mul, le_div_iff₀ ht] at hJensen
  linarith

/-- Among all paths with the same two endpoints, the straight path minimizes
integral action. The initial cost cancels. -/
theorem pathCost_straightPath_le {L g : E → ℝ} (hconv : ConvexOn ℝ Set.univ L)
    (hcont : Continuous L) {t : ℝ} {x : E} (ht : 0 < t) (γ : AdmissiblePath L t x) :
    pathCost L g (straightPath L (x := x) ht (γ.curve 0)) ≤ pathCost L g γ := by
  rw [pathCost_straightPath]
  exact add_le_add le_rfl (lagrangian_displacement_le_action hconv hcont ht γ)

/-- The Hopf–Lax infimum bounds the cost of every admissible path below. -/
theorem value_le_pathCost {L g : E → ℝ} (hconv : ConvexOn ℝ Set.univ L) (hcont : Continuous L)
    {t : ℝ} {x : E} (ht : 0 < t) (hbb : BddBelow (Set.range (cost L g t x)))
    (γ : AdmissiblePath L t x) :
    value L g t x ≤ pathCost L g γ :=
  (csInf_le hbb ⟨t⁻¹ • (x - γ.curve 0), rfl⟩).trans (by
    simpa [pathCost_straightPath, cost, smul_smul, ne_of_gt ht] using
      pathCost_straightPath_le (g := g) hconv hcont ht γ)

/-- The Jensen bound transfers a lower bound on velocity costs to path costs. -/
theorem bddBelow_pathCost {L g : E → ℝ} (hconv : ConvexOn ℝ Set.univ L) (hcont : Continuous L)
    {t : ℝ} {x : E} (ht : 0 < t) (hbb : BddBelow (Set.range (cost L g t x))) :
    BddBelow (Set.range (pathCost L g : AdmissiblePath L t x → ℝ)) :=
  ⟨value L g t x, Set.forall_mem_range.2 (value_le_pathCost hconv hcont ht hbb)⟩

/-- Reduction of the full finite-action path problem to the Hopf–Lax
velocity formula. Every velocity is realized by an admissible straight path. -/
theorem value_eq_variationalValue {L g : E → ℝ} (hconv : ConvexOn ℝ Set.univ L)
    (hcont : Continuous L) {t : ℝ} {x : E} (ht : 0 < t)
    (hbb : BddBelow (Set.range (cost L g t x))) :
    value L g t x = variationalValue L g t x := by
  refine le_antisymm (le_csInf ⟨_, straightPath L (x := x) ht x, rfl⟩
    (Set.forall_mem_range.2 (value_le_pathCost hconv hcont ht hbb)))
    (le_csInf (Set.range_nonempty _) (Set.forall_mem_range.2 fun q ↦ ?_))
  have hs := csInf_le (bddBelow_pathCost hconv hcont ht hbb)
    ⟨straightPath L (x := x) ht (x - t • q), rfl⟩
  rw [pathCost_straightPath] at hs
  simpa [variationalValue, cost, smul_smul, ne_of_gt ht] using hs

/-- For a superlinear convex Lagrangian and Lipschitz datum, Hopf–Lax equals
the path infimum without any supplied lower bound or minimizer. -/
theorem value_eq_variationalValue_of_lipschitz {L g : E → ℝ} (hconv : ConvexOn ℝ Set.univ L)
    (hL : Superlinear L) {K : NNReal} (hg : LipschitzWith K g) {t : ℝ} {x : E} (ht : 0 < t) :
    value L g t x = variationalValue L g t x :=
  value_eq_variationalValue hconv (continuousOn_univ.mp (hconv.continuousOn isOpen_univ))
    ht (bddBelow_cost hL hg ht.le x)

/-- Evans's footpoint formula (21) for the infimum over absolutely continuous
paths in arbitrary finite dimension. -/
theorem variationalValue_eq_inf_footpoints {L g : E → ℝ} (hconv : ConvexOn ℝ Set.univ L)
    (hL : Superlinear L) {K : NNReal} (hg : LipschitzWith K g) {t : ℝ} {x : E} (ht : 0 < t) :
    variationalValue L g t x = sInf (Set.range fun y : E ↦ g y + t * L (t⁻¹ • (x - y))) := by
  rw [← value_eq_variationalValue_of_lipschitz hconv hL hg ht,
    value_eq_inf_footpoints L g (ne_of_gt ht)]

/-- Compact attainment in velocity space produces a globally minimizing
straight path among all absolutely continuous paths of finite action. -/
theorem exists_isMinOn_pathCost_straightPath {L g : E → ℝ} (hconv : ConvexOn ℝ Set.univ L)
    (hL : Superlinear L) {K : NNReal} (hg : LipschitzWith K g) {t : ℝ} {x : E} (ht : 0 < t) :
    ∃ y : E, variationalValue L g t x = pathCost L g (straightPath L (x := x) ht y) ∧ IsMinOn
      (pathCost L g : AdmissiblePath L t x → ℝ) Set.univ (straightPath L (x := x) ht y) := by
  have hcont : Continuous L := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  obtain ⟨q, hq, _⟩ := exists_minimizer hcont hL hg ht x
  have hs : pathCost L g (straightPath L (x := x) ht (x - t • q)) = value L g t x := by
    rw [pathCost_straightPath, hq]
    simp [cost, smul_smul, ne_of_gt ht]
  refine ⟨x - t • q, ?_, ?_⟩
  · rw [hs, value_eq_variationalValue_of_lipschitz hconv hL hg ht]
  · intro γ _
    rw [hs]
    exact value_le_pathCost hconv hcont ht (bddBelow_cost hL hg ht.le x) γ

end HamiltonJacobi.HopfLax

end
