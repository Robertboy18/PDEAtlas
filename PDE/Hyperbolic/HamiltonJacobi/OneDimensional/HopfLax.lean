/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Continuous
import PDE.Analysis.Convex.Differentiable.Supporting
import CAS.ExactTactic

/-!
# Legendre transform and the one-dimensional Hopf–Lax core

The convex-duality and minimization core of the one-dimensional Hopf–Lax
theory of Evans, §3.3.2:

* the Legendre–Fenchel transform `L(q) = sup_p (p * q - H(p))`, as in (13);
* Fenchel support and differentiable biconjugacy, as in Theorem 3;
* the Hopf–Lax infimum `u(t, x) = inf_y (φ(y) + t * L((x - y) / t))`, formula (21);
* coercive lower bounds and existence of minimizing footpoints for Lipschitz data, the attainment
  that Evans leaves as an exercise in the proof of Theorem 4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2, definition (13), Theorems 3 and 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HopfLax1D

noncomputable section

set_option linter.missingDocs true

open scoped BigOperators
open scoped Topology

/-- Legendre–Fenchel transform `L(q) = sup_p (p * q - H(p))`. -/
noncomputable def legendreTransform (H : ℝ → ℝ) (q : ℝ) : ℝ :=
  sSup (Set.range fun p : ℝ ↦ p * q - H p)

/-- Finiteness hypothesis for the Legendre transform:
each `sup_p (p * q - H(p))` is bounded above. -/
def LegendreFinite (H : ℝ → ℝ) : Prop :=
  ∀ q : ℝ, BddAbove (Set.range fun p : ℝ ↦ p * q - H p)

/-- Every affine term in the defining supremum lies below the Legendre transform. -/
theorem le_legendreTransform {H : ℝ → ℝ} {q p : ℝ}
    (hBdd : BddAbove (Set.range fun r : ℝ ↦ r * q - H r)) :
    p * q - H p ≤ legendreTransform H q :=
  le_csSup hBdd ⟨p, rfl⟩

/-- If the Hamiltonian vanishes at zero, then its Legendre transform is
nonnegative. -/
theorem legendreTransform_nonneg {H : ℝ → ℝ} (hFin : LegendreFinite H) (hzero : H 0 = 0) (q : ℝ) :
    0 ≤ legendreTransform H q := by
  simpa [hzero] using le_legendreTransform (p := 0) (hFin q)

/-- A nonnegative Hamiltonian vanishing at zero has zero Legendre cost at
zero displacement. -/
theorem legendreTransform_zero_eq_zero {H : ℝ → ℝ} (hFin : LegendreFinite H)
    (hnonneg : ∀ p, 0 ≤ H p) (hzero : H 0 = 0) :
    legendreTransform H 0 = 0 :=
  le_antisymm (csSup_le (Set.range_nonempty _) (Set.forall_mem_range.2 fun p ↦ by
    simpa using hnonneg p)) (legendreTransform_nonneg hFin hzero 0)

/-- Adding an affine function to a Hamiltonian preserves finiteness of its
Legendre transform. -/
theorem LegendreFinite.add_affine {H : ℝ → ℝ} (hFin : LegendreFinite H) (a b : ℝ) :
    LegendreFinite fun p ↦ H p + a * p + b := by
  intro q
  obtain ⟨B, hB⟩ := hFin (q - a)
  exact ⟨B - b, Set.forall_mem_range.2 fun p ↦ by linarith [hB ⟨p, rfl⟩]⟩

/-- Adding `p ↦ a * p + b` to a Hamiltonian translates its Legendre transform
by `q ↦ q - a` and subtracts `b`. -/
theorem legendreTransform_add_affine {H : ℝ → ℝ} (hFin : LegendreFinite H) (a b q : ℝ) :
    legendreTransform (fun p ↦ H p + a * p + b) q = legendreTransform H (q - a) - b := by
  refine le_antisymm (csSup_le (Set.range_nonempty _) (Set.forall_mem_range.2 fun p ↦ ?_)) ?_
  · linarith [le_legendreTransform (p := p) (hFin (q - a))]
  · have hle : legendreTransform H (q - a) ≤ legendreTransform (fun p ↦ H p + a * p + b) q + b :=
      csSup_le (Set.range_nonempty _) (Set.forall_mem_range.2 fun p ↦ by
        linarith [le_legendreTransform (p := p) (hFin.add_affine a b q)])
    linarith

/-- Finiteness of a Legendre transform implies finiteness of its conjugate.

The Fenchel bound `q * p - H*(q) ≤ H(p)` gives a uniform upper bound for
the second conjugate at each `p`. -/
theorem LegendreFinite.legendreTransform {H : ℝ → ℝ} (hFin : LegendreFinite H) :
    LegendreFinite (HopfLax1D.legendreTransform H) :=
  fun p ↦ ⟨H p, Set.forall_mem_range.2 fun q ↦ by linarith [le_legendreTransform (p := p) (hFin q)]⟩

/-- `legendreTransform` is convex (as a supremum of affine functions), under finiteness. -/
theorem convexOn_legendreTransform {H : ℝ → ℝ} (hFin : LegendreFinite H) :
    ConvexOn ℝ (Set.univ : Set ℝ) (legendreTransform H) := by
  refine ⟨convex_univ, fun q1 _ q2 _ a b ha hb hab ↦
    csSup_le (Set.range_nonempty _) (Set.forall_mem_range.2 fun p ↦ ?_)⟩
  have h1 := mul_le_mul_of_nonneg_left (le_legendreTransform (p := p) (hFin q1)) ha
  have h2 := mul_le_mul_of_nonneg_left (le_legendreTransform (p := p) (hFin q2)) hb
  have hH : (a + b) * H p = H p := by rw [hab, one_mul]
  simp only [smul_eq_mul]
  linarith

/-- A finite real-valued Legendre transform is continuous on the real line. -/
theorem continuous_legendreTransform {H : ℝ → ℝ} (hFin : LegendreFinite H) :
    Continuous (legendreTransform H) :=
  continuousOn_univ.mp ((convexOn_legendreTransform hFin).continuousOn isOpen_univ)

/-- Evaluating the dual supremum at `A` and `-A` gives a coercive absolute-value lower bound. -/
theorem legendreTransform_lower_bound_abs {H : ℝ → ℝ} (hFin : LegendreFinite H) (A q : ℝ) :
    A * |q| - max (H A) (H (-A)) ≤ legendreTransform H q := by
  rcases le_total 0 q with hq | hq
  · rw [abs_of_nonneg hq]
    linarith [le_legendreTransform (p := A) (hFin q), le_max_left (H A) (H (-A))]
  · rw [abs_of_nonpos hq]
    linarith [le_legendreTransform (p := -A) (hFin q), le_max_right (H A) (H (-A))]

/-- For differentiable convex `H`, the supremum defining `H*(H'(p))` is attained at `p`. -/
theorem legendreTransform_eq_of_convex_differentiable {H : ℝ → ℝ} (hFin : LegendreFinite H)
    (hconv : ConvexOn ℝ (Set.univ : Set ℝ) H) {p : ℝ} (hp : DifferentiableAt ℝ H p) :
    legendreTransform H (deriv H p) = p * deriv H p - H p := by
  set q : ℝ := deriv H p
  have hderiv : HasDerivAt H q p := hp.hasDerivAt
  have hsupport (r : ℝ) : H p + q * (r - p) ≤ H r := by
    simpa [ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_comm, le_sub_iff_add_le,
      add_comm] using PDE.Analysis.fderiv_apply_sub_le_sub_of_convex hconv hderiv.hasFDerivAt r
        (Set.mem_univ _) (Set.mem_univ _)
  exact le_antisymm (csSup_le (Set.range_nonempty _) (Set.forall_mem_range.2 fun r ↦ by
    linarith [hsupport r])) (le_legendreTransform (hFin q))

/-- A convex Hamiltonian differentiable at `p` agrees with its Legendre biconjugate there. -/
theorem biconjugate_eq_of_convex_of_differentiableAt {H : ℝ → ℝ} (hFin : LegendreFinite H)
    (hconv : ConvexOn ℝ (Set.univ : Set ℝ) H) {p : ℝ} (hp : DifferentiableAt ℝ H p) :
    legendreTransform (legendreTransform H) p = H p := by
  have hLq := legendreTransform_eq_of_convex_differentiable hFin hconv hp
  refine le_antisymm (csSup_le (Set.range_nonempty _) (Set.forall_mem_range.2 fun r ↦ ?_)) ?_
  · linarith [le_legendreTransform (p := p) (hFin r)]
  · linarith [le_legendreTransform (p := deriv H p) (hFin.legendreTransform p)]

/-- A differentiable convex Hamiltonian agrees pointwise with its Legendre biconjugate. -/
theorem biconjugate_eq_of_convex_of_differentiable {H : ℝ → ℝ} (hFin : LegendreFinite H)
    (hconv : ConvexOn ℝ (Set.univ : Set ℝ) H) (hH : Differentiable ℝ H) :
    ∀ p : ℝ, legendreTransform (legendreTransform H) p = H p :=
  fun p ↦ biconjugate_eq_of_convex_of_differentiableAt hFin hconv (hH p)

/-- Convexity of the Legendre transform bounds a one-step cost by any two-step path cost. -/
theorem legendreTransform_time_split_le {H : ℝ → ℝ} (hFin : LegendreFinite H) {t s : ℝ}
    (ht : 0 < t) (hs : 0 < s) (x y z : ℝ) :
    (t + s) * legendreTransform H ((x - y) / (t + s)) ≤
        s * legendreTransform H ((z - y) / s) + t * legendreTransform H ((x - z) / t) := by
  have hts := add_pos ht hs
  have hL := (convexOn_legendreTransform hFin).2 (Set.mem_univ ((z - y) / s))
    (Set.mem_univ ((x - z) / t)) (div_nonneg hs.le hts.le) (div_nonneg ht.le hts.le)
    (by field_simp; ring)
  simp only [smul_eq_mul] at hL
  rw [show s / (t + s) * ((z - y) / s) + t / (t + s) * ((x - z) / t) = (x - y) / (t + s) by
    field_simp; ring] at hL
  calc _ ≤ (t + s) * (s / (t + s) * legendreTransform H ((z - y) / s) +
        t / (t + s) * legendreTransform H ((x - z) / t)) := by gcongr
    _ = _ := by field_simp

/-- Hopf–Lax integrand: `φ(y) + t * L((x-y)/t)`.

Analytically this expression is used for `t > 0`; at `t = 0` the quotient is Lean's totalized
division and should not be interpreted as the variational Hopf–Lax slope. -/
noncomputable def hopfLaxIntegrand (H φ : ℝ → ℝ) (t x y : ℝ) : ℝ :=
  φ y + t * legendreTransform H ((x - y) / t)

/-- Hopf–Lax formula as an infimum over the totalized integrand.

The analytic Hopf–Lax formula is the `t > 0` regime. The
`hopfLaxEvolution` definition separately inserts the initial condition at
`t = 0`. -/
noncomputable def hopfLax (H φ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  sInf (Set.range fun y : ℝ ↦ hopfLaxIntegrand H φ t x y)

/-- A mild well-definedness condition: the range of Hopf–Lax integrands is bounded below. -/
def HopfLaxBddBelow (H φ : ℝ → ℝ) (t x : ℝ) : Prop :=
  BddBelow (Set.range fun y : ℝ ↦ hopfLaxIntegrand H φ t x y)

/-- Lipschitz initial data and Legendre finiteness give a coercive lower bound for the integrand. -/
theorem hopfLaxIntegrand_lower_bound_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t x y : ℝ} (ht : 0 < t) :
    φ x + dist x y - t * max (H ((K : ℝ) + 1)) (H (-((K : ℝ) + 1))) ≤
      hopfLaxIntegrand H φ t x y := by
  have hφlower : φ x - K * dist x y ≤ φ y := by
    linarith [le_abs_self (φ x - φ y), hφ.dist_le_mul x y, Real.dist_eq (φ x) (φ y)]
  have hL := mul_le_mul_of_nonneg_left
    (legendreTransform_lower_bound_abs hFin ((K : ℝ) + 1) ((x - y) / t)) ht.le
  have habs : t * (((K : ℝ) + 1) * |(x - y) / t|) = ((K : ℝ) + 1) * dist x y := by
    rw [Real.dist_eq, abs_div, abs_of_pos ht]
    cas
  unfold hopfLaxIntegrand
  linarith

/-- For positive time and Lipschitz initial data, every Hopf–Lax infimum is bounded below. -/
theorem hopfLaxBddBelow_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    HopfLaxBddBelow H φ t x :=
  ⟨φ x - t * max (H ((K : ℝ) + 1)) (H (-((K : ℝ) + 1))), Set.forall_mem_range.2 fun y ↦ by
    linarith [hopfLaxIntegrand_lower_bound_of_lipschitz (x := x) (y := y) hFin hφ ht,
      dist_nonneg (x := x) (y := y)]⟩

/-- The Hopf–Lax infimum for Lipschitz data at positive time is attained by a global minimizer. -/
theorem exists_isMinOn_hopfLaxIntegrand_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    ∃ y0 : ℝ, IsMinOn (hopfLaxIntegrand H φ t x) Set.univ y0 ∧
      hopfLax H φ t x = hopfLaxIntegrand H φ t x y0 := by
  let C : ℝ := max (H ((K : ℝ) + 1)) (H (-((K : ℝ) + 1)))
  let R : ℝ := max 0 (t * C + t * legendreTransform H 0 + 1)
  let f : ℝ → ℝ := hopfLaxIntegrand H φ t x
  have hfcont : Continuous f := hφ.continuous.add (continuous_const.mul
    ((continuous_legendreTransform hFin).comp ((continuous_const.sub continuous_id).div_const t)))
  have hxR : x ∈ Metric.closedBall x R := Metric.mem_closedBall_self (le_max_left _ _)
  obtain ⟨y0, -, hy0min⟩ := (isCompact_closedBall x R).exists_isMinOn ⟨x, hxR⟩ hfcont.continuousOn
  have hmin (y : ℝ) : f y0 ≤ f y := by
    by_cases hy : y ∈ Metric.closedBall x R
    · exact hy0min hy
    have hy' : R < dist x y := by simpa [Metric.mem_closedBall, dist_comm] using hy
    have hlow : φ x + dist x y - t * C ≤ f y := hopfLaxIntegrand_lower_bound_of_lipschitz hFin hφ ht
    have hx : f x = φ x + t * legendreTransform H 0 := by simp [f, hopfLaxIntegrand]
    have hR : t * C + t * legendreTransform H 0 + 1 ≤ R := le_max_right _ _
    have hx0 : f y0 ≤ f x := hy0min hxR
    linarith
  exact ⟨y0, fun y _ ↦ hmin y, le_antisymm (csInf_le ⟨f y0, Set.forall_mem_range.2 hmin⟩
    ⟨y0, rfl⟩) (le_csInf (Set.range_nonempty f) (Set.forall_mem_range.2 hmin))⟩

/-- The Hopf–Lax value for Lipschitz data equals its integrand at some spatial footpoint. -/
theorem exists_hopfLax_eq_integrand_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    ∃ y0 : ℝ, hopfLax H φ t x = hopfLaxIntegrand H φ t x y0 :=
  (exists_isMinOn_hopfLaxIntegrand_of_lipschitz hFin hφ ht).imp fun _ h ↦ h.2

/-- Basic bound: `hopfLax` is below any integrand value (requires bounded-below). -/
theorem hopfLax_le_integrand {H φ : ℝ → ℝ} {t x y : ℝ} (hbb : HopfLaxBddBelow H φ t x) :
    hopfLax H φ t x ≤ hopfLaxIntegrand H φ t x y :=
  csInf_le hbb ⟨y, rfl⟩

end

end HopfLax1D
