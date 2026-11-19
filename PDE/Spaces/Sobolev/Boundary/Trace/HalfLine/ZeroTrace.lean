/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfLine.Core
public import PDE.Analysis.Calculus.LocalExtension
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import PDE.Spaces.Sobolev.GraphSpace.Norms
import CAS.ExactTactic

import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Analysis.Calculus.SmoothTransitionDerivatives

/-!
# Zero trace on the half-line

The zero-trace space `H¹₀(0,∞)` is defined as the closure in `H¹(0,∞)` of the test functions
compactly supported in the open half-line. We show that it coincides with the kernel of
the completed endpoint trace `endpointTrace : H¹(0,∞) → ℝ` built in `HalfLine.Core`. This is
the one-dimensional case of the characterization of `W^{1,p}_0` as the trace-zero subspace of
`W^{1,p}` (Evans, PDE, §5.5, the theorem on trace-zero functions in `W^{1,p}`).

The tool is a family of one-sided cutoffs `boundaryCutoff n`, built from Mathlib's
`Real.smoothTransition`, that vanish for `x ≤ 1/(n+1)` and equal one for `x ≥ 2/(n+1)`.
Multiplying a global test function `φ` with `φ 0 = 0` by these cutoffs gives test functions
supported in `(0,∞)`. They converge to `φ` in `H¹(0,∞)`: the cutoff derivative is of size
`n+1` on a layer of width `1/(n+1)`, and the linear bound `|φ(x)| ≤ C|x|` coming from `φ 0 = 0`
makes the derivative energy of the layer `O(1/n)`.

## Main results

* `boundaryCutoffTestFunction_tendsto_H1`: for a global test function `φ` with `φ 0 = 0`, the
  cut-off test functions converge to the restriction of `φ` in `H¹(0,∞)`.
* `globalTestFunctionToHalfLineH1_mem_H10_of_endpoint_eq_zero`: such a `φ` restricts to an
  element of `H¹₀(0,∞)`.
* `endpointTrace_zero_mem_H10`: a completed `H¹(0,∞)` element with zero endpoint trace lies in
  `H¹₀(0,∞)`. A dense approximating sequence of global test functions is corrected by multiples
  of a fixed bump equal to one at the endpoint, and the previous result applies.
* `endpointTrace_eq_zero_iff_mem_H10`: the kernel of the endpoint trace is exactly `H¹₀(0,∞)`.

## Implementation notes

The half-line is `HalfSpace.upper 1 ⊆ ℝ^1`, so points are `x : ℝ^1` and the coordinate is
`x 0`. The energy estimates are carried out for the real-variable transports of the cutoffs
(`boundaryCutoffReal`), integrating over `Ioi 0`; the two convergence lemmas
`boundaryCutoff_baseEnergy_tendsto_zero` and `boundaryCutoff_derivEnergy_tendsto_zero` treat
the `L²` and derivative parts of the `H¹` norm separately.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 2 and its proof, pp. 273-275, the
  characterization of `W^{1,p}_0(U)` as the kernel of the trace; the cutoffs `1 - ζ(m x_n)` of step
  3 of that proof play the role of `boundaryCutoff n`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (coordinateLine)
open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace
namespace Trace.HalfLine

open MeasureTheory Set
open scoped ENNReal
open PDE.Analysis (standardBump)

/-! ## One-sided smooth boundary cutoffs -/

/-- A smooth cutoff which vanishes to the left of `1/(n+1)` and transitions
to one before `2/(n+1)`.  In particular, its topological support lies strictly
inside the positive half-line. -/
noncomputable def boundaryCutoff (n : ℕ) (x : ℝ^1) : ℝ :=
  Real.smoothTransition (((n + 1 : ℕ) : ℝ) * x 0 - 1)

/-- The one-sided cutoff is `C^∞`: it is `Real.smoothTransition` composed with an affine map of
the single coordinate. -/
theorem boundaryCutoff_contDiff (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (boundaryCutoff n) := by
  unfold boundaryCutoff
  fun_prop

/-- The cutoff is nonnegative. -/
theorem boundaryCutoff_nonneg (n : ℕ) (x : ℝ^1) :
    0 ≤ boundaryCutoff n x :=
  Real.smoothTransition.nonneg _

/-- The cutoff is bounded by one. -/
theorem boundaryCutoff_le_one (n : ℕ) (x : ℝ^1) :
    boundaryCutoff n x ≤ 1 :=
  Real.smoothTransition.le_one _

/-- The cutoff vanishes on the closed left half-line `x 0 ≤ 0`. It actually vanishes on
`x 0 ≤ 1/(n+1)`; this weaker form is what the endpoint arguments use. -/
theorem boundaryCutoff_eq_zero_of_nonpos (n : ℕ) {x : ℝ^1}
    (hx : x 0 ≤ 0) : boundaryCutoff n x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hn : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  nlinarith

/-- The cutoff equals one once `(n+1) · x 0 ≥ 2`, that is, for `x 0 ≥ 2/(n+1)`, because
`Real.smoothTransition` equals one on `[1, ∞)`. -/
theorem boundaryCutoff_eq_one_of_two_le (n : ℕ) {x : ℝ^1}
    (hx : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * x 0) :
    boundaryCutoff n x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

/-- For `t > 0`, eventually `2 < (n+1) t`: the layer `[1/(n+1), 2/(n+1)]` moves left of `t`. -/
private theorem eventually_two_lt_mul {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in Filter.atTop, 2 < ((n + 1 : ℕ) : ℝ) * t := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (2 / t)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hn.trans (Nat.le_add_right n 1)
  linarith [(div_lt_iff₀ ht).1 hN, mul_le_mul_of_nonneg_right hcast ht.le]

/-- At every point of the open half-line the cutoffs converge to one: the transition layer
`[1/(n+1), 2/(n+1)]` eventually lies to the left of any fixed `x 0 > 0`, after which the
sequence is constantly one. -/
theorem boundaryCutoff_tendsto_one {x : ℝ^1}
    (hx : x ∈ (HalfSpace.upper 1)) :
    Filter.Tendsto (fun n : ℕ ↦ boundaryCutoff n x) Filter.atTop (nhds 1) :=
  tendsto_const_nhds.congr' <| (eventually_two_lt_mul (t := x 0) hx).mono fun n hn ↦
    (boundaryCutoff_eq_one_of_two_le n hn.le).symm

/-- Chain rule for the cutoff: its derivative in the single coordinate is `n+1` times the
derivative of `Real.smoothTransition` at the rescaled point `(n+1) · x 0 - 1`. The factor `n+1`
is what the derivative energy estimate has to absorb. -/
theorem boundaryCutoff_partialDeriv (n : ℕ) (x : ℝ^1) :
    (∂[0] (boundaryCutoff n)) x =
      ((n + 1 : ℕ) : ℝ) *
        deriv Real.smoothTransition (((n + 1 : ℕ) : ℝ) * x 0 - 1) := by
  rw [PDE.partialDeriv_eq_deriv_coordinateLine 0 x
    ((boundaryCutoff_contDiff n).differentiable (by simp)).differentiableAt]
  have hinner : HasDerivAt
      (fun s : ℝ ↦ ((n + 1 : ℕ) : ℝ) * s - 1)
      ((n + 1 : ℕ) : ℝ) (x 0) := by
    cas
  have hsmoothAll : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have hsmooth : DifferentiableAt ℝ Real.smoothTransition
      (((n + 1 : ℕ) : ℝ) * x 0 - 1) :=
    (hsmoothAll.differentiable (by simp)).differentiableAt
  have hcomp := hsmooth.hasDerivAt.comp (x 0) hinner
  rw [show (boundaryCutoff n ∘ coordinateLine 0 x) =
      fun s : ℝ ↦ Real.smoothTransition (((n + 1 : ℕ) : ℝ) * s - 1) by
    funext s
    unfold Function.comp boundaryCutoff
    rw [PDE.coordinateLine_apply_same]]
  change deriv (Real.smoothTransition ∘ fun s : ℝ ↦
    (((n + 1 : ℕ) : ℝ) * s - 1)) (x 0) = _
  rw [hcomp.deriv]
  ring

/-- The derivative of `Real.smoothTransition` is supported in `[0,1]`: the function is locally
constant (zero, respectively one) outside that interval. -/
theorem smoothTransition_deriv_support_subset :
    Function.support (deriv Real.smoothTransition) ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  by_contra hxIcc
  change x ∉ Icc (0 : ℝ) 1 at hxIcc
  simp only [Set.mem_Icc, not_and_or, not_le] at hxIcc
  rcases hxIcc with hxneg | hxpos
  · have heq : Real.smoothTransition =ᶠ[nhds x] (fun _ : ℝ ↦ 0) := by
      filter_upwards [Iio_mem_nhds hxneg] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    exact hx (by simpa using heq.deriv_eq)
  · have heq : Real.smoothTransition =ᶠ[nhds x] (fun _ : ℝ ↦ 1) := by
      filter_upwards [Ioi_mem_nhds hxpos] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    exact hx (by simpa using heq.deriv_eq)

/-- The derivative of `Real.smoothTransition` is bounded on `ℝ`, being continuous with compact
support. The bound `D` is the constant in the derivative energy estimate for the shrinking
cutoffs. -/
theorem exists_smoothTransition_deriv_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ D := by
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff
  obtain ⟨D, hD⟩ :=
    (hsmooth.continuous_deriv (by simp)).bounded_above_of_compact_support
      PDE.Analysis.hasCompactSupport_deriv_smoothTransition
  refine ⟨max D 0, le_max_right _ _, fun x ↦ ?_⟩
  have hx := (hD x).trans (le_max_left D 0)
  rw [Real.norm_eq_abs] at hx
  exact hx

/-- A global test function read as a function of the single real coordinate is smooth and
compactly supported. -/
private theorem testFunction_comp_symm (φ : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1))) :
    ContDiff ℝ (⊤ : ℕ∞) (φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) ∧
      HasCompactSupport (φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) :=
  ⟨φ.1.contDiff.comp (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.contDiff,
    φ.1.hasCompactSupport.comp_homeomorph
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.toHomeomorph⟩

/-- A smooth global test function which vanishes at the endpoint grows at
most linearly in the distance to that endpoint. -/
theorem abs_globalTestFunction_le_mul_abs_coord_of_zero
    (φ : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1))) (hφ0 : φ.1.toFun 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ^1, |φ.1.toFun x| ≤ C * |x 0| := by
  obtain ⟨hf, hfc⟩ := testFunction_comp_symm φ
  obtain ⟨C, hC⟩ := (hf.continuous_deriv (by simp)).bounded_above_of_compact_support hfc.deriv
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  have hmv := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun t _ ↦ (hf.differentiable (by simp)) t) (fun t _ ↦ (hC t).trans (le_max_left C 0))
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (x 0))
  have hx : (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm (x 0) = x :=
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm_apply_apply x
  simpa only [Function.comp_apply, hx, map_zero, hφ0, sub_zero, Real.norm_eq_abs] using hmv

/-- The closed support of `boundaryCutoff n` lies in the open half-line `x 0 > 0`. It is in fact
contained in the closed set `{x | 1 ≤ (n+1) · x 0}`, which stays away from the endpoint. This is
what makes the cutoff products test functions on `(0,∞)`. -/
theorem boundaryCutoff_tsupport_subset_positiveHalfLine (n : ℕ) :
    tsupport (boundaryCutoff n) ⊆ (HalfSpace.upper 1) := by
  have hsupport : Function.support (boundaryCutoff n) ⊆ {x | 1 ≤ ((n + 1 : ℕ) : ℝ) * x 0} :=
    fun x hx ↦ show 1 ≤ _ from not_lt.1 fun h ↦ hx (Real.smoothTransition.zero_of_nonpos
      (by linarith))
  refine (closure_minimal hsupport (isClosed_le continuous_const (by fun_prop))).trans
    fun x (hx : 1 ≤ ((n + 1 : ℕ) : ℝ) * x 0) ↦ ?_
  change 0 < x 0
  nlinarith [show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by positivity]

/-- Multiplying a global test function by the one-sided cutoff produces a
test function compactly supported in `(0,∞)`. -/
noncomputable def boundaryCutoffTestFunction (n : ℕ)
    (φ : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1))) :
    GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1) := by
  let g : ℝ^1 → ℝ := fun x ↦ boundaryCutoff n x * φ.1.toFun x
  have hgSmooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    (boundaryCutoff_contDiff n).mul φ.1.contDiff
  have hgCompact : HasCompactSupport g := by
    exact φ.1.hasCompactSupport.mul_left (f := boundaryCutoff n)
  let ψ : 𝓓((⊤ : Opens (ℝ^1)), ℝ) :=
    _root_.TestFunction.mk g hgSmooth hgCompact (Set.subset_univ _)
  refine ⟨ψ, ?_⟩
  change tsupport g ⊆ (HalfSpace.upper 1)
  exact (tsupport_mul_subset_left
    (f := boundaryCutoff n) (g := φ.1.toFun)).trans
    (boundaryCutoff_tsupport_subset_positiveHalfLine n)

/-- Pointwise formula for the cut-off test function. -/
@[simp] theorem boundaryCutoffTestFunction_toFun (n : ℕ)
    (φ : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1))) (x : ℝ^1) :
    (boundaryCutoffTestFunction n φ).1.toFun x =
      boundaryCutoff n x * φ.1.toFun x :=
  rfl

/-- The one-sided boundary cutoff read as a function of the real coordinate. -/
def boundaryCutoffReal (n : ℕ) (t : ℝ) : ℝ :=
  boundaryCutoff n ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)

private theorem boundaryCutoffReal_nonneg (n) (t) : 0 ≤ boundaryCutoffReal n t :=
  boundaryCutoff_nonneg n _
private theorem boundaryCutoffReal_le_one (n) (t) : boundaryCutoffReal n t ≤ 1 :=
  boundaryCutoff_le_one n _
private theorem boundaryCutoffReal_tendsto_one {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun n ↦ boundaryCutoffReal n t) Filter.atTop (nhds 1) :=
  boundaryCutoff_tendsto_one (x := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t) ht
private theorem boundaryCutoffReal_contDiff (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (boundaryCutoffReal n) :=
  (boundaryCutoff_contDiff n).comp (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.contDiff

/-- The zeroth-order `L²(0,∞)` error of the boundary cutoff tends to zero by
dominated convergence. -/
theorem boundaryCutoff_baseEnergy_tendsto_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) :
    Filter.Tendsto
      (fun n ↦ ∫ t in Ioi (0 : ℝ), ((boundaryCutoffReal n t - 1) * f t) ^ 2)
      Filter.atTop (nhds 0) := by
  have hdom (n : ℕ) : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖((boundaryCutoffReal n t - 1) * f t) ^ 2‖ ≤ f t ^ 2 := .of_forall fun t ↦ by
    rw [norm_pow, Real.norm_eq_abs, sq_abs, mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _)
      (by nlinarith [boundaryCutoffReal_nonneg n t, boundaryCutoffReal_le_one n t])
  have hlim : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      Filter.Tendsto (fun n ↦ ((boundaryCutoffReal n t - 1) * f t) ^ 2) Filter.atTop (nhds 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa using (((boundaryCutoffReal_tendsto_one ht).sub_const 1).mul_const (f t)).pow 2
  simpa using tendsto_integral_filter_of_dominated_convergence _
    (.of_forall fun n ↦ ((((boundaryCutoffReal_contDiff n).continuous.sub continuous_const).mul
      hf.continuous).pow 2).aestronglyMeasurable) (.of_forall hdom)
    ((hf.continuous.pow 2).integrable_of_hasCompactSupport
      (by simpa [pow_two] using hfc.mul_left (f := f))).restrict hlim

private theorem boundaryCutoffReal_deriv (n : ℕ) (t : ℝ) :
    deriv (boundaryCutoffReal n) t = ((n + 1 : ℕ) : ℝ) *
      deriv Real.smoothTransition (((n + 1 : ℕ) : ℝ) * t - 1) := by
  have h := PDE.deriv_comp_equivOfUnique_symm
    (boundaryCutoff n) t ((boundaryCutoff_contDiff n).differentiable (by simp)).differentiableAt
  rw [show boundaryCutoffReal n = boundaryCutoff n ∘
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm by rfl]
  rw [h]
  simpa [PiLp.equivOfUnique_symm_apply] using
    boundaryCutoff_partialDeriv n ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)

private theorem boundaryCutoffReal_deriv_eventually_zero {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in Filter.atTop, deriv (boundaryCutoffReal n) t = 0 :=
  (eventually_two_lt_mul ht).mono fun n hn ↦ by
    have hd : deriv Real.smoothTransition (((n + 1 : ℕ) : ℝ) * t - 1) = 0 :=
      Function.notMem_support.1 fun hs ↦ by
        linarith [(smoothTransition_deriv_support_subset hs).2]
    rw [boundaryCutoffReal_deriv, hd, mul_zero]

/-- For endpoint-zero smooth data, the derivative energy of the shrinking
boundary layer tends to zero.  The transition derivative is controlled by the
linear endpoint growth of the data. -/
theorem boundaryCutoff_derivEnergy_tendsto_zero
    (φ : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1))) (hφ0 : φ.1.toFun 0 = 0) :
    let f : ℝ → ℝ := φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
    Filter.Tendsto
      (fun n ↦ ∫ t in Ioi (0 : ℝ),
        (deriv (fun s ↦ (boundaryCutoffReal n s - 1) * f s) t) ^ 2)
      Filter.atTop (nhds 0) := by
  intro f
  obtain ⟨hf, hfc⟩ := testFunction_comp_symm φ
  obtain ⟨C, hC0, hC⟩ := abs_globalTestFunction_le_mul_abs_coord_of_zero φ hφ0
  obtain ⟨D, hD0, hD⟩ := exists_smoothTransition_deriv_bound
  obtain ⟨E, hE⟩ := (hf.continuous_deriv (by simp)).bounded_above_of_compact_support hfc.deriv
  let A : ℕ → ℝ → ℝ := fun n t ↦ deriv (boundaryCutoffReal n) t * f t
  let B : ℕ → ℝ → ℝ := fun n t ↦ A n t + (boundaryCutoffReal n t - 1) * deriv f t
  have hderiv (n : ℕ) (t : ℝ) :
      deriv (fun s ↦ (boundaryCutoffReal n s - 1) * f s) t = B n t :=
    ((((boundaryCutoffReal_contDiff n).differentiable (by simp)) t).hasDerivAt.sub_const 1).mul
      ((hf.differentiable (by simp)) t).hasDerivAt |>.deriv
  -- on the layer, `|A n t| = (n+1) |σ'| |f t| ≤ (n+1) D C t ≤ 2 C D`
  have hA (n : ℕ) {t : ℝ} (ht : 0 < t) : |A n t| ≤ 2 * C * D := by
    have hft : |f t| ≤ C * t := by
      simpa [f, abs_of_pos ht] using hC ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)
    simp only [A, boundaryCutoffReal_deriv, abs_mul, Nat.abs_cast]
    by_cases hd0 : deriv Real.smoothTransition (((n + 1 : ℕ) : ℝ) * t - 1) = 0
    · simp only [hd0, abs_zero, mul_zero, zero_mul]
      positivity
    have hNt : ((n + 1 : ℕ) : ℝ) * t ≤ 2 := by
      linarith [(smoothTransition_deriv_support_subset hd0).2]
    calc _ ≤ ((n + 1 : ℕ) : ℝ) * D * (C * t) := by gcongr; exact hD _
      _ = C * D * (((n + 1 : ℕ) : ℝ) * t) := by ring
      _ ≤ C * D * 2 := by gcongr
      _ = 2 * C * D := by ring
  have hdom (n : ℕ) : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖B n t ^ 2‖ ≤ (tsupport f).indicator (fun _ ↦ (2 * C * D + E) ^ 2) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    by_cases htK : t ∈ tsupport f
    · have h1 : |boundaryCutoffReal n t - 1| ≤ 1 := abs_le.2
        ⟨by linarith [boundaryCutoffReal_nonneg n t], by linarith [boundaryCutoffReal_le_one n t]⟩
      have hB : |B n t| ≤ 2 * C * D + E := (abs_add_le _ _).trans <| add_le_add (hA n ht) <| by
        rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans (hE t)
      rw [indicator_of_mem htK, norm_pow, Real.norm_eq_abs]
      gcongr
    · have hf'0 : deriv f t = 0 := Function.notMem_support.1 fun h ↦ htK (support_deriv_subset h)
      simp [indicator_of_notMem htK, B, A, image_eq_zero_of_notMem_tsupport htK, hf'0]
  have hlim : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      Filter.Tendsto (fun n ↦ B n t ^ 2) Filter.atTop (nhds 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hAt : Filter.Tendsto (fun n ↦ A n t) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.congr' <| (boundaryCutoffReal_deriv_eventually_zero ht).mono
        fun n hn ↦ by simp [A, hn]
    simpa [B] using (hAt.add (((boundaryCutoffReal_tendsto_one ht).sub_const 1).mul_const
      (deriv f t))).pow 2
  have hmeas (n : ℕ) :
      AEStronglyMeasurable (fun t ↦ B n t ^ 2) (volume.restrict (Ioi (0 : ℝ))) :=
    ((((boundaryCutoffReal_contDiff n).continuous_deriv (by simp)).mul hf.continuous).add
      (((boundaryCutoffReal_contDiff n).continuous.sub continuous_const).mul
        (hf.continuous_deriv (by simp)))).pow 2 |>.aestronglyMeasurable
  simp only [hderiv]
  simpa using tendsto_integral_filter_of_dominated_convergence _ (.of_forall hmeas)
    (.of_forall hdom) (((integrableOn_const hfc.isCompact.measure_lt_top.ne).integrable_indicator
      (isClosed_tsupport f).measurableSet).restrict) hlim

/-- The one-sided cutoff test functions converge in the full half-line `H¹`
norm to the restriction of endpoint-zero global smooth data. -/
theorem boundaryCutoffTestFunction_tendsto_H1
    (φ : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1))) (hφ0 : φ.1.toFun 0 = 0) :
    Filter.Tendsto
      (fun n ↦ GraphSpace.testFunctionToH1
        (n := 1) (Ω := (HalfSpace.upper 1))
        (boundaryCutoffTestFunction n φ))
      Filter.atTop (nhds (globalTestFunctionToHalfLineH1Linear φ)) := by
  let ψ : ℕ → GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1)) := fun n ↦
    ⟨(boundaryCutoffTestFunction n φ).1, Set.subset_univ _⟩
  let δ : ℕ → GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1)) := fun n ↦ ψ n - φ
  have hcut (n : ℕ) :
      GraphSpace.testFunctionToH1 (n := 1) (Ω := (HalfSpace.upper 1))
          (boundaryCutoffTestFunction n φ) =
        globalTestFunctionToHalfLineH1Linear (ψ n) := by
    rw [globalTestFunctionToHalfLineH1Linear_eq_mk]
    rfl
  have hdelta (n : ℕ) :
      globalTestFunctionToHalfLineH1Linear (ψ n) - globalTestFunctionToHalfLineH1Linear φ =
        globalTestFunctionToHalfLineH1Linear (δ n) := by
    simp [δ]
  -- `δ n` read on the real line is `(χ_n - 1) f`
  have hfun (n : ℕ) : (δ n).1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm =
      fun s ↦ (boundaryCutoffReal n s - 1) *
        (φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) s := by
    funext s
    change boundaryCutoffReal n s * φ.1.toFun _ - φ.1.toFun _ =
      (boundaryCutoffReal n s - 1) * φ.1.toFun _
    ring
  have hsq : Filter.Tendsto
      (fun n ↦ ‖globalTestFunctionToHalfLineH1Linear (δ n)‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have h := (boundaryCutoff_baseEnergy_tendsto_zero (testFunction_comp_symm φ).1
      (testFunction_comp_symm φ).2).add (boundaryCutoff_derivEnergy_tendsto_zero φ hφ0)
    rw [add_zero] at h
    refine h.congr fun n ↦ ?_
    rw [show ‖globalTestFunctionToHalfLineH1Linear (δ n)‖ ^ 2 =
        ‖((globalTestFunctionToHalfLineH1Linear (δ n) :
            GraphSpace.WkpAmbientOn 1 1 2 (HalfSpace.upper 1))
          (GraphSpace.baseIndex 1 1))‖ ^ 2 +
        ‖((globalTestFunctionToHalfLineH1Linear (δ n) :
            GraphSpace.WkpAmbientOn 1 1 2 (HalfSpace.upper 1))
          (GraphSpace.singleDerivIndex (n := 1) 0))‖ ^ 2 by
      simpa using GraphSpace.ambient_norm_sq_eq_base_sq_add_sum_deriv_sq
        (globalTestFunctionToHalfLineH1Linear (δ n) :
          GraphSpace.WkpAmbientOn 1 1 2 (HalfSpace.upper 1)),
      ← integral_sq_eq_baseCoordinate_norm_sq,
      ← integral_deriv_sq_eq_firstDerivativeCoordinate_norm_sq, hfun n]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [hcut, hdelta, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsq.sqrt

/-- A globally smooth compactly supported function whose endpoint value is
zero restricts to an element of `H¹₀(0,∞)`. -/
theorem globalTestFunctionToHalfLineH1_mem_H10_of_endpoint_eq_zero
    (φ : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1))) (hφ0 : φ.1.toFun 0 = 0) :
    globalTestFunctionToHalfLineH1Linear φ ∈
      (GraphSpace.h10SubmoduleOn
        (n := 1) (Ω := (HalfSpace.upper 1))).toSubmodule := by
  let H10 : Set (H¹(HalfSpace.upper 1)) :=
    (GraphSpace.h10SubmoduleOn
      (n := 1) (Ω := (HalfSpace.upper 1))).toSubmodule
  have hclosed : IsClosed H10 :=
    GraphSpace.instIsClosed_h10SubmoduleOn_toSubmodule
  apply hclosed.mem_of_tendsto (boundaryCutoffTestFunction_tendsto_H1 φ hφ0)
  exact Filter.Eventually.of_forall fun n ↦
    GraphSpace.testFunctionToH1_mem_H10
      (n := 1) (Ω := (HalfSpace.upper 1))
      (boundaryCutoffTestFunction n φ)

/-- The unit endpoint bump as a global test function. -/
noncomputable def endpointUnitTestFunction : GraphSpace.TestFunctionOn 1 (Set.univ : Set (ℝ^1)) :=
  ⟨_root_.TestFunction.mk
    (standardBump 1 : ℝ^1 → ℝ)
    (ContDiffBump.contDiff (standardBump 1))
    (ContDiffBump.hasCompactSupport (standardBump 1))
    (Set.subset_univ _), Set.subset_univ _⟩

/-- The unit endpoint bump takes the value one at the origin. -/
@[simp] theorem endpointUnitTestFunction_zero :
    endpointUnitTestFunction.1.toFun 0 = 1 := by
  change standardBump 1 (0 : ℝ^1) = 1
  apply ContDiffBump.one_of_mem_closedBall
  simp [standardBump]

/-- Every completed half-line `H¹` element with zero endpoint trace belongs to
`H¹₀(0,∞)`.  The proof corrects a dense global smooth approximation by a
fixed unit endpoint bump and applies the one-sided cutoff density theorem. -/
theorem endpointTrace_zero_mem_H10
    (u : H¹(HalfSpace.upper 1))
    (huTrace : endpointTrace u = 0) :
    u ∈ (GraphSpace.h10SubmoduleOn
      (n := 1) (Ω := (HalfSpace.upper 1))).toSubmodule := by
  obtain ⟨v, hvRange, hvlim⟩ :=
    mem_closure_iff_seq_limit.mp (denseRange_globalTestFunctionToHalfLineH1Linear u)
  choose φ hφ using hvRange
  have hφlim : Filter.Tendsto (fun n ↦ globalTestFunctionToHalfLineH1Linear (φ n))
      Filter.atTop (nhds u) := by
    rwa [funext hφ]
  -- correct `φ n` by the endpoint value `c n` times the unit bump; `c n → 0`
  let c : ℕ → ℝ := fun n ↦ endpointTrace (globalTestFunctionToHalfLineH1Linear (φ n))
  have hclim : Filter.Tendsto c Filter.atTop (nhds 0) :=
    huTrace ▸ (endpointTrace.continuous.tendsto u).comp hφlim
  have hψlim : Filter.Tendsto
      (fun n ↦ globalTestFunctionToHalfLineH1Linear (φ n - c n • endpointUnitTestFunction))
      Filter.atTop (nhds u) := by
    simpa using hφlim.sub (hclim.smul_const
      (globalTestFunctionToHalfLineH1Linear endpointUnitTestFunction))
  refine GraphSpace.instIsClosed_h10SubmoduleOn_toSubmodule.mem_of_tendsto hψlim
    (.of_forall fun n ↦ globalTestFunctionToHalfLineH1_mem_H10_of_endpoint_eq_zero _ ?_)
  change (φ n).1.toFun 0 - c n * endpointUnitTestFunction.1.toFun 0 = 0
  rw [endpointUnitTestFunction_zero, mul_one, show c n = (φ n).1.toFun 0 from
    endpointTrace_smooth (φ n), sub_self]

/-- The completed endpoint trace kernel on the positive half-line is exactly
the closure-defined zero-trace Sobolev space `H¹₀(0,∞)`. -/
theorem endpointTrace_eq_zero_iff_mem_H10
    (u : H¹(HalfSpace.upper 1)) :
    endpointTrace u = 0 ↔
      u ∈ (GraphSpace.h10SubmoduleOn
        (n := 1) (Ω := (HalfSpace.upper 1))).toSubmodule :=
  ⟨endpointTrace_zero_mem_H10 u, endpointTrace_eq_zero_of_mem_H10 u⟩

end Trace.HalfLine
end SobolevSpace
