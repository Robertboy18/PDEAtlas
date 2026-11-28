/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import PDE.Analysis.Evolution.Semigroup.Complex.EssentialGrowth

/-!
# The group on a spectral subspace and the unstable decomposition

Let `P` be the Riesz projection of the generator `A` of a complex-linear semigroup on a circle
around an isolated point `μ` of the spectrum, of finite rank. On the range of `P` the semigroup
is the group `G(τ) = e^{μτ} exp(τ N) P`, where `N = (A - μ) P` is nilpotent there. So it grows
and decays like `e^{Re μ τ}` up to a factor `e^{δ|τ|}`, for every `δ > 0`, forward and backward
in time. Together with the spectral gap above the essential growth bound
(`IsComplexLinear.exists_spectral_gap`) this gives the unstable decomposition of a semigroup
with negative essential growth bound: finitely many unstable eigenvalues with projections of
finite rank, and growth at most `e^{δt}` on the rest. It also gives
`ω₀(T) = max (ω_ess(T), s(A))`. When the semigroup is the complexification of a real one, the
splitting of real data into real and imaginary parts is not treated here.

## Main results

* `NormedSpace.exp_smul_mul_eq_sum` and `NormedSpace.exists_norm_exp_smul_mul_le`: in a real
  Banach algebra, if `a^k p = 0`, then `exp(τ a) p = Σ_{j<k} τ^j/j! a^j p`, so
  `‖exp(τ a) p‖ ≤ C e^{δ|τ|}` for every `δ > 0`.
* `LinearPMap.rieszNilpotent` and `LinearPMap.rieszGroup`: `N` and `G` for any operator and any
  circle. `rieszGroup_add` is the group law, and `rieszNilpotent_pow_mul_eq_zero` gives
  `N^k P = 0` for an isolated point, with `k` the rank of `P`.
* `LinearPMap.exists_norm_rieszGroup_le` and `exists_le_norm_rieszGroup_apply`:
  `‖G(τ)‖ ≤ C e^{Re μ τ + δ|τ|}`, and `e^{Re μ τ - δ|τ|} ‖f‖ ≤ C ‖G(τ) f‖` on the range of `P`.
* `IsComplexLinear.apply_eq_exp_smul_apply`: an orbit along which the generator acts as a
  bounded operator `W` is `exp(t W) x`.
* `IsComplexLinear.clm_mul_rieszProjection`: `T(t) P = G(t)` for `t ≥ 0`, and
  `exists_norm_clm_mul_rieszProjection_le`: `‖T(t) P‖ ≤ C e^{(Re μ + δ) t}`.
* `IsComplexLinear.exists_unstable_decomposition` and `exists_unstable_decomposition_bounds`: if
  `ω_ess(T) < 0`, the spectrum in `Re z > 0` is a finite set `Λ` of eigenvalues whose Riesz
  projections `P_μ` have finite rank, `T(t) P_μ = G_μ(t)` with the two-sided bounds above, and
  `‖T(t) (1 - Σ_μ P_μ)‖ ≤ C e^{δt}` for every `δ > 0`.
* `IsComplexLinear.exists_norm_le_exp_of_spectrum_re_lt`, `growthBound_lt_iff_spectrum` and
  `growthBound_eq_max`: `ω₀(T) = max (ω_ess(T), s(A))`.

## How it works

The range of `P` is `ker (A - μ)^k` (`LinearPMap.range_rieszProjection_resolvent_eq_genEigenspace`)
and `N` lowers the order of a generalized eigenvector, so `N^k P = 0`. Then `exp(τ N) P` is a
polynomial in `τ`; this is the Jordan block computation, and it gives the upper bound. The lower
bound follows from `f = G(-τ) G(τ) f`. On the range of `P` the generator of the rescaled
semigroup `e^{-μt} T(t)` is the bounded operator `N`, and uniqueness for the linear equation
`u' = N u` (`ODE_solution_unique`) gives `T(t) P = G(t)`. For the decomposition,
`exists_spectral_gap` at `ω = 0` gives finitely many spectral points with `Re z > ω'` for some
`ω' < 0`, and decay like `e^{ω't}` off their projections. The points with `Re μ ≤ 0` move to the
stable part, where each grows at most like `e^{(Re μ + δ) t} ≤ e^{δt}`; this is why the bound
holds for every `δ > 0` and not for `δ = 0`. The same splitting at a real `ω` above `ω_ess` and
above the real part of the spectrum gives `‖T(t)‖ ≤ M e^{ω''t}` with `ω'' < ω`, hence
`ω₀ = max (ω_ess, s(A))`. The group `rieszGroup` plays the role of the real library's
`StronglyContinuousSemigroup.unstableGroup`, one eigenvalue at a time.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Graduate Texts in Mathematics 194, Springer, 2000, Chapter IV, Section 2 (the growth bound as
  the maximum of the essential growth bound and the spectral bound).
  <https://doi.org/10.1007/b97696>
* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 2.2, the paragraph
  "Decomposition via Riesz projection": the splitting into stable and unstable subspaces and
  the bounds (2.14). <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open Filter Topology Set Metric PDE.Analysis.Spectral
open scoped Nat

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **The exponential of a nilpotent element is a polynomial.** If `a^k p = 0`, then
`exp(τ a) p = Σ_{j<k} τ^j/j! a^j p`. -/
theorem exp_smul_mul_eq_sum {a p : 𝔸} {k : ℕ} (h : a ^ k * p = 0) (τ : ℝ) :
    exp (τ • a) * p = ∑ j ∈ Finset.range k, ((j ! : ℝ)⁻¹ * τ ^ j) • (a ^ j * p) := by
  have h1 := congrFun (exp_eq_tsum ℝ (𝔸 := 𝔸)) (τ • a)
  have hsum := expSeries_summable' (𝕂 := ℝ) (τ • a)
  rw [h1, ← hsum.tsum_mul_right p, tsum_eq_sum (s := Finset.range k)]
  · exact Finset.sum_congr rfl fun j _ ↦ by rw [smul_pow, smul_smul, smul_mul_assoc]
  · intro n hn
    have hkn : k ≤ n := not_lt.mp fun hlt ↦ hn (Finset.mem_range.mpr hlt)
    have hzero : a ^ n * p = 0 := by
      rw [← Nat.sub_add_cancel hkn, pow_add, mul_assoc, h, mul_zero]
    rw [smul_pow, smul_smul, smul_mul_assoc, hzero, smul_zero]

/-- **The Jordan block bound.** If `a^k p = 0`, then `‖exp(τ a) p‖ ≤ C e^{δ|τ|}` for every
`δ > 0`: a polynomial grows more slowly than any exponential. -/
theorem exists_norm_exp_smul_mul_le {a p : 𝔸} {k : ℕ} (h : a ^ k * p = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ τ : ℝ, ‖exp (τ • a) * p‖ ≤ C * Real.exp (δ * |τ|) := by
  refine ⟨∑ j ∈ Finset.range k, ‖a ^ j * p‖ / δ ^ j, fun τ ↦ ?_⟩
  rw [exp_smul_mul_eq_sum h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  have h1 := Real.pow_div_factorial_le_exp _ (mul_nonneg hδ.le (abs_nonneg τ)) j
  have h2 : ‖((j ! : ℝ)⁻¹ * τ ^ j) • (a ^ j * p)‖ =
      ‖a ^ j * p‖ / δ ^ j * ((δ * |τ|) ^ j / j !) := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast, abs_pow, mul_pow]
    field_simp
  rw [h2]
  gcongr

end NormedSpace

/-- Rational scalars on bounded complex operators, as the exponential series needs them. -/
local instance normedAlgebraRatComplexEnd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    NormedAlgebra ℚ (E →L[ℂ] E) :=
  NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)

namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (A : E →ₗ.[ℂ] E) {μ : ℂ} {r : ℝ}

/-- The operator `N = (A - μ) P` for the Riesz projection `P` of `A` on the circle `C(μ, r)`:
the bounded operator `(2πi)⁻¹ ∮ (z - μ) (z - A)⁻¹ dz`. For an isolated point `μ` with a
projection of finite rank it is nilpotent. -/
def rieszNilpotent (μ : ℂ) (r : ℝ) : E →L[ℂ] E :=
  dunfordIntegral A.resolvent μ r (fun z ↦ z) - μ • rieszProjection A.resolvent μ r

/-- The group `G(τ) = e^{μτ} exp(τ N) P` on the range of the Riesz projection `P` of `A` on
the circle `C(μ, r)`, for every real `τ`. For the generator of a semigroup it is `T(τ) P` at
`τ ≥ 0`. -/
def rieszGroup (μ : ℂ) (r : ℝ) (τ : ℝ) : E →L[ℂ] E :=
  Complex.exp (μ * τ) •
    (NormedSpace.exp (τ • A.rieszNilpotent μ r) * rieszProjection A.resolvent μ r)

variable {A}

/-- The Riesz projection commutes with `N = (A - μ) P`. -/
theorem commute_rieszProjection_rieszNilpotent (hr : 0 ≤ r) (hs : sphere μ r ⊆ A.resolventSet) :
    Commute (rieszProjection A.resolvent μ r) (A.rieszNilpotent μ r) :=
  (commute_dunfordIntegral_resolvent hr hs
    (fun _ _ h ↦ rieszProjection_resolvent_map_mem_graph hr hs h) _).sub_right
      ((Commute.refl _).smul_right μ)

/-- On the range of the Riesz projection, `A = μ + N`. -/
theorem mem_graph_rieszNilpotent (hr : 0 ≤ r) (hs : sphere μ r ⊆ A.resolventSet) {v : E}
    (hv : rieszProjection A.resolvent μ r v = v) :
    (v, A.rieszNilpotent μ r v + μ • v) ∈ A.graph := by
  have h := rieszProjection_resolvent_mem_graph hr hs v
  have e : A.rieszNilpotent μ r v + μ • v = dunfordIntegral A.resolvent μ r (fun z ↦ z) v := by
    rw [rieszNilpotent, _root_.sub_apply, _root_.smul_apply, hv, sub_add_cancel]
  rwa [hv, ← e] at h

omit [CompleteSpace E] in
/-- At `τ = 0` the group is the Riesz projection. -/
@[simp]
theorem rieszGroup_zero (A : E →ₗ.[ℂ] E) (μ : ℂ) (r : ℝ) :
    A.rieszGroup μ r 0 = rieszProjection A.resolvent μ r := by
  simp [rieszGroup, NormedSpace.exp_zero]

/-- **The group law** `G(τ + σ) = G(τ) G(σ)`. -/
theorem rieszGroup_add (hr : 0 < r) (hs : sphere μ r ⊆ A.resolventSet) (τ σ : ℝ) :
    A.rieszGroup μ r (τ + σ) = A.rieszGroup μ r τ * A.rieszGroup μ r σ := by
  have hP := isIdempotentElem_rieszProjection_resolvent hr hs
  have hc := commute_rieszProjection_rieszNilpotent hr.le hs
  have hc' : rieszProjection A.resolvent μ r * NormedSpace.exp (σ • A.rieszNilpotent μ r) =
      NormedSpace.exp (σ • A.rieszNilpotent μ r) * rieszProjection A.resolvent μ r :=
    ((hc.smul_right σ).exp_right).eq
  have hexp : NormedSpace.exp ((τ + σ) • A.rieszNilpotent μ r) =
      NormedSpace.exp (τ • A.rieszNilpotent μ r) * NormedSpace.exp (σ • A.rieszNilpotent μ r) := by
    rw [add_smul]
    exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left τ).smul_right σ)
  have key : NormedSpace.exp (τ • A.rieszNilpotent μ r) * rieszProjection A.resolvent μ r *
      (NormedSpace.exp (σ • A.rieszNilpotent μ r) * rieszProjection A.resolvent μ r) =
      NormedSpace.exp (τ • A.rieszNilpotent μ r) * NormedSpace.exp (σ • A.rieszNilpotent μ r) *
        rieszProjection A.resolvent μ r := by
    calc _ = NormedSpace.exp (τ • A.rieszNilpotent μ r) *
          (rieszProjection A.resolvent μ r * NormedSpace.exp (σ • A.rieszNilpotent μ r)) *
            rieszProjection A.resolvent μ r := by simp only [mul_assoc]
      _ = NormedSpace.exp (τ • A.rieszNilpotent μ r) *
          (NormedSpace.exp (σ • A.rieszNilpotent μ r) * rieszProjection A.resolvent μ r) *
            rieszProjection A.resolvent μ r := by rw [hc']
      _ = _ := by rw [mul_assoc, mul_assoc, hP.eq, ← mul_assoc]
  simp only [rieszGroup]
  rw [smul_mul_smul_comm, key, ← hexp, ← Complex.exp_add, ← mul_add, ← Complex.ofReal_add]

/-- **`N` is nilpotent on the range of a Riesz projection of finite rank**: `N^k P = 0` with
`k` the rank of `P`, for an isolated point of the spectrum. The range of `P` is
`ker (A - μ)^k`, and `N` lowers the order of a generalized eigenvector. -/
theorem rieszNilpotent_pow_mul_eq_zero (hr : 0 < r)
    (hiso : closedBall μ r \ {μ} ⊆ A.resolventSet)
    [FiniteDimensional ℂ (LinearMap.range (rieszProjection A.resolvent μ r).toLinearMap)] :
    A.rieszNilpotent μ r ^
        Module.finrank ℂ (LinearMap.range (rieszProjection A.resolvent μ r).toLinearMap) *
      rieszProjection A.resolvent μ r = 0 := by
  have hs : sphere μ r ⊆ A.resolventSet := sphere_subset_of_closedBall_sdiff_subset hr hiso
  have hP := isIdempotentElem_rieszProjection_resolvent hr hs
  have hc := commute_rieszProjection_rieszNilpotent hr.le hs
  have hrange := range_rieszProjection_resolvent_eq_genEigenspace hr hiso
  have key : ∀ (j : ℕ) (v : E), v ∈ A.genEigenspace μ j →
      rieszProjection A.resolvent μ r v = v → (A.rieszNilpotent μ r ^ j) v = 0 := by
    intro j
    induction j with
    | zero =>
      intro v hv _
      rw [(Submodule.mem_bot ℂ).mp hv, _root_.map_zero]
    | succ j ih =>
      intro v hv hPv
      obtain ⟨y, hvy, hu⟩ := mem_genEigenspace_succ.mp hv
      have hy : y = A.rieszNilpotent μ r v + μ • v :=
        A.mem_graph_snd_inj hvy (mem_graph_rieszNilpotent hr.le hs hPv) rfl
      rw [hy, add_sub_cancel_right] at hu
      have hPN : rieszProjection A.resolvent μ r (A.rieszNilpotent μ r v) =
          A.rieszNilpotent μ r v := by
        rw [← mul_apply_eq_comp, hc.eq, mul_apply_eq_comp, hPv]
      rw [pow_succ, mul_apply_eq_comp]
      exact ih _ hu hPN
  refine ContinuousLinearMap.ext fun y ↦ ?_
  rw [mul_apply_eq_comp, _root_.zero_apply]
  refine key _ _ ?_ (DFunLike.congr_fun hP.eq y)
  rw [← hrange]
  exact ⟨y, rfl⟩

/-- **The growth of the group.** For an isolated point `μ` of the spectrum with a Riesz
projection of finite rank and every `δ > 0`, `‖G(τ)‖ ≤ C e^{Re μ τ + δ|τ|}` for all real `τ`.
This is the growth of the semigroup on one spectral subspace, forward and backward in time.
The factor `e^{μτ}` has modulus `e^{Re μ τ}`, and `exp(τ N) P` is a polynomial in `τ` because
`N^k P = 0` (`NormedSpace.exists_norm_exp_smul_mul_le`). -/
theorem exists_norm_rieszGroup_le (hr : 0 < r) (hiso : closedBall μ r \ {μ} ⊆ A.resolventSet)
    [FiniteDimensional ℂ (LinearMap.range (rieszProjection A.resolvent μ r).toLinearMap)]
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ τ : ℝ, ‖A.rieszGroup μ r τ‖ ≤ C * Real.exp (μ.re * τ + δ * |τ|) := by
  obtain ⟨C, hC⟩ :=
    NormedSpace.exists_norm_exp_smul_mul_le (rieszNilpotent_pow_mul_eq_zero hr hiso) hδ
  refine ⟨C, fun τ ↦ ?_⟩
  rw [rieszGroup, norm_smul, Complex.norm_exp, show (μ * (τ : ℂ)).re = μ.re * τ by simp,
    Real.exp_add, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hC τ) (Real.exp_nonneg _)

/-- **The decay of the group is at most exponential.** For an isolated point `μ` of the
spectrum with a Riesz projection `P` of finite rank and every `δ > 0`,
`e^{Re μ τ - δ|τ|} ‖f‖ ≤ C ‖G(τ) f‖` for all real `τ` and all `f` in the range of `P`. So a mode
in the range of `P` cannot decay faster than its eigenvalue allows, forward or backward in
time. The proof applies the upper bound at `-τ` to `f = G(-τ) G(τ) f`. -/
theorem exists_le_norm_rieszGroup_apply (hr : 0 < r)
    (hiso : closedBall μ r \ {μ} ⊆ A.resolventSet)
    [FiniteDimensional ℂ (LinearMap.range (rieszProjection A.resolvent μ r).toLinearMap)]
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ) (f : E), rieszProjection A.resolvent μ r f = f →
      Real.exp (μ.re * τ - δ * |τ|) * ‖f‖ ≤ C * ‖A.rieszGroup μ r τ f‖ := by
  have hs : sphere μ r ⊆ A.resolventSet := sphere_subset_of_closedBall_sdiff_subset hr hiso
  obtain ⟨C, hC⟩ := exists_norm_rieszGroup_le hr hiso hδ
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun τ f hf ↦ ?_⟩
  have h1 : A.rieszGroup μ r (-τ) (A.rieszGroup μ r τ f) = f := by
    rw [← mul_apply_eq_comp, ← rieszGroup_add hr hs, neg_add_cancel, rieszGroup_zero, hf]
  have h2 : ‖f‖ ≤ max C 1 * Real.exp (μ.re * -τ + δ * |τ|) * ‖A.rieszGroup μ r τ f‖ := by
    have h3 := hC (-τ)
    rw [abs_neg] at h3
    calc ‖f‖ = ‖A.rieszGroup μ r (-τ) (A.rieszGroup μ r τ f)‖ := by rw [h1]
      _ ≤ ‖A.rieszGroup μ r (-τ)‖ * ‖A.rieszGroup μ r τ f‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ max C 1 * Real.exp (μ.re * -τ + δ * |τ|) * ‖A.rieszGroup μ r τ f‖ := by
          gcongr
          exact h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
  have he : Real.exp (μ.re * τ - δ * |τ|) * Real.exp (μ.re * -τ + δ * |τ|) = 1 := by
    rw [← Real.exp_add, show μ.re * τ - δ * |τ| + (μ.re * -τ + δ * |τ|) = 0 by ring,
      Real.exp_zero]
  calc Real.exp (μ.re * τ - δ * |τ|) * ‖f‖
      ≤ Real.exp (μ.re * τ - δ * |τ|) *
        (max C 1 * Real.exp (μ.re * -τ + δ * |τ|) * ‖A.rieszGroup μ r τ f‖) := by gcongr
    _ = Real.exp (μ.re * τ - δ * |τ|) * Real.exp (μ.re * -τ + δ * |τ|) *
        (max C 1 * ‖A.rieszGroup μ r τ f‖) := by ring
    _ = max C 1 * ‖A.rieszGroup μ r τ f‖ := by rw [he, one_mul]

end LinearPMap

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsComplexLinear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {T : StronglyContinuousSemigroup X} (hT : T.IsComplexLinear) {μ : ℂ} {r : ℝ}

include hT

/-- **Orbits on which the generator is bounded are exponentials.** If the generator acts as the
bounded operator `W` along the orbit of `x`, then `T(t) x = exp(t W) x`: both sides solve
`u' = W u` with the same initial value. -/
theorem apply_eq_exp_smul_apply {W : X →L[ℂ] X} {x : X}
    (hW : ∀ t : NNReal, (T t x, W (T t x)) ∈ hT.generator.graph) (t : NNReal) :
    T t x = NormedSpace.exp ((t : ℝ) • W) x := by
  have hx0 : (x, W x) ∈ hT.generator.graph := by
    have h := hW 0
    rwa [T.map_zero_apply] at h
  have h := ODE_solution_unique (K := ‖W‖₊) (v := fun _ y ↦ W y) (f := T.realOrbit x)
    (g := fun s : ℝ ↦ NormedSpace.exp (s • W) x) (a := 0) (b := t)
    (fun _ ↦ W.lipschitzWith) (T.continuous_realOrbit x).continuousOn ?_ ?_ ?_ ?_
  · simpa using h ⟨t.coe_nonneg, le_rfl⟩
  · intro s hs
    have h1 := (hT.mem_graph_generator_iff.mp hx0).hasDerivWithinAt_realOrbit s.toNNReal
    rw [Real.coe_toNNReal s hs.1] at h1
    have h2 : T s.toNNReal (W x) = W (T.realOrbit x s) :=
      hT.generator.mem_graph_snd_inj (hT.map_mem_graph s.toNNReal hx0) (hW s.toNNReal) rfl
    rwa [h2] at h1
  · exact ((ContinuousLinearMap.apply ℂ X x).continuous.comp
      (NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const))).continuousOn
  · intro s _
    exact (((ContinuousLinearMap.apply ℂ X x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_exp_smul_const' W s)).hasDerivWithinAt
  · simp [realOrbit, NormedSpace.exp_zero]

/-- **On the range of a Riesz projection the semigroup is the group** `G(t) = e^{μt} exp(t N) P`:
`T(t) P = G(t)` for `t ≥ 0`. So the bounds of the group are bounds for the semigroup, and `G`
extends the semigroup on the range of `P` to negative times. On that range
the generator of the rescaled semigroup `e^{-μt} T(t)` is the bounded operator `N`, so its
orbits are `exp(t N) x` (`apply_eq_exp_smul_apply`). -/
theorem clm_mul_rieszProjection (hr : 0 < r) (hs : sphere μ r ⊆ hT.generator.resolventSet)
    (t : NNReal) :
    hT.clm t * rieszProjection hT.generator.resolvent μ r = hT.generator.rieszGroup μ r t := by
  have hP := LinearPMap.isIdempotentElem_rieszProjection_resolvent hr hs
  have hPT : ∀ s : NNReal, Commute (hT.clm s) (rieszProjection hT.generator.resolvent μ r) :=
    fun s ↦ LinearPMap.commute_rieszProjection_resolvent hr.le hs
      fun _ _ h ↦ hT.map_mem_graph s h
  refine ContinuousLinearMap.ext fun y ↦ ?_
  obtain ⟨x, hx⟩ : ∃ x, x = rieszProjection hT.generator.resolvent μ r y := ⟨_, rfl⟩
  have hPx : rieszProjection hT.generator.resolvent μ r x = x := by
    rw [hx]
    exact DFunLike.congr_fun hP.eq y
  have hS := hT.isComplexLinear_rescale (-μ)
  -- along the orbit of `x` the generator of `e^{-μt} T(t)` is `N`
  have hW : ∀ s : NNReal, (hT.rescale (-μ) s x,
      hT.generator.rieszNilpotent μ r (hT.rescale (-μ) s x)) ∈ hS.generator.graph := by
    intro s
    have hfix : rieszProjection hT.generator.resolvent μ r (hT.rescale (-μ) s x) =
        hT.rescale (-μ) s x := by
      rw [rescale_apply, _root_.smul_apply, _root_.map_smul]
      congr 1
      exact (DFunLike.congr_fun (hPT s).eq x).symm.trans (congrArg (T s) hPx)
    have h := LinearPMap.mem_graph_rieszNilpotent hr.le hs hfix
    rw [mem_graph_generator_iff, hasGeneratorAt_rescale_iff, ← mem_graph_generator_iff hT,
      neg_smul, sub_neg_eq_add]
    exact h
  have h := hS.apply_eq_exp_smul_apply hW t
  rw [rescale_apply, _root_.smul_apply] at h
  rw [mul_apply_eq_comp, ← hx, LinearPMap.rieszGroup, _root_.smul_apply, mul_apply_eq_comp, ← hx,
    ← h, smul_smul, ← Complex.exp_add,
    show μ * ((t : ℝ) : ℂ) + -μ * ((t : ℝ) : ℂ) = 0 by ring, Complex.exp_zero, one_smul]
  rfl

/-- **The forward bound on a spectral subspace**: for an isolated point `μ` of the spectrum of
the generator with a Riesz projection `P` of finite rank and every `δ > 0`,
`‖T(t) P‖ ≤ C e^{(Re μ + δ) t}` for all `t ≥ 0`. This is `exists_norm_rieszGroup_le` at
nonnegative times, where the group is the semigroup. -/
theorem exists_norm_clm_mul_rieszProjection_le (hr : 0 < r)
    (hiso : closedBall μ r \ {μ} ⊆ hT.generator.resolventSet)
    [FiniteDimensional ℂ
      (LinearMap.range (rieszProjection hT.generator.resolvent μ r).toLinearMap)]
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : NNReal,
      ‖hT.clm t * rieszProjection hT.generator.resolvent μ r‖ ≤
        C * Real.exp ((μ.re + δ) * t) := by
  have hs : sphere μ r ⊆ hT.generator.resolventSet :=
    sphere_subset_of_closedBall_sdiff_subset hr hiso
  obtain ⟨C, hC⟩ := LinearPMap.exists_norm_rieszGroup_le hr hiso hδ
  refine ⟨max C 0, le_max_right _ _, fun t ↦ ?_⟩
  rw [hT.clm_mul_rieszProjection hr hs t]
  have h1 := hC t
  rw [abs_of_nonneg t.coe_nonneg, ← add_mul] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))

/-- **The unstable decomposition.** If the essential growth bound of the semigroup is negative,
then

* the spectrum of the generator `A` in `Re z > 0` is a finite set `Λ` of eigenvalues;
* for some `r > 0`, each circle `C(μ, r)`, `μ ∈ Λ`, surrounds no other point of the spectrum,
  the closed discs are disjoint, and the Riesz projections
  `P_μ = (2πi)⁻¹ ∮_{C(μ, r)} (z - A)⁻¹ dz` have finite rank;
* with `P_s = 1 - Σ_{μ ∈ Λ} P_μ`, for every `δ > 0` there is `C` with
  `‖T(t) P_s‖ ≤ C e^{δt}` for all `t ≥ 0`.

Eigenvalues on the imaginary axis are in the stable part, which is why the bound holds for
every `δ > 0` and not for `δ = 0`. The proof takes `exists_spectral_gap` at `ω = 0`, which gives
a rate `ω' < 0` and decay `e^{ω't}` off the projections of all spectral points with
`Re z > ω'`; those with `Re μ ≤ 0` are moved to the stable part, where each grows at most like
`e^{(Re μ + δ) t} ≤ e^{δt}` (`exists_norm_clm_mul_rieszProjection_le`). This is the form in
which Hou, Wang and Yang use Lemma 4.2 of Albritton, Brué and Colombo (Section 2.2, the second
line of (2.14)). -/
theorem exists_unstable_decomposition (h : hT.essGrowthBound < 0) :
    ∃ (Λ : Finset ℂ) (r : ℝ), 0 < r ∧
      (∀ z : ℂ, z ∈ Λ ↔ z ∈ hT.generator.spectrum ∧ 0 < z.re) ∧
      (∀ μ ∈ Λ, closedBall μ r \ {μ} ⊆ hT.generator.resolventSet) ∧
      (∀ μ ∈ Λ, ∀ ν ∈ Λ, μ ≠ ν → Disjoint (closedBall μ r) (closedBall ν r)) ∧
      (∀ μ ∈ Λ, ∃ x, x ≠ 0 ∧ (x, μ • x) ∈ hT.generator.graph) ∧
      (∀ μ ∈ Λ, FiniteDimensional ℂ
        (LinearMap.range (rieszProjection hT.generator.resolvent μ r).toLinearMap)) ∧
      ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ t : NNReal,
        ‖hT.clm t * (1 - ∑ μ ∈ Λ, rieszProjection hT.generator.resolvent μ r)‖ ≤
          C * Real.exp (δ * t) := by
  classical
  obtain ⟨ω', Λ₀, r, M, hω', hr, hspec, hrre, hrdist, heig, hfin, hM⟩ :=
    hT.exists_spectral_gap (ω := 0) (by simpa using h)
  have hM0 : 0 ≤ M := by simpa using (norm_nonneg _).trans (hM 0)
  have hiso : ∀ μ ∈ Λ₀, closedBall μ r \ {μ} ⊆ hT.generator.resolventSet := fun μ hμ ↦
    LinearPMap.closedBall_sdiff_subset_resolventSet hspec hrre hrdist hμ
  refine ⟨Λ₀.filter fun z ↦ 0 < z.re, r, hr, fun z ↦ ?_,
    fun μ hμ ↦ hiso μ (Finset.mem_filter.mp hμ).1, fun μ hμ ν hν hne ↦ ?_,
    fun μ hμ ↦ heig μ (Finset.mem_filter.mp hμ).1,
    fun μ hμ ↦ hfin μ (Finset.mem_filter.mp hμ).1, fun δ hδ ↦ ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨fun ⟨hz, hzre⟩ ↦ ⟨(hspec z (hω'.trans hzre)).mpr hz, hzre⟩,
      fun ⟨hz, hzre⟩ ↦ ⟨(hspec z (hω'.trans hzre)).mp hz, hzre⟩⟩
  · refine Set.disjoint_left.mpr fun z hz1 hz2 ↦ ?_
    have h1 := hrdist μ (Finset.mem_filter.mp hμ).1 ν (Finset.mem_filter.mp hν).1 hne
    have h2 : dist z μ ≤ r := hz1
    have h3 : dist z ν ≤ r := hz2
    have h4 := dist_triangle_left μ ν z
    linarith
  · -- the stable spectral points grow at most like `e^{δt}`
    have hC : ∀ μ ∈ Λ₀, ∃ Cμ : ℝ, 0 ≤ Cμ ∧ ∀ t : NNReal,
        ‖hT.clm t * rieszProjection hT.generator.resolvent μ r‖ ≤
          Cμ * Real.exp ((μ.re + δ) * t) := fun μ hμ ↦ by
      have := hfin μ hμ
      exact hT.exists_norm_clm_mul_rieszProjection_le hr (hiso μ hμ) hδ
    choose! C hC0 hCb using hC
    refine ⟨M + ∑ μ ∈ Λ₀, C μ, fun t ↦ ?_⟩
    have ht : (0 : ℝ) ≤ t := t.coe_nonneg
    have hsplit : (1 : X →L[ℂ] X) -
        ∑ μ ∈ Λ₀.filter (fun z ↦ 0 < z.re), rieszProjection hT.generator.resolvent μ r =
        (1 - ∑ μ ∈ Λ₀, rieszProjection hT.generator.resolvent μ r) +
          ∑ μ ∈ Λ₀.filter (fun z ↦ ¬0 < z.re), rieszProjection hT.generator.resolvent μ r := by
      rw [← Finset.sum_filter_add_sum_filter_not Λ₀ (fun z : ℂ ↦ 0 < z.re)]
      abel
    rw [hsplit, mul_add, Finset.mul_sum, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (hM t).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith)) hM0)
    · refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine (Finset.sum_le_sum fun μ hμ ↦ ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) fun μ hμ _ ↦ mul_nonneg (hC0 μ hμ) (Real.exp_nonneg _))
      obtain ⟨hμ₀, hμre⟩ := Finset.mem_filter.mp hμ
      exact (hCb μ hμ₀ t).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [not_lt.mp hμre])) (hC0 μ hμ₀))

/-- **The growth bound is determined by the essential growth bound and the spectrum.** If
`ω_ess(T) < ω` and the generator has no spectrum in the half-plane `Re z ≥ ω`, then
`‖T(t)‖ ≤ M e^{ω't}` for some `ω' < ω`. The semigroup decays like `e^{ω't}` off finitely many
Riesz projections (`exists_spectral_gap`), and on each of them it grows like `e^{(Re μ + δ)t}`
with `Re μ < ω` (`exists_norm_clm_mul_rieszProjection_le`). -/
theorem exists_norm_le_exp_of_spectrum_re_lt {ω : ℝ} (hω : hT.essGrowthBound < ω)
    (hσ : ∀ z ∈ hT.generator.spectrum, z.re < ω) :
    ∃ M ω' : ℝ, ω' < ω ∧ ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω' * t) := by
  classical
  obtain ⟨ω₁, Λ, r, M, hω₁, hr, hspec, hrre, hrdist, -, hfin, hM⟩ :=
    hT.exists_spectral_gap hω
  have hM0 : 0 ≤ M := by simpa using (norm_nonneg _).trans (hM 0)
  have hiso : ∀ μ ∈ Λ, closedBall μ r \ {μ} ⊆ hT.generator.resolventSet := fun μ hμ ↦
    LinearPMap.closedBall_sdiff_subset_resolventSet hspec hrre hrdist hμ
  have hΛre : ∀ μ ∈ Λ, μ.re < ω := fun μ hμ ↦
    hσ μ ((hspec μ (by have := hrre μ hμ; linarith)).mpr hμ)
  -- a rate below `ω` and above `ω₁` and the real parts of the points of `Λ`
  obtain ⟨δ, hδ, hδlt⟩ := Finset.exists_pos_forall_lt Λ (fun μ ↦ ω - μ.re)
    fun μ hμ ↦ sub_pos.mpr (hΛre μ hμ)
  obtain ⟨ω', hω'def⟩ : ∃ ω', ω' = max ω₁ (ω - δ / 2) := ⟨_, rfl⟩
  have hω'lt : ω' < ω := by
    rw [hω'def]
    exact max_lt hω₁ (by linarith)
  have hC : ∀ μ ∈ Λ, ∃ Cμ : ℝ, 0 ≤ Cμ ∧ ∀ t : NNReal,
      ‖hT.clm t * rieszProjection hT.generator.resolvent μ r‖ ≤ Cμ * Real.exp (ω' * t) := by
    intro μ hμ
    have := hfin μ hμ
    obtain ⟨C, hC0, hC⟩ :=
      hT.exists_norm_clm_mul_rieszProjection_le hr (hiso μ hμ) (half_pos hδ)
    have h2 : μ.re + δ / 2 ≤ ω' := by
      rw [hω'def]
      exact le_max_of_le_right (by linarith [hδlt μ hμ])
    exact ⟨C, hC0, fun t ↦ (hC t).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h2 t.coe_nonneg)) hC0)⟩
  choose! C hC0 hCb using hC
  refine ⟨M + ∑ μ ∈ Λ, C μ, ω', hω'lt, fun t ↦ ?_⟩
  have hsplit : hT.clm t = hT.clm t * (1 - ∑ μ ∈ Λ, rieszProjection hT.generator.resolvent μ r) +
      ∑ μ ∈ Λ, hT.clm t * rieszProjection hT.generator.resolvent μ r := by
    rw [← Finset.mul_sum, ← mul_add, sub_add_cancel, mul_one]
  rw [← hT.norm_clm t, hsplit, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (hM t).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by rw [hω'def]; exact le_max_left _ _) t.coe_nonneg)) hM0)
  · rw [Finset.sum_mul]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ hμ ↦ hCb μ hμ t)

/-- **The growth bound, the essential growth bound and the spectrum.** For every real `ω`:
`ω₀(T) < ω` if and only if `ω_ess(T) < ω` and the spectrum of the generator lies in the
half-plane `Re z < ω`. -/
theorem growthBound_lt_iff_spectrum {ω : ℝ} :
    T.growthBound < ω ↔ hT.essGrowthBound < ω ∧ ∀ z ∈ hT.generator.spectrum, z.re < ω := by
  rw [growthBound_lt_iff]
  refine ⟨fun ⟨M, ω', hω', hM⟩ ↦ ⟨(hT.essGrowthBound_le_of_norm_le hM).trans_lt
    (EReal.coe_lt_coe_iff.mpr hω'), fun z hz ↦ ?_⟩,
    fun ⟨hω, hσ⟩ ↦ hT.exists_norm_le_exp_of_spectrum_re_lt hω hσ⟩
  by_contra hzω
  exact hz (hT.mem_resolventSet_generator hM (hω'.trans_le (not_lt.mp hzω)))

/-- **The growth bound is the maximum of the essential growth bound and the spectral bound**:
`ω₀(T) = max (ω_ess(T), s(A))` in `[-∞, ∞]`. If `ω_ess(T) < ω₀(T)`, the equality says
`ω₀(T) = s(A)`. Both bounds are at most `ω₀` (`essGrowthBound_le_growthBound`,
`spectralBound_generator_le_growthBound`), and a real `ω` above both is above `ω₀` by
`growthBound_lt_iff_spectrum`. -/
theorem growthBound_eq_max :
    T.growthBound = max hT.essGrowthBound hT.generator.spectralBound := by
  refine le_antisymm ?_
    (max_le hT.essGrowthBound_le_growthBound hT.spectralBound_generator_le_growthBound)
  by_contra hlt
  obtain ⟨ω, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp (not_le.mp hlt)
  have h3 := max_lt_iff.mp h1
  refine h2.not_gt (hT.growthBound_lt_iff_spectrum.mpr ⟨h3.1, fun z hz ↦ ?_⟩)
  exact EReal.coe_lt_coe_iff.mp ((LinearPMap.re_le_spectralBound hz).trans_lt h3.2)

/-- **The unstable decomposition with two-sided bounds.** If the essential growth bound of
the semigroup is negative, there are a finite set `Λ` and a radius `r > 0` such that, with
`P_μ` the Riesz projection of the generator `A` on the circle `C(μ, r)`, `G_μ` the group
`LinearPMap.rieszGroup` and `P_s = 1 - Σ_{μ ∈ Λ} P_μ`:

* `Λ` is the spectrum of `A` in `Re z > 0`, every point of `Λ` is an eigenvalue, the closed
  discs of radius `r` around the points of `Λ` are disjoint, and each contains no other point of
  the spectrum (so each `P_μ` is a projection and `P_μ P_ν = 0` for `μ ≠ ν`, by
  `LinearPMap.isIdempotentElem_rieszProjection_resolvent` and
  `LinearPMap.rieszProjection_resolvent_mul_of_disjoint`);
* `P_s` is a projection that commutes with the semigroup, and every `P_μ` has finite rank;
* `T(t) P_μ = G_μ(t)` for `t ≥ 0`;
* for every `δ > 0`, `c e^{Re μ τ - δ|τ|} ‖f‖ ≤ ‖G_μ(τ) f‖ ≤ C e^{Re μ τ + δ|τ|} ‖f‖` for all real
  `τ` and all `f` in the range of `P_μ`, and `‖T(t) P_s‖ ≤ C e^{δt}` for `t ≥ 0`.

This is the decomposition of Hou, Wang and Yang (Section 2.2) with both lines of their bounds
(2.14) in one statement, with `e^{τ A_j}` read as `G_μ(τ)` on `X_j`, the range of `P_μ`. Every
clause of `exists_unstable_decomposition` is a clause here, for the same `Λ` and `r`. It
assembles that theorem, `clm_mul_rieszProjection`, `exists_norm_rieszGroup_le` and
`exists_le_norm_rieszGroup_apply`. -/
theorem exists_unstable_decomposition_bounds (h : hT.essGrowthBound < 0) :
    ∃ (Λ : Finset ℂ) (r : ℝ), 0 < r ∧
      (∀ z : ℂ, z ∈ Λ ↔ z ∈ hT.generator.spectrum ∧ 0 < z.re) ∧
      (∀ μ ∈ Λ, closedBall μ r \ {μ} ⊆ hT.generator.resolventSet) ∧
      (∀ μ ∈ Λ, ∀ ν ∈ Λ, μ ≠ ν → Disjoint (closedBall μ r) (closedBall ν r)) ∧
      (∀ μ ∈ Λ, ∃ x, x ≠ 0 ∧ (x, μ • x) ∈ hT.generator.graph) ∧
      IsIdempotentElem (1 - ∑ μ ∈ Λ, rieszProjection hT.generator.resolvent μ r) ∧
      (∀ t : NNReal,
        Commute (hT.clm t) (1 - ∑ μ ∈ Λ, rieszProjection hT.generator.resolvent μ r)) ∧
      (∀ μ ∈ Λ, FiniteDimensional ℂ
        (LinearMap.range (rieszProjection hT.generator.resolvent μ r).toLinearMap)) ∧
      (∀ μ ∈ Λ, ∀ t : NNReal, hT.clm t * rieszProjection hT.generator.resolvent μ r =
        hT.generator.rieszGroup μ r t) ∧
      ∀ δ : ℝ, 0 < δ →
        (∀ μ ∈ Λ, ∃ C c : ℝ, 0 < c ∧ ∀ (τ : ℝ) (f : X),
          rieszProjection hT.generator.resolvent μ r f = f →
            c * Real.exp (μ.re * τ - δ * |τ|) * ‖f‖ ≤ ‖hT.generator.rieszGroup μ r τ f‖ ∧
            ‖hT.generator.rieszGroup μ r τ f‖ ≤ C * Real.exp (μ.re * τ + δ * |τ|) * ‖f‖) ∧
        ∃ C : ℝ, ∀ t : NNReal,
          ‖hT.clm t * (1 - ∑ μ ∈ Λ, rieszProjection hT.generator.resolvent μ r)‖ ≤
            C * Real.exp (δ * t) := by
  obtain ⟨Λ, r, hr, hΛ, hiso, hdisj, heig, hfin, hstable⟩ :=
    hT.exists_unstable_decomposition h
  have hs : ∀ μ ∈ Λ, sphere μ r ⊆ hT.generator.resolventSet := fun μ hμ ↦
    sphere_subset_of_closedBall_sdiff_subset hr (hiso μ hμ)
  refine ⟨Λ, r, hr, hΛ, hiso, hdisj, heig,
    (LinearPMap.isIdempotentElem_sum_rieszProjection_resolvent hr hs hdisj).one_sub,
    fun t ↦ (Commute.one_right _).sub_right (Commute.sum_right _ _ _ fun μ hμ ↦
      LinearPMap.commute_rieszProjection_resolvent hr.le (hs μ hμ)
        fun _ _ hxy ↦ hT.map_mem_graph t hxy),
    hfin, fun μ hμ t ↦ hT.clm_mul_rieszProjection hr (hs μ hμ) t,
    fun δ hδ ↦ ⟨fun μ hμ ↦ ?_, hstable δ hδ⟩⟩
  have := hfin μ hμ
  obtain ⟨C, hC⟩ := LinearPMap.exists_norm_rieszGroup_le hr (hiso μ hμ) hδ
  obtain ⟨C', hC'0, hC'⟩ := LinearPMap.exists_le_norm_rieszGroup_apply hr (hiso μ hμ) hδ
  refine ⟨C, C'⁻¹, inv_pos.mpr hC'0, fun τ f hf ↦ ⟨?_, ?_⟩⟩
  · rw [mul_assoc, inv_mul_le_iff₀ hC'0]
    exact hC' τ f hf
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hC τ) (norm_nonneg f))

end PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsComplexLinear
