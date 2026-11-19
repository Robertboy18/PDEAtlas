/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityLipschitz
import Mathlib.Analysis.Real.Pi.Bounds
import PDE.Analysis.Normed.PiLp.CoordinateProjection
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import PDE.Analysis.Calculus.FaaDiBrunoBounds

/-!
# Higher-order Hölder estimates of the half-plane velocity

Let `f` be `C^k` within the closed upper half-plane `H̄ = {x₁ ≥ 0}` and vanish there outside a disc.
Write `D^j` for the `j`-th derivative within `H̄` (`iteratedFDerivWithin ℝ j · H̄`) and
`u(f) = halfPlaneVelocity f`. Then `u(f)` is `C^k` within `H̄`, and `C^{k+1}` with a Hölder top
derivative when `D^k f` is Hölder; all its derivatives up to that order have explicit size bounds.

The top-order Hölder estimate is free of masses; the size bounds and the log-Lipschitz modulus
contain the masses `∫ ‖D^j f‖`, which for data supported in a disc of radius `R` are at most
`πR²/2` times the corresponding supremum.

## Main results

* `contDiffOn_halfPlaneVelocity`: `u(f)` is `C^k` within `H̄`, and its derivatives are linear in
  `f` (`iteratedFDerivWithin_halfPlaneVelocity_sub`).
* `norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le`: if `D^k f` is `α`-Hölder on `H̄` with
  constant `M`, `0 < α < 1`, then `u(f)` is `C^{k+1}` within `H̄`
  (`contDiffOn_succ_halfPlaneVelocity`) and
  `‖D^{k+1} u(f)(x) - D^{k+1} u(f)(x')‖ ≤ (844/(α(1-α)) + k) M |x - x'|^α`. The estimate is
  homogeneous: no lower-order or low-frequency term enters.
* `norm_iteratedFDerivWithin_halfPlaneVelocity_le_holder`: with `‖D^k f‖ ≤ B` on `H̄` and
  `∫_{ℝ²₊} ‖D^k f‖ ≤ L`, `‖D^{k+1} u(f)‖ ≤ 4(50M/α + 8B + 10L) + kB`; the Kato forms
  `norm_iteratedFDerivWithin_halfPlaneVelocity_le_kato` and
  `norm_iteratedFDerivWithin_halfPlaneVelocity_le_kato_homogeneous` have
  `(50/α)(1 + B log(2 + M))` or, for `B > 0`, `(50B/α)(1 + log(2 + M/B))` in place of `50M/α`.
* `norm_iteratedFDerivWithin_halfPlaneVelocity_le`: below the top order, for `f` `C^{j+1}` within
  `H̄` with `‖D^{j+1} f‖ ≤ B`, `∫_{ℝ²₊} ‖D^{j+1} f‖ ≤ L` and `‖D^j f‖ ≤ B'`,
  `‖D^{j+1} u(f)‖ ≤ B + L/π + (j + 1) B'` (and `‖u(f)‖ ≤ B + L/π` at order zero).
* `contDiffOn_halfSpaceGreenPotential`: the Green stream is `C^{k+1}` within `H̄` for `C^k` data,
  and `C^{k+2}` for `C^{k,α}` data (`contDiffOn_succ_succ_halfSpaceGreenPotential`).
* `norm_iteratedFDerivWithin_halfPlaneVelocity_le_mul`: the sizes
  `‖D^j u(f)‖ ≤ (200/α + 40π(1 + R²) + k + 33) N` for `j ≤ k + 1`, for data supported in the
  disc of radius `R` with `C^{k,α}` norm at most `N`; with the seminorm bound
  `(844/(α(1-α)) + k) N` this bounds the `C^{k+1,α}` norm of `u(f)` by the larger of the two
  constants times `N`. The component forms are
  `norm_iteratedFDerivWithin_halfPlaneVelocity_apply_le` and
  `norm_iteratedFDerivWithin_halfPlaneVelocity_apply_sub_le`.
* `dist_fderivWithin_halfPlaneVelocity_le_log`: for `C¹` data the derivative of the velocity is
  log-Lipschitz on `H̄`, `‖Du(x) - Du(x')‖ ≤ |x - x'| (11B + 4L + 4B log⁺(1/|x - x'|))` with
  `‖Df‖ ≤ B` and `∫_{ℝ²₊} ‖Df‖ ≤ L`.
* `holderOnWith_iteratedFDerivWithin_halfPlaneVelocity`: the statement for compactly supported
  `f ∈ C^k(ℝ²)` with `D^k f` globally `α`-Hölder, as a `HolderOnWith` bound on `H̄`.

## How it works

Since the tangential derivative `∂₀` commutes with the velocity, the derivative of the velocity on
`H̄` is `D u(f) = divFreeDeriv (u(∂₀f)) f` (`fderivWithin_halfPlaneVelocity_of_contDiffOn`).
Differentiating `j` more times gives

`D^{j+1} u(f) = T ∘ D^j u(∂₀f) + N ∘ D^j f`

with linear maps `‖T‖, ‖N‖ ≤ 1`, and `D^j(∂₀f)` is a partial evaluation of `D^{j+1} f`
(`norm_iteratedFDerivWithin_partialDerivWithin_sub_le`). We induct on the order and apply the
statement of one order lower to `∂₀f`, which still vanishes outside the disc. The base cases are the
first-order estimates: the Hölder bound `844/(α(1-α)) M` for `Du`
(`dist_fderivWithin_halfPlaneVelocity_le`), the size bounds for `Du`
(`norm_fderivWithin_halfPlaneVelocity_le_holder` and its Kato forms) and, below the top order, the
bound `B + L/π` for the velocity itself (`norm_halfPlaneVelocity_le_of_continuousOn`). Each step
adds the term `N ∘ D^j f` once, which gives the summands `k M` and `k B` in the constants. The
log-Lipschitz modulus uses the same formula for `Du`: the velocity of `∂₀f` is log-Lipschitz, and
`f` is Lipschitz on the convex set `H̄`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal
open GreenFunction PotentialTheory.Planar SobolevSpace
open PDE.Analysis (evenReflection evenReflection_of_nonneg continuous_evenReflection
  hasCompactSupport_evenReflection_of_eq_zero)

namespace IncompressibleFlow

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {f : ℝ^2 → ℝ}

/-! ### Iterated derivatives within the closed half-plane -/

/-- At two points of the closed half-plane, the `(n + 1)`-th iterated derivatives within it differ
by as much as the `n`-th iterated derivatives of the derivative. -/
theorem norm_iteratedFDerivWithin_succ_sub {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : ℝ^2 → F) {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ (n + 1) g H̄ x - iteratedFDerivWithin ℝ (n + 1) g H̄ x'‖ =
      ‖iteratedFDerivWithin ℝ n (fderivWithin ℝ g H̄) H̄ x -
        iteratedFDerivWithin ℝ n (fderivWithin ℝ g H̄) H̄ x'‖ := by
  rw [← dist_eq_norm, ← dist_eq_norm,
    iteratedFDerivWithin_succ_eq_comp_right uniqueDiffOn_closedUpper hx,
    iteratedFDerivWithin_succ_eq_comp_right uniqueDiffOn_closedUpper hx',
    Function.comp_apply, Function.comp_apply, LinearIsometryEquiv.dist_map]

/-- Iterated derivatives within the closed half-plane of a function vanishing there outside a
disc vanish there outside the same disc. -/
theorem iteratedFDerivWithin_eq_zero_of_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : ℝ^2 → F} {R : ℝ} (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → g y = 0)
    (n : ℕ) {y : ℝ^2} (hy : 0 ≤ y 1) (hyR : R < ‖y‖) : iteratedFDerivWithin ℝ n g H̄ y = 0 := by
  have hev : g =ᶠ[𝓝[H̄] y] fun _ ↦ 0 := by
    have hopen : {z : ℝ^2 | R < ‖z‖} ∈ 𝓝 y :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hyR
    filter_upwards [inter_mem_nhdsWithin H̄ hopen] with z hz
    exact hR z hz.1 hz.2
  rw [hev.iteratedFDerivWithin_eq (hR y hy hyR) n]
  cases n with
  | zero => ext v; simp
  | succ n => rw [iteratedFDerivWithin_succ_const]; rfl

/-- A real function continuous on the closed half-plane and vanishing there outside a disc is
integrable on the open half-plane. -/
theorem integrableOn_upper_of_continuousOn {g : ℝ^2 → ℝ} {R : ℝ} (hg : ContinuousOn g H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → g y = 0) : IntegrableOn g (HalfSpace.upper 2) :=
  ((continuous_evenReflection hg).integrable_of_hasCompactSupport
    (hasCompactSupport_evenReflection_of_eq_zero hR)).integrableOn.congr_fun
    (fun _ hy ↦ evenReflection_of_nonneg (le_of_lt hy))
    (HalfSpace.measurableSet_upper (n := 2))

/-! ### The tangential derivative of the data -/

/-- Evaluation at `e₀` has operator norm at most one on the functionals of the plane. -/
private theorem norm_apply_single_le :
    ‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L ↦ by
    rw [ContinuousLinearMap.apply_apply, one_mul]
    simpa using L.le_opNorm (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))

/-- For `f` `C^{k+1}` within `H̄`, at points of `H̄` the derivative `D^k(∂₀^H f)` is `D^k(D^H f)`
followed by evaluation at `e₀`. -/
private theorem iteratedFDerivWithin_partialDerivWithin {k : ℕ}
    (hf : ContDiffOn ℝ (k + 1) f H̄) {y : ℝ^2} (hy : 0 ≤ y 1) :
    iteratedFDerivWithin ℝ k (PDE.partialDerivWithin 0 f H̄) H̄ y =
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).compContinuousMultilinearMap
        (iteratedFDerivWithin ℝ k (fderivWithin ℝ f H̄) H̄ y) := by
  have hφ : ContDiffOn ℝ k (fderivWithin ℝ f H̄) H̄ :=
    hf.fderivWithin uniqueDiffOn_closedUpper le_rfl
  have he : PDE.partialDerivWithin 0 f H̄ =
      ⇑(ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) ∘
        fderivWithin ℝ f H̄ :=
    funext fun _ ↦ (ContinuousLinearMap.apply_apply _ _).symm
  rw [he]
  exact (ContinuousLinearMap.apply ℝ ℝ _).iteratedFDerivWithin_comp_left (hφ y hy)
    uniqueDiffOn_closedUpper hy le_rfl

/-- The differences of `D^k(∂₀^H f)` are bounded by those of `D^{k+1} f`. -/
theorem norm_iteratedFDerivWithin_partialDerivWithin_sub_le {k : ℕ}
    (hf : ContDiffOn ℝ (k + 1) f H̄) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    ‖iteratedFDerivWithin ℝ k (PDE.partialDerivWithin 0 f H̄) H̄ y -
        iteratedFDerivWithin ℝ k (PDE.partialDerivWithin 0 f H̄) H̄ z‖ ≤
      ‖iteratedFDerivWithin ℝ (k + 1) f H̄ y - iteratedFDerivWithin ℝ (k + 1) f H̄ z‖ := by
  rw [iteratedFDerivWithin_partialDerivWithin hf hy, iteratedFDerivWithin_partialDerivWithin hf hz,
    norm_iteratedFDerivWithin_succ_sub f hy hz k]
  set A := ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
  set a := iteratedFDerivWithin ℝ k (fderivWithin ℝ f H̄) H̄ y
  set b := iteratedFDerivWithin ℝ k (fderivWithin ℝ f H̄) H̄ z
  have e : A.compContinuousMultilinearMap a - A.compContinuousMultilinearMap b =
      A.compContinuousMultilinearMap (a - b) := by
    ext v; simp
  rw [e]
  exact (A.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_of_le_one_left (norm_nonneg _) norm_apply_single_le)

/-- `‖D^k(∂₀^H f)‖ ≤ ‖D^{k+1} f‖` pointwise. -/
theorem norm_iteratedFDerivWithin_partialDerivWithin_le {k : ℕ}
    (hf : ContDiffOn ℝ (k + 1) f H̄) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖iteratedFDerivWithin ℝ k (PDE.partialDerivWithin 0 f H̄) H̄ y‖ ≤
      ‖iteratedFDerivWithin ℝ (k + 1) f H̄ y‖ := by
  rw [iteratedFDerivWithin_partialDerivWithin hf hy,
    ← norm_iteratedFDerivWithin_fderivWithin uniqueDiffOn_closedUpper hy]
  exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) norm_apply_single_le)

/-! ### The recursion for the derivatives of the velocity -/

/-- The vorticity part as a linear map of the vorticity. -/
private def vorticityMap : ℝ →L[ℝ] (ℝ^2 →L[ℝ] ℝ^2) :=
  ContinuousLinearMap.toSpanSingleton ℝ divFreeVorticity

/-- The vorticity map has norm at most one. -/
private theorem norm_vorticityMap_le : ‖vorticityMap‖ ≤ 1 := by
  rw [vorticityMap, ContinuousLinearMap.norm_toSpanSingleton]
  exact norm_divFreeVorticity_le

/-- For `f` `C¹` within `H̄` and vanishing there outside a disc, on `H̄` the derivative of the
velocity is `D^H u(f) = T(u(∂₀^H f)) + N(f)`, with `T = divFreeTangential` and
`N = vorticityMap`. -/
private theorem fderivWithin_eqOn {R : ℝ} (hf : ContDiffOn ℝ 1 f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) :
    EqOn (fderivWithin ℝ (halfPlaneVelocity f) H̄)
      ((⇑divFreeTangential ∘ halfPlaneVelocity (PDE.partialDerivWithin 0 f H̄)) +
        (⇑vorticityMap ∘ f)) H̄ := by
  intro x hx
  rw [fderivWithin_halfPlaneVelocity_of_contDiffOn hf hR hx]
  simp [divFreeDeriv, vorticityMap, ContinuousLinearMap.toSpanSingleton_apply]

/-- The recursion `D^n(D^H u(f)) = T ∘ D^n u(∂₀^H f) + N ∘ D^n f` at points of `H̄`, for `f` `C^n`
within `H̄` and vanishing there outside a disc, with `u(∂₀^H f)` `C^n` within `H̄`. -/
private theorem iteratedFDerivWithin_fderivWithin_eq {n : ℕ} {R : ℝ} (hf1 : ContDiffOn ℝ 1 f H̄)
    (hfn : ContDiffOn ℝ n f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hug : ContDiffOn ℝ n (halfPlaneVelocity (PDE.partialDerivWithin 0 f H̄)) H̄) {x : ℝ^2}
    (hx : 0 ≤ x 1) :
    iteratedFDerivWithin ℝ n (fderivWithin ℝ (halfPlaneVelocity f) H̄) H̄ x =
      divFreeTangential.compContinuousMultilinearMap
          (iteratedFDerivWithin ℝ n (halfPlaneVelocity (PDE.partialDerivWithin 0 f H̄)) H̄ x) +
        vorticityMap.compContinuousMultilinearMap (iteratedFDerivWithin ℝ n f H̄ x) := by
  rw [iteratedFDerivWithin_congr (fderivWithin_eqOn hf1 hR) hx n,
    iteratedFDerivWithin_add_apply ((divFreeTangential.contDiff.comp_contDiffOn hug) x hx)
      ((vorticityMap.contDiff.comp_contDiffOn hfn) x hx) uniqueDiffOn_closedUpper hx,
    divFreeTangential.iteratedFDerivWithin_comp_left (hug x hx) uniqueDiffOn_closedUpper hx le_rfl,
    vorticityMap.iteratedFDerivWithin_comp_left (hfn x hx) uniqueDiffOn_closedUpper hx le_rfl]

/-- Since `‖T‖, ‖N‖ ≤ 1`, `‖(T ∘ a + N ∘ b) - (T ∘ a' + N ∘ b')‖ ≤ ‖a - a'‖ + ‖b - b'‖`. -/
private theorem norm_comp_add_sub_le {n : ℕ}
    (a a' : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ ℝ^2) (ℝ^2))
    (b b' : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ ℝ^2) ℝ) :
    ‖(divFreeTangential.compContinuousMultilinearMap a +
        vorticityMap.compContinuousMultilinearMap b) -
      (divFreeTangential.compContinuousMultilinearMap a' +
        vorticityMap.compContinuousMultilinearMap b')‖ ≤ ‖a - a'‖ + ‖b - b'‖ := by
  have e : (divFreeTangential.compContinuousMultilinearMap a +
        vorticityMap.compContinuousMultilinearMap b) -
      (divFreeTangential.compContinuousMultilinearMap a' +
        vorticityMap.compContinuousMultilinearMap b') =
      divFreeTangential.compContinuousMultilinearMap (a - a') +
        vorticityMap.compContinuousMultilinearMap (b - b') := by
    ext v : 1
    simp [map_sub]
    abel
  rw [e]
  refine (norm_add_le (divFreeTangential.compContinuousMultilinearMap (a - a'))
    (vorticityMap.compContinuousMultilinearMap (b - b'))).trans (add_le_add ?_ ?_)
  · exact (divFreeTangential.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_of_le_one_left (norm_nonneg _) norm_divFreeTangential_le)
  · exact (vorticityMap.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_of_le_one_left (norm_nonneg _) norm_vorticityMap_le)

/-- Since `‖T‖, ‖N‖ ≤ 1`, `‖T ∘ a + N ∘ b‖ ≤ ‖a‖ + ‖b‖`. -/
private theorem norm_comp_add_le {n : ℕ}
    (a : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ ℝ^2) (ℝ^2))
    (b : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ ℝ^2) ℝ) :
    ‖divFreeTangential.compContinuousMultilinearMap a +
        vorticityMap.compContinuousMultilinearMap b‖ ≤ ‖a‖ + ‖b‖ :=
  (norm_add_le (divFreeTangential.compContinuousMultilinearMap a)
    (vorticityMap.compContinuousMultilinearMap b)).trans (add_le_add
    ((divFreeTangential.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_of_le_one_left (norm_nonneg _) norm_divFreeTangential_le))
    ((vorticityMap.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_of_le_one_left (norm_nonneg _) norm_vorticityMap_le)))

/-! ### Regularity -/

/-- **Regularity of the velocity up to the boundary.** For `f` `C^m` within the closed
half-plane and vanishing there outside a disc, the velocity is `C^m` within the closed
half-plane. -/
theorem contDiffOn_halfPlaneVelocity {m : ℕ} {R : ℝ} (hf : ContDiffOn ℝ m f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) :
    ContDiffOn ℝ m (halfPlaneVelocity f) H̄ := by
  induction m generalizing f with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero] at hf ⊢
    exact (continuous_halfPlaneVelocity_of_continuousOn hf hR).continuousOn
  | succ m ih =>
    rw [Nat.cast_add_one] at hf ⊢
    have hf1 : ContDiffOn ℝ 1 f H̄ := hf.of_le le_add_self
    have hug := ih (hf.partialDerivWithin 0 uniqueDiffOn_closedUpper le_rfl)
      (partialDerivWithin_eq_zero_of_eq_zero hR 0)
    refine (contDiffOn_succ_iff_fderivWithin uniqueDiffOn_closedUpper).2
      ⟨fun x hx ↦
        (hasFDerivWithinAt_halfPlaneVelocity_of_contDiffOn hf1 hR hx).differentiableWithinAt,
        by simp, ?_⟩
    exact ((divFreeTangential.contDiff.comp_contDiffOn hug).add
      (vorticityMap.contDiff.comp_contDiffOn (hf.of_le le_self_add))).congr
        fun x hx ↦ fderivWithin_eqOn hf1 hR hx

/-- **Linearity of the derivatives.** For `f, g` continuous on the closed half-plane and
vanishing there outside discs, with velocities `C^m` within it,
`D^m u(f - g) = D^m u(f) - D^m u(g)` on the closed half-plane. The regularity of the velocities
comes from `contDiffOn_halfPlaneVelocity` (`C^m` data) or `contDiffOn_succ_halfPlaneVelocity`
(`C^{m-1,α}` data), so every estimate below applies to differences. -/
theorem iteratedFDerivWithin_halfPlaneVelocity_sub {m : ℕ} {g : ℝ^2 → ℝ} {R R' : ℝ}
    (hf : ContinuousOn f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hg : ContinuousOn g H̄) (hR' : ∀ y : ℝ^2, 0 ≤ y 1 → R' < ‖y‖ → g y = 0)
    (huf : ContDiffOn ℝ m (halfPlaneVelocity f) H̄) (hug : ContDiffOn ℝ m (halfPlaneVelocity g) H̄)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    iteratedFDerivWithin ℝ m (halfPlaneVelocity (f - g)) H̄ x =
      iteratedFDerivWithin ℝ m (halfPlaneVelocity f) H̄ x -
        iteratedFDerivWithin ℝ m (halfPlaneVelocity g) H̄ x := by
  rw [halfPlaneVelocity_sub_of_continuousOn hf hR hg hR']
  exact iteratedFDerivWithin_sub_apply (huf x hx) (hug x hx) uniqueDiffOn_closedUpper hx

/-! ### The top-order Hölder estimate -/

/-- A function with a Hölder bound on a set is continuous on it. -/
private theorem continuousOn_of_dist_le {F : Type*} [PseudoMetricSpace F] {g : ℝ^2 → F}
    {s : Set (ℝ^2)} {C α : ℝ} (hα : 0 < α)
    (hg : ∀ x ∈ s, ∀ y ∈ s, dist (g x) (g y) ≤ C * ‖x - y‖ ^ α) : ContinuousOn g s := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hC : 0 < |C| + 1 := by positivity
  refine ⟨(ε / (|C| + 1)) ^ (1 / α), by positivity, fun {y} hy hyx ↦ ?_⟩
  rw [dist_eq_norm] at hyx
  calc dist (g y) (g x) ≤ C * ‖y - x‖ ^ α := hg y hy x hx
    _ ≤ (|C| + 1) * ‖y - x‖ ^ α := by
        gcongr
        linarith [le_abs_self C]
    _ < (|C| + 1) * ((ε / (|C| + 1)) ^ (1 / α)) ^ α := by
        gcongr
    _ = ε := by
        rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one]
        field_simp

section Holder

variable {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
include hα hα1

/-- For `f` `C^k` within `H̄`, vanishing there outside a disc, with `D^k f` `α`-Hölder on `H̄` with
constant `M`, the velocity is `C^{k+1}` within `H̄` and
`‖D^{k+1} u(x) - D^{k+1} u(x')‖ ≤ (844/(α(1-α)) + k) M |x - x'|^α` on `H̄`. -/
private theorem contDiffOn_succ_halfPlaneVelocity_and_norm_sub_le (k : ℕ) :
    ∀ {f : ℝ^2 → ℝ} {R M : ℝ}, ContDiffOn ℝ k f H̄ →
    (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) →
    (∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ M * ‖y - z‖ ^ α) →
    ContDiffOn ℝ (k + 1) (halfPlaneVelocity f) H̄ ∧
      ∀ x x' : ℝ^2, 0 ≤ x 1 → 0 ≤ x' 1 →
        ‖iteratedFDerivWithin ℝ (k + 1) (halfPlaneVelocity f) H̄ x -
            iteratedFDerivWithin ℝ (k + 1) (halfPlaneVelocity f) H̄ x'‖ ≤
          (844 / (α * (1 - α)) + k) * M * ‖x - x'‖ ^ α := by
  induction k with
  | zero =>
    intro f R M hf hR hM
    rw [Nat.cast_zero, contDiffOn_zero] at hf
    have hM' : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α :=
      fun y z hy hz ↦ by
        have := hM y z hy hz
        rwa [PDE.Analysis.norm_iteratedFDerivWithin_zero_sub, Real.norm_eq_abs] at this
    have hdist := fun (x : ℝ^2) (hx : 0 ≤ x 1) (x' : ℝ^2) (hx' : 0 ≤ x' 1) ↦
      dist_fderivWithin_halfPlaneVelocity_le hf hR hα hα1 hM' hx hx'
    refine ⟨?_, fun x x' hx hx' ↦ ?_⟩
    · rw [Nat.cast_zero]
      exact (contDiffOn_succ_iff_fderivWithin uniqueDiffOn_closedUpper).2
        ⟨differentiableOn_halfPlaneVelocity hf hR hα hα1 hM', by simp,
          contDiffOn_zero.mpr (continuousOn_of_dist_le hα fun x hx x' hx' ↦ hdist x hx x' hx')⟩
    · rw [Nat.cast_zero, add_zero, norm_iteratedFDerivWithin_succ_sub _ hx hx',
        PDE.Analysis.norm_iteratedFDerivWithin_zero_sub, ← dist_eq_norm]
      exact hdist x hx x' hx'
  | succ k ih =>
    intro f R M hf hR hM
    rw [Nat.cast_add_one] at hf
    have hf1 : ContDiffOn ℝ 1 f H̄ := hf.of_le le_add_self
    have hg : ContDiffOn ℝ k (PDE.partialDerivWithin 0 f H̄) H̄ :=
      hf.partialDerivWithin 0 uniqueDiffOn_closedUpper le_rfl
    obtain ⟨hug, hugM⟩ := ih hg (partialDerivWithin_eq_zero_of_eq_zero hR 0)
      fun y z hy hz ↦ (norm_iteratedFDerivWithin_partialDerivWithin_sub_le hf hy hz).trans
        (hM y z hy hz)
    have hf' : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f H̄ := by rwa [Nat.cast_add_one]
    have hug' : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
        (halfPlaneVelocity (PDE.partialDerivWithin 0 f H̄)) H̄ := by rwa [Nat.cast_add_one]
    refine ⟨?_, fun x x' hx hx' ↦ ?_⟩
    · refine (contDiffOn_succ_iff_fderivWithin uniqueDiffOn_closedUpper).2
        ⟨fun x hx ↦
          (hasFDerivWithinAt_halfPlaneVelocity_of_contDiffOn hf1 hR hx).differentiableWithinAt,
          by simp, ?_⟩
      exact ((divFreeTangential.contDiff.comp_contDiffOn hug').add
        (vorticityMap.contDiff.comp_contDiffOn hf')).congr fun y hy ↦ fderivWithin_eqOn hf1 hR hy
    · rw [norm_iteratedFDerivWithin_succ_sub _ hx hx',
        iteratedFDerivWithin_fderivWithin_eq hf1 hf' hR hug' hx,
        iteratedFDerivWithin_fderivWithin_eq hf1 hf' hR hug' hx']
      refine (norm_comp_add_sub_le _ _ _ _).trans ?_
      calc _ ≤ (844 / (α * (1 - α)) + k) * M * ‖x - x'‖ ^ α + M * ‖x - x'‖ ^ α :=
            add_le_add (hugM x x' hx hx') (hM x x' hx hx')
        _ = (844 / (α * (1 - α)) + ((k + 1 : ℕ) : ℝ)) * M * ‖x - x'‖ ^ α := by
            push_cast; ring

/-- **The velocity is `C^{k+1}` up to the boundary for `C^{k,α}` vorticity.** For `f` `C^k`
within the closed half-plane, vanishing there outside a disc, with `D^k f` `α`-Hölder on the
closed half-plane (`0 < α < 1`), the velocity is `C^{k+1}` within the closed half-plane. -/
theorem contDiffOn_succ_halfPlaneVelocity {k : ℕ} {R M : ℝ} (hf : ContDiffOn ℝ k f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ M * ‖y - z‖ ^ α) :
    ContDiffOn ℝ (k + 1) (halfPlaneVelocity f) H̄ :=
  (contDiffOn_succ_halfPlaneVelocity_and_norm_sub_le hα hα1 k hf hR hM).1

/-- **The `C^{k+1,α}` estimate of the velocity up to the boundary.** Under the hypotheses of
`contDiffOn_succ_halfPlaneVelocity`, for `x, x'` in the closed half-plane
`‖D^{k+1} u(x) - D^{k+1} u(x')‖ ≤ (844/(α(1-α)) + k) · M |x - x'|^α`, with `D` the derivatives
within the closed half-plane. -/
theorem norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le {k : ℕ} {R M : ℝ}
    (hf : ContDiffOn ℝ k f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ M * ‖y - z‖ ^ α)
    {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    ‖iteratedFDerivWithin ℝ (k + 1) (halfPlaneVelocity f) H̄ x -
        iteratedFDerivWithin ℝ (k + 1) (halfPlaneVelocity f) H̄ x'‖ ≤
      (844 / (α * (1 - α)) + k) * M * ‖x - x'‖ ^ α :=
  (contDiffOn_succ_halfPlaneVelocity_and_norm_sub_le hα hα1 k hf hR hM).2 x x' hx hx'

end Holder

/-! ### Sizes of the derivatives -/

/-- The bounds on `D^k f` pass to `D^{k-1}(∂₀^H f)`, including the mass on the open half-plane. -/
private theorem setIntegral_norm_iteratedFDerivWithin_partialDerivWithin_le {k : ℕ} {R L : ℝ}
    (hf : ContDiffOn ℝ (k + 1) f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hL : ∫ y in HalfSpace.upper 2, ‖iteratedFDerivWithin ℝ (k + 1) f H̄ y‖ ≤ L) :
    ∫ y in HalfSpace.upper 2,
      ‖iteratedFDerivWithin ℝ k (PDE.partialDerivWithin 0 f H̄) H̄ y‖ ≤ L := by
  have hint : IntegrableOn (fun y ↦ ‖iteratedFDerivWithin ℝ (k + 1) f H̄ y‖)
      (HalfSpace.upper 2) :=
    integrableOn_upper_of_continuousOn
      ((hf.continuousOn_iteratedFDerivWithin le_rfl uniqueDiffOn_closedUpper).norm)
      fun y hy hyR ↦ by rw [iteratedFDerivWithin_eq_zero_of_eq_zero hR _ hy hyR, norm_zero]
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun y ↦ norm_nonneg _) hint ?_) hL
  filter_upwards [ae_restrict_mem (HalfSpace.measurableSet_upper (n := 2))] with y hy
  exact norm_iteratedFDerivWithin_partialDerivWithin_le hf (le_of_lt hy)

section Size

variable {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
include hα hα1

/-- The top-order size bound, for any first-order bound `c` of `D u(f)` within `H̄` valid for all
data `C⁰` within `H̄` with the stated Hölder constant, bound and mass. -/
private theorem norm_iteratedFDerivWithin_halfPlaneVelocity_le_of_fderivWithin_le {M B L c : ℝ}
    (base : ∀ {f : ℝ^2 → ℝ} {R : ℝ}, ContinuousOn f H̄ →
      (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) →
      (∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α) →
      (∀ y, 0 ≤ y 1 → |f y| ≤ B) → ∫ y in HalfSpace.upper 2, |f y| ≤ L →
      ∀ x : ℝ^2, 0 ≤ x 1 → ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ x‖ ≤ c)
    (k : ℕ) : ∀ {f : ℝ^2 → ℝ} {R : ℝ}, ContDiffOn ℝ k f H̄ →
      (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) →
      (∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
        ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ M * ‖y - z‖ ^ α) →
      (∀ y, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ k f H̄ y‖ ≤ B) →
      ∫ y in HalfSpace.upper 2, ‖iteratedFDerivWithin ℝ k f H̄ y‖ ≤ L →
      ∀ x : ℝ^2, 0 ≤ x 1 →
        ‖iteratedFDerivWithin ℝ (k + 1) (halfPlaneVelocity f) H̄ x‖ ≤ c + k * B := by
  induction k with
  | zero =>
    intro f R hf hR hM hB hL x hx
    rw [Nat.cast_zero, contDiffOn_zero] at hf
    have h0 : ∀ y, ‖iteratedFDerivWithin ℝ 0 f H̄ y‖ = |f y| := fun y ↦ by
      rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
    rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper x hx), Nat.cast_zero, zero_mul,
      add_zero]
    refine base hf hR (fun y z hy hz ↦ ?_) (fun y hy ↦ by rw [← h0]; exact hB y hy)
      (by simpa only [h0] using hL) x hx
    have := hM y z hy hz
    rwa [PDE.Analysis.norm_iteratedFDerivWithin_zero_sub, Real.norm_eq_abs] at this
  | succ k ih =>
    intro f R hf hR hM hB hL x hx
    rw [Nat.cast_add_one] at hf
    have hf1 : ContDiffOn ℝ 1 f H̄ := hf.of_le le_add_self
    have hg : ContDiffOn ℝ k (PDE.partialDerivWithin 0 f H̄) H̄ :=
      hf.partialDerivWithin 0 uniqueDiffOn_closedUpper le_rfl
    have hgR := partialDerivWithin_eq_zero_of_eq_zero hR 0
    have hug := ih hg hgR
      (fun y z hy hz ↦ (norm_iteratedFDerivWithin_partialDerivWithin_sub_le hf hy hz).trans
        (hM y z hy hz))
      (fun y hy ↦ (norm_iteratedFDerivWithin_partialDerivWithin_le hf hy).trans (hB y hy))
      (setIntegral_norm_iteratedFDerivWithin_partialDerivWithin_le hf hR hL) x hx
    have hf' : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f H̄ := by rwa [Nat.cast_add_one]
    have hreg : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
        (halfPlaneVelocity (PDE.partialDerivWithin 0 f H̄)) H̄ := by
      rw [Nat.cast_add_one]
      exact contDiffOn_succ_halfPlaneVelocity hα hα1 hg hgR fun y z hy hz ↦
        (norm_iteratedFDerivWithin_partialDerivWithin_sub_le hf hy hz).trans (hM y z hy hz)
    rw [← norm_iteratedFDerivWithin_fderivWithin uniqueDiffOn_closedUpper hx,
      iteratedFDerivWithin_fderivWithin_eq hf1 hf' hR hreg hx]
    refine (norm_comp_add_le _ _).trans ?_
    calc _ ≤ (c + k * B) + B := add_le_add hug (hB x hx)
      _ = c + ((k + 1 : ℕ) : ℝ) * B := by push_cast; ring

/-- **Size of the top-order derivative, Hölder form.** For `f` `C^k` within the closed
half-plane and vanishing there outside a disc, with `D^k f` `α`-Hölder on `H̄` with constant `M`,
`‖D^k f‖ ≤ B` on `H̄` and `∫_{ℝ²₊} ‖D^k f‖ ≤ L`, at every point of the closed half-plane
`‖D^{k+1} u(f)(x)‖ ≤ 4(50M/α + 8B + 10L) + kB`. -/
theorem norm_iteratedFDerivWithin_halfPlaneVelocity_le_holder {k : ℕ} {R M B L : ℝ}
    (hf : ContDiffOn ℝ k f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ M * ‖y - z‖ ^ α)
    (hB : ∀ y, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ k f H̄ y‖ ≤ B)
    (hL : ∫ y in HalfSpace.upper 2, ‖iteratedFDerivWithin ℝ k f H̄ y‖ ≤ L)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖iteratedFDerivWithin ℝ (k + 1) (halfPlaneVelocity f) H̄ x‖ ≤
      4 * (50 * M / α + 8 * B + 10 * L) + k * B := by
  refine norm_iteratedFDerivWithin_halfPlaneVelocity_le_of_fderivWithin_le hα hα1
    (fun hf hR hM hB hL x hx ↦ ?_) k hf hR hM hB hL x hx
  refine (norm_fderivWithin_halfPlaneVelocity_le_holder hf hR hα hα1 hM hB hx).trans ?_
  gcongr

/-- **Size of the top-order derivative, Kato form.** Under the hypotheses of
`norm_iteratedFDerivWithin_halfPlaneVelocity_le_holder`, at every point of the closed half-plane
`‖D^{k+1} u(f)(x)‖ ≤ 4((50/α)(1 + B log(2 + M)) + 8B + 10L) + kB`: the Hölder constant enters
only through the logarithm. -/
theorem norm_iteratedFDerivWithin_halfPlaneVelocity_le_kato {k : ℕ} {R M B L : ℝ}
    (hf : ContDiffOn ℝ k f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ M * ‖y - z‖ ^ α)
    (hB : ∀ y, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ k f H̄ y‖ ≤ B)
    (hL : ∫ y in HalfSpace.upper 2, ‖iteratedFDerivWithin ℝ k f H̄ y‖ ≤ L)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖iteratedFDerivWithin ℝ (k + 1) (halfPlaneVelocity f) H̄ x‖ ≤
      4 * (50 / α * (1 + B * Real.log (2 + M)) + 8 * B + 10 * L) + k * B := by
  refine norm_iteratedFDerivWithin_halfPlaneVelocity_le_of_fderivWithin_le hα hα1
    (fun hf hR hM hB hL x hx ↦ ?_) k hf hR hM hB hL x hx
  refine (norm_fderivWithin_halfPlaneVelocity_le_kato hf hR hα hα1 hM hB hx).trans ?_
  gcongr

/-- **Size of the top-order derivative, homogeneous Kato form.** Under the hypotheses of
`norm_iteratedFDerivWithin_halfPlaneVelocity_le_holder` with `0 < B`, at every point of the
closed half-plane `‖D^{k+1} u(f)(x)‖ ≤ 4((50B/α)(1 + log(2 + M/B)) + 8B + 10L) + kB`. The bound
is homogeneous of degree one in `(f, M, B, L)`, so it applies to differences; when the data
vanish, `norm_iteratedFDerivWithin_halfPlaneVelocity_le_holder` with zero constants applies. -/
theorem norm_iteratedFDerivWithin_halfPlaneVelocity_le_kato_homogeneous {k : ℕ} {R M B L : ℝ}
    (hf : ContDiffOn ℝ k f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ M * ‖y - z‖ ^ α)
    (hB : ∀ y, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ k f H̄ y‖ ≤ B) (hB0 : 0 < B)
    (hL : ∫ y in HalfSpace.upper 2, ‖iteratedFDerivWithin ℝ k f H̄ y‖ ≤ L)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖iteratedFDerivWithin ℝ (k + 1) (halfPlaneVelocity f) H̄ x‖ ≤
      4 * (50 * B / α * (1 + Real.log (2 + M / B)) + 8 * B + 10 * L) + k * B := by
  refine norm_iteratedFDerivWithin_halfPlaneVelocity_le_of_fderivWithin_le hα hα1
    (fun hf hR hM hB hL x hx ↦ ?_) k hf hR hM hB hL x hx
  refine (norm_fderivWithin_halfPlaneVelocity_le_kato_homogeneous hf hR hα hα1 hM hB hB0
    hx).trans ?_
  gcongr

end Size

/-- The derivative formula bounds the first derivative of the velocity by the velocity of
`∂₀^H f` and the vorticity. -/
private theorem norm_divFreeDeriv_le (a : ℝ^2) (c : ℝ) : ‖divFreeDeriv a c‖ ≤ ‖a‖ + |c| := by
  refine (norm_add_le _ _).trans (add_le_add (norm_divFreeTangential_apply_le a) ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg c) norm_divFreeVorticity_le

private theorem norm_iteratedFDerivWithin_halfPlaneVelocity_le_of_mem (j : ℕ) :
    ∀ {f : ℝ^2 → ℝ} {R B B' L : ℝ},
    ContDiffOn ℝ (j + 1) f H̄ → (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) →
    (∀ y, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ (j + 1) f H̄ y‖ ≤ B) →
    ∫ y in HalfSpace.upper 2, ‖iteratedFDerivWithin ℝ (j + 1) f H̄ y‖ ≤ L →
    (∀ y, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ j f H̄ y‖ ≤ B') →
    ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖iteratedFDerivWithin ℝ (j + 1) (halfPlaneVelocity f) H̄ x‖ ≤
        B + L / Real.pi + (j + 1) * B' := by
  induction j with
  | zero =>
    intro f R B B' L hf hR hB hL hB' x hx
    rw [Nat.cast_zero, zero_add] at hf
    have hg0 : ∀ y, 0 ≤ y 1 → |PDE.partialDerivWithin 0 f H̄ y| ≤
        ‖iteratedFDerivWithin ℝ 1 f H̄ y‖ := fun y hy ↦ by
      have := norm_iteratedFDerivWithin_partialDerivWithin_le (k := 0) (by simpa using hf) hy
      rwa [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] at this
    have hgL : ∫ y in HalfSpace.upper 2, |PDE.partialDerivWithin 0 f H̄ y| ≤ L := by
      have := setIntegral_norm_iteratedFDerivWithin_partialDerivWithin_le (k := 0)
        (by simpa using hf) hR hL
      simpa only [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] using this
    have hvel := norm_halfPlaneVelocity_le_of_continuousOn
      (hf.partialDerivWithin (m := 0) 0 uniqueDiffOn_closedUpper (by norm_num)).continuousOn
      (partialDerivWithin_eq_zero_of_eq_zero hR 0)
      (fun y hy ↦ (hg0 y (le_of_lt hy)).trans (hB y (le_of_lt hy))) x
    rw [norm_iteratedFDerivWithin_one _ (uniqueDiffOn_closedUpper x hx),
      fderivWithin_halfPlaneVelocity_of_contDiffOn hf hR hx]
    refine (norm_divFreeDeriv_le _ _).trans ?_
    have hfx : |f x| ≤ B' := by
      have := hB' x hx; rwa [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] at this
    have hpi := Real.pi_pos
    have : (∫ y in HalfSpace.upper 2, |PDE.partialDerivWithin 0 f H̄ y|) / Real.pi ≤
        L / Real.pi := by gcongr
    push_cast
    linarith
  | succ j ih =>
    intro f R B B' L hf hR hB hL hB' x hx
    rw [Nat.cast_add_one] at hf
    have hf1 : ContDiffOn ℝ 1 f H̄ := hf.of_le le_add_self
    have hg : ContDiffOn ℝ (j + 1) (PDE.partialDerivWithin 0 f H̄) H̄ :=
      hf.partialDerivWithin 0 uniqueDiffOn_closedUpper le_rfl
    have hgR := partialDerivWithin_eq_zero_of_eq_zero hR 0
    have hf2 : ContDiffOn ℝ (((j + 1 : ℕ) : WithTop ℕ∞) + 1) f H̄ := by
      rw [Nat.cast_add_one]; exact hf
    have hug := ih (f := PDE.partialDerivWithin 0 f H̄) hg hgR
      (fun y hy ↦ (norm_iteratedFDerivWithin_partialDerivWithin_le hf2 hy).trans (hB y hy))
      (setIntegral_norm_iteratedFDerivWithin_partialDerivWithin_le hf2 hR hL)
      (fun y hy ↦ (norm_iteratedFDerivWithin_partialDerivWithin_le
        (hf.of_le le_self_add) hy).trans (hB' y hy)) x hx
    have hf' : ContDiffOn ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f H̄ := by
      rw [Nat.cast_add_one]; exact hf.of_le le_self_add
    have hreg : ContDiffOn ℝ ((j + 1 : ℕ) : WithTop ℕ∞)
        (halfPlaneVelocity (PDE.partialDerivWithin 0 f H̄)) H̄ :=
      contDiffOn_halfPlaneVelocity (by rwa [Nat.cast_add_one]) hgR
    rw [← norm_iteratedFDerivWithin_fderivWithin uniqueDiffOn_closedUpper hx,
      iteratedFDerivWithin_fderivWithin_eq hf1 hf' hR hreg hx]
    refine (norm_comp_add_le _ _).trans ?_
    calc _ ≤ (B + L / Real.pi + (j + 1) * B') + B' := add_le_add hug (hB' x hx)
      _ = B + L / Real.pi + (((j + 1 : ℕ) : ℝ) + 1) * B' := by push_cast; ring

/-! ### The stream function -/

/-- **Sizes of the lower-order derivatives.** For `f` `C^{j+1}` within the closed half-plane and
vanishing there outside a disc, with `‖D^{j+1} f‖ ≤ B` and `‖D^j f‖ ≤ B'` on `H̄` and
`∫_{ℝ²₊} ‖D^{j+1} f‖ ≤ L`, at every point of the closed half-plane
`‖D^{j+1} u(f)(x)‖ ≤ B + L/π + (j + 1) B'`. No Hölder bound is needed below the top order. -/
theorem norm_iteratedFDerivWithin_halfPlaneVelocity_le (j : ℕ) : ∀ {f : ℝ^2 → ℝ} {R B B' L : ℝ},
    ContDiffOn ℝ (j + 1) f H̄ → (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) →
    (∀ y, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ (j + 1) f H̄ y‖ ≤ B) →
    ∫ y in HalfSpace.upper 2, ‖iteratedFDerivWithin ℝ (j + 1) f H̄ y‖ ≤ L →
    (∀ y, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ j f H̄ y‖ ≤ B') →
    ∀ x : ℝ^2,
      ‖iteratedFDerivWithin ℝ (j + 1) (halfPlaneVelocity f) H̄ x‖ ≤
        B + L / Real.pi + (j + 1) * B' := by
  intro f R B B' L hf hR hB hL hB' x
  by_cases hx : 0 ≤ x 1
  · exact norm_iteratedFDerivWithin_halfPlaneVelocity_le_of_mem j hf hR hB hL hB' x hx
  -- Off the closed half-plane the derivative within it is zero, and the bound is nonnegative.
  have hclosed : IsClosed H̄ :=
    isClosed_le continuous_const (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 ↦ ℝ) 1)
  have hnot : x ∉ closure H̄ := by rw [hclosed.closure_eq]; exact hx
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
  have hB'0 : 0 ≤ B' := (norm_nonneg _).trans (hB' 0 (by simp))
  have hL0 : 0 ≤ L := (integral_nonneg fun _ ↦ norm_nonneg _).trans hL
  rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply,
    fderivWithin_zero_of_notMem_closure hnot, map_zero, norm_zero]
  exact add_nonneg (add_nonneg hB0 (div_nonneg hL0 Real.pi_pos.le))
    (mul_nonneg (by positivity) hB'0)

/-- For `f` `C^m` within the closed half-plane and vanishing there outside a disc, the Green
stream is `C^{m+1}` within the closed half-plane. -/
theorem contDiffOn_halfSpaceGreenPotential {m : ℕ} {R : ℝ} (hf : ContDiffOn ℝ m f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) :
    ContDiffOn ℝ (m + 1) (halfSpaceGreenPotential f) H̄ :=
  contDiffOn_succ_halfSpaceGreenPotential hf.continuousOn hR (contDiffOn_halfPlaneVelocity hf hR)

/-- For `f` `C^k` within the closed half-plane, vanishing there outside a disc, with `D^k f`
`α`-Hölder on the closed half-plane (`0 < α < 1`), the Green stream is `C^{k+2}` within the closed
half-plane. -/
theorem contDiffOn_succ_succ_halfSpaceGreenPotential {k : ℕ} {R M α : ℝ} (hα : 0 < α)
    (hα1 : α < 1) (hf : ContDiffOn ℝ k f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ M * ‖y - z‖ ^ α) :
    ContDiffOn ℝ (k + 2) (halfSpaceGreenPotential f) H̄ := by
  have h := contDiffOn_succ_halfSpaceGreenPotential (m := k + 1) hf.continuousOn hR
    (by rw [Nat.cast_add_one]; exact contDiffOn_succ_halfPlaneVelocity hα hα1 hf hR hM)
  rw [Nat.cast_add_one, add_assoc, one_add_one_eq_two] at h
  exact h

/-! ### Log-Lipschitz derivative for `C¹` data -/

/-- **The derivative of the velocity is log-Lipschitz for `C¹` data.** For `f` `C¹` within the
closed half-plane and vanishing there outside a disc, with `‖D f‖ ≤ B` on `H̄` and
`∫_{ℝ²₊} ‖D f‖ ≤ L`, for `x, x'` in the closed half-plane
`‖D u(x) - D u(x')‖ ≤ |x - x'| (11B + 4L + 4B log⁺(1/|x - x'|))`. -/
theorem dist_fderivWithin_halfPlaneVelocity_le_log {R B L : ℝ} (hf : ContDiffOn ℝ 1 f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hB : ∀ y, 0 ≤ y 1 → ‖fderivWithin ℝ f H̄ y‖ ≤ B)
    (hL : ∫ y in HalfSpace.upper 2, ‖fderivWithin ℝ f H̄ y‖ ≤ L) {x x' : ℝ^2} (hx : 0 ≤ x 1)
    (hx' : 0 ≤ x' 1) :
    dist (fderivWithin ℝ (halfPlaneVelocity f) H̄ x)
        (fderivWithin ℝ (halfPlaneVelocity f) H̄ x') ≤
      ‖x - x'‖ * (11 * B + 4 * L + 4 * B * Real.posLog (1 / ‖x - x'‖)) := by
  set g := PDE.partialDerivWithin 0 f H̄ with hgdef
  have hgc : ContinuousOn g H̄ :=
    (hf.partialDerivWithin (m := 0) 0 uniqueDiffOn_closedUpper (by norm_num)).continuousOn
  have hgR := partialDerivWithin_eq_zero_of_eq_zero hR 0
  have hgB : ∀ y, 0 ≤ y 1 → |g y| ≤ B := fun y hy ↦ by
    refine le_trans ?_ (hB y hy)
    rw [← Real.norm_eq_abs, hgdef, PDE.partialDerivWithin]
    simpa using (fderivWithin ℝ f H̄ y).le_opNorm (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
  have hint : IntegrableOn (fun y ↦ ‖fderivWithin ℝ f H̄ y‖) (HalfSpace.upper 2) :=
    integrableOn_upper_of_continuousOn
      ((hf.continuousOn_fderivWithin uniqueDiffOn_closedUpper le_rfl).norm)
      fun y hy hyR ↦ by rw [fderivWithin_eq_zero_of_eq_zero hR hy hyR, norm_zero]
  have hgL : ∫ y in HalfSpace.upper 2, |g y| ≤ L := by
    refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun y ↦ abs_nonneg _) hint ?_)
      hL
    filter_upwards [ae_restrict_mem (HalfSpace.measurableSet_upper (n := 2))] with y hy
    rw [← Real.norm_eq_abs, hgdef, PDE.partialDerivWithin]
    simpa using (fderivWithin ℝ f H̄ y).le_opNorm (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
  -- the velocity of `∂₀^H f` is log-Lipschitz
  have hEc : Continuous (evenReflection g) :=
    continuous_evenReflection hgc
  have hEcs : HasCompactSupport (evenReflection g) :=
    hasCompactSupport_evenReflection_of_eq_zero hgR
  have hEB : ∀ y ∈ HalfSpace.upper 2, |evenReflection g y| ≤ B := fun y hy ↦ by
    rw [evenReflection_of_nonneg (le_of_lt hy)]; exact hgB y (le_of_lt hy)
  have hEL : ∫ y in HalfSpace.upper 2, |evenReflection g y| =
      ∫ y in HalfSpace.upper 2, |g y| :=
    setIntegral_congr_fun (HalfSpace.measurableSet_upper (n := 2))
      fun y hy ↦ by rw [evenReflection_of_nonneg (le_of_lt hy)]
  have hk : ∀ k : Fin 2, |halfPlaneVelocity g x k - halfPlaneVelocity g x' k| ≤
      ‖x - x'‖ * (5 * B + 2 * L + 2 * B * Real.posLog (1 / ‖x - x'‖)) := by
    intro k
    have h := abs_halfPlaneVelocity_sub_le hEc hEcs hEB k x x'
    rw [halfPlaneVelocity_evenReflection, hEL] at h
    refine h.trans ?_
    gcongr
  -- the vorticity is Lipschitz on the closed half-plane
  have hconv : Convex ℝ H̄ :=
    convex_halfSpace_ge (f := fun y : ℝ^2 ↦ y 1) ⟨fun _ _ ↦ by simp, fun _ _ ↦ by simp⟩ 0
  have hfx : |f x - f x'| ≤ B * ‖x - x'‖ := by
    have := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun w hw ↦ ((hf.differentiableOn one_ne_zero) w hw).hasFDerivWithinAt) hB hx' hx
    rwa [Real.norm_eq_abs] at this
  rw [dist_eq_norm, fderivWithin_halfPlaneVelocity_of_contDiffOn hf hR hx,
    fderivWithin_halfPlaneVelocity_of_contDiffOn hf hR hx']
  have hsub : divFreeDeriv (halfPlaneVelocity g x) (f x) -
      divFreeDeriv (halfPlaneVelocity g x') (f x') =
      divFreeDeriv (halfPlaneVelocity g x - halfPlaneVelocity g x') (f x - f x') := by
    ext1 v
    rw [sub_apply, divFreeDeriv_apply, divFreeDeriv_apply, divFreeDeriv_apply]
    ext i; fin_cases i <;> simp <;> ring
  rw [hsub]
  refine (norm_divFreeDeriv_le _ _).trans ?_
  have hn :=
    EuclideanSpace.norm_le_abs_add_abs_fin_two (halfPlaneVelocity g x - halfPlaneVelocity g x')
  simp only [PiLp.sub_apply] at hn
  have h0 := hk 0
  have h1 := hk 1
  nlinarith [norm_nonneg (x - x')]

/-! ### Components and the full `C^{k+1,α}` bound -/

/-- The derivatives within the closed half-plane of a velocity component are components of those
of the velocity, so every bound above holds for each component: sizes. -/
theorem norm_iteratedFDerivWithin_halfPlaneVelocity_apply_le {m : ℕ}
    (hu : ContDiffOn ℝ m (halfPlaneVelocity f) H̄) (k : Fin 2) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖iteratedFDerivWithin ℝ m (fun y ↦ halfPlaneVelocity f y k) H̄ x‖ ≤
      ‖iteratedFDerivWithin ℝ m (halfPlaneVelocity f) H̄ x‖ := by
  have h := (EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ).iteratedFDerivWithin_comp_left (hu x hx)
    uniqueDiffOn_closedUpper hx le_rfl
  change ‖iteratedFDerivWithin ℝ m ((EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ) ∘
    halfPlaneVelocity f) H̄ x‖ ≤ _
  rw [h]
  exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (PiLp.norm_proj_le k))

/-- The derivatives within the closed half-plane of a velocity component are components of those
of the velocity: differences between two points. -/
theorem norm_iteratedFDerivWithin_halfPlaneVelocity_apply_sub_le {m : ℕ}
    (hu : ContDiffOn ℝ m (halfPlaneVelocity f) H̄) (k : Fin 2) {x x' : ℝ^2} (hx : 0 ≤ x 1)
    (hx' : 0 ≤ x' 1) :
    ‖iteratedFDerivWithin ℝ m (fun y ↦ halfPlaneVelocity f y k) H̄ x -
        iteratedFDerivWithin ℝ m (fun y ↦ halfPlaneVelocity f y k) H̄ x'‖ ≤
      ‖iteratedFDerivWithin ℝ m (halfPlaneVelocity f) H̄ x -
        iteratedFDerivWithin ℝ m (halfPlaneVelocity f) H̄ x'‖ := by
  set P := (EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ)
  change ‖iteratedFDerivWithin ℝ m (P ∘ halfPlaneVelocity f) H̄ x -
    iteratedFDerivWithin ℝ m (P ∘ halfPlaneVelocity f) H̄ x'‖ ≤ _
  rw [P.iteratedFDerivWithin_comp_left (hu x hx) uniqueDiffOn_closedUpper hx le_rfl,
    P.iteratedFDerivWithin_comp_left (hu x' hx') uniqueDiffOn_closedUpper hx' le_rfl]
  have e : P.compContinuousMultilinearMap (iteratedFDerivWithin ℝ m (halfPlaneVelocity f) H̄ x) -
      P.compContinuousMultilinearMap (iteratedFDerivWithin ℝ m (halfPlaneVelocity f) H̄ x') =
      P.compContinuousMultilinearMap (iteratedFDerivWithin ℝ m (halfPlaneVelocity f) H̄ x -
        iteratedFDerivWithin ℝ m (halfPlaneVelocity f) H̄ x') := by
    ext v; simp
  rw [e]
  exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (PiLp.norm_proj_le k))

/-- The mass on the open half-plane of a function bounded by `N` on the closed half-plane and
vanishing there outside the disc of radius `R` is at most `πR² N`. -/
theorem setIntegral_upper_le {h : ℝ^2 → ℝ} {R N : ℝ} (hR0 : 0 ≤ R)
    (hh : ContinuousOn h H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → h y = 0)
    (hN : ∀ y, 0 ≤ y 1 → h y ≤ N) (hh0 : ∀ y, 0 ≤ h y) :
    ∫ y in HalfSpace.upper 2, h y ≤ Real.pi * R ^ 2 * N := by
  have hN0 : 0 ≤ N := (hh0 0).trans (hN 0 (by simp))
  have hle : ∀ y ∈ HalfSpace.upper 2, h y ≤ (closedBall (0 : ℝ^2) R).indicator (fun _ ↦ N) y := by
    intro y hy
    by_cases hyR : y ∈ closedBall (0 : ℝ^2) R
    · rw [indicator_of_mem hyR]; exact hN y (le_of_lt hy)
    · rw [indicator_of_notMem hyR]
      rw [mem_closedBall, dist_zero_right, not_le] at hyR
      rw [hR y (le_of_lt hy) hyR]
  have hind : Integrable ((closedBall (0 : ℝ^2) R).indicator fun _ ↦ N) :=
    (integrableOn_const (C := N) measure_closedBall_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  have hvol : volume.real (closedBall (0 : ℝ^2) R) = Real.pi * R ^ 2 := by
    rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hR0, ENNReal.toReal_ofReal Real.pi_pos.le]
    ring
  calc ∫ y in HalfSpace.upper 2, h y
      ≤ ∫ y in HalfSpace.upper 2, (closedBall (0 : ℝ^2) R).indicator (fun _ ↦ N) y :=
        setIntegral_mono_on (integrableOn_upper_of_continuousOn hh hR) hind.integrableOn
          (HalfSpace.measurableSet_upper (n := 2)) hle
    _ ≤ ∫ y, (closedBall (0 : ℝ^2) R).indicator (fun _ ↦ N) y :=
        setIntegral_le_integral hind (Eventually.of_forall fun y ↦ by
          by_cases hy : y ∈ closedBall (0 : ℝ^2) R <;> simp [hy, hN0])
    _ = Real.pi * R ^ 2 * N := by
        rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul, hvol]

/-- **The `C^{k+1,α}` bound of the velocity.** For `f` `C^k` within the closed half-plane,
vanishing there outside the disc of radius `R`, with `‖D^j f‖ ≤ N` on the closed half-plane for
`j ≤ k` and `D^k f` `α`-Hölder there with constant `N` (`0 < α < 1`), every derivative of order
`j ≤ k + 1` of the velocity is bounded on the closed half-plane by `C N`,
`C = 200/α + 40π(1 + R²) + k + 33`; with
`norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le` this bounds the `C^{k+1,α}` norm of `u(f)`
linearly by the `C^{k,α}` norm of `f`, so by linearity
(`iteratedFDerivWithin_halfPlaneVelocity_sub`) it also bounds differences. -/
theorem norm_iteratedFDerivWithin_halfPlaneVelocity_le_mul {k : ℕ} {R N α : ℝ} (hα : 0 < α)
    (hα1 : α < 1) (hR0 : 0 ≤ R) (hf : ContDiffOn ℝ k f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hN : ∀ j ≤ k, ∀ y, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ j f H̄ y‖ ≤ N)
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ N * ‖y - z‖ ^ α)
    {j : ℕ} (hj : j ≤ k + 1) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖iteratedFDerivWithin ℝ j (halfPlaneVelocity f) H̄ x‖ ≤
      (200 / α + 40 * Real.pi * (1 + R ^ 2) + k + 33) * N := by
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (Nat.zero_le _) 0 (by simp))
  have hpi := Real.pi_gt_three
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  have hA : (1 + R ^ 2) * N ≤ 40 * Real.pi * (1 + R ^ 2) * N :=
    mul_le_mul_of_nonneg_right (by nlinarith) hN0
  have hαN : 0 ≤ 200 / α * N := mul_nonneg (by positivity) hN0
  have hkN : 0 ≤ (k : ℝ) * N := mul_nonneg (Nat.cast_nonneg k) hN0
  have hCN : (200 / α + 40 * Real.pi * (1 + R ^ 2) + k + 33) * N =
      200 / α * N + 40 * Real.pi * (1 + R ^ 2) * N + k * N + 33 * N := by ring
  have hmass : ∀ i ≤ k, ∫ y in HalfSpace.upper 2, ‖iteratedFDerivWithin ℝ i f H̄ y‖ ≤
      Real.pi * R ^ 2 * N := fun i hi ↦
    setIntegral_upper_le hR0
      ((hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi) uniqueDiffOn_closedUpper).norm)
      (fun y hy hyR ↦ by rw [iteratedFDerivWithin_eq_zero_of_eq_zero hR i hy hyR, norm_zero])
      (hN i hi) fun y ↦ norm_nonneg _
  have hC : 0 ≤ 200 / α + 40 * Real.pi * (1 + R ^ 2) + k + 33 := by positivity
  rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
  · cases j with
    | zero =>
      rw [norm_iteratedFDerivWithin_zero]
      have hB : ∀ y ∈ HalfSpace.upper 2, |f y| ≤ N := fun y hy ↦ by
        have := hN 0 (Nat.zero_le _) y (le_of_lt hy)
        rwa [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] at this
      have hL : ∫ y in HalfSpace.upper 2, |f y| ≤ Real.pi * R ^ 2 * N := by
        have := hmass 0 (Nat.zero_le _)
        simpa only [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] using this
      refine (norm_halfPlaneVelocity_le_of_continuousOn hf.continuousOn hR hB x).trans ?_
      have : (∫ y in HalfSpace.upper 2, |f y|) / Real.pi ≤ R ^ 2 * N := by
        rw [div_le_iff₀ Real.pi_pos]; linarith
      rw [hCN]
      linarith
    | succ i =>
      have hik : i + 1 ≤ k := by omega
      have hfi : ContDiffOn ℝ (i + 1) f H̄ := hf.of_le (by exact_mod_cast hik)
      have h := norm_iteratedFDerivWithin_halfPlaneVelocity_le i hfi hR (hN (i + 1) hik)
        (hmass (i + 1) hik) (hN i (by omega)) x
      have hik' : ((i : ℝ) + 1) ≤ k := by exact_mod_cast hik
      calc _ ≤ N + Real.pi * R ^ 2 * N / Real.pi + (i + 1) * N := h
        _ ≤ (200 / α + 40 * Real.pi * (1 + R ^ 2) + k + 33) * N := by
            rw [show Real.pi * R ^ 2 * N / Real.pi = R ^ 2 * N by field_simp, hCN]
            have hiN : ((i : ℝ) + 1) * N ≤ k * N := mul_le_mul_of_nonneg_right hik' hN0
            linarith
  · have hjk' : j = k + 1 := by omega
    subst hjk'
    have h := norm_iteratedFDerivWithin_halfPlaneVelocity_le_holder hα hα1 hf hR hM (hN k le_rfl)
      (hmass k le_rfl) hx
    calc _ ≤ 4 * (50 * N / α + 8 * N + 10 * (Real.pi * R ^ 2 * N)) + k * N := h
      _ ≤ (200 / α + 40 * Real.pi * (1 + R ^ 2) + k + 33) * N := by
          have h1 : 4 * (50 * N / α) = 200 / α * N := by ring
          rw [hCN]
          nlinarith

/-! ### Global data -/

/-- **The `C^{k+1,α}` estimate for global `C^{k,α}` data.** For a compactly supported
`f ∈ C^k(ℝ²)` whose `k`-th derivative is `α`-Hölder with constant `C` (`0 < α < 1`), the velocity
is `C^{k+1}` within the closed half-plane and its `(k+1)`-st derivative within the closed
half-plane is `α`-Hölder there with constant `(844/(α(1-α)) + k) C`. -/
theorem holderOnWith_iteratedFDerivWithin_halfPlaneVelocity {k : ℕ} {α C : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) (hf : ContDiff ℝ k f) (hc : HasCompactSupport f)
    (hC : HolderWith C α (iteratedFDeriv ℝ k f)) :
    ContDiffOn ℝ (k + 1) (halfPlaneVelocity f) H̄ ∧
      HolderOnWith (Real.toNNReal (844 / (α * (1 - α)) + k) * C) α
        (iteratedFDerivWithin ℝ (k + 1) (halfPlaneVelocity f) H̄) H̄ := by
  have hα' : (0 : ℝ) < α := hα
  have hα1' : (α : ℝ) < 1 := hα1
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hR' : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0 := fun y _ hy ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ by
      have := hR h; rw [mem_closedBall, dist_zero_right] at this; linarith
  have hD : ∀ y : ℝ^2, 0 ≤ y 1 → iteratedFDerivWithin ℝ k f H̄ y = iteratedFDeriv ℝ k f y :=
    fun y hy ↦ iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_closedUpper hf.contDiffAt hy
  have hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤
        (C : ℝ) * ‖y - z‖ ^ (α : ℝ) := fun y z hy hz ↦ by
    rw [hD y hy, hD z hz, ← dist_eq_norm, ← dist_eq_norm]
    exact hC.dist_le y z
  refine ⟨contDiffOn_succ_halfPlaneVelocity hα' hα1' hf.contDiffOn hR' hM, ?_⟩
  intro x hx x' hx'
  have hpos : 0 ≤ 844 / ((α : ℝ) * (1 - α)) + k := by
    have : 0 < (α : ℝ) * (1 - α) := mul_pos hα' (by linarith)
    positivity
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
    ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _ hpos]
  have := norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le hα' hα1' hf.contDiffOn hR' hM hx hx'
  linarith

end IncompressibleFlow
