/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Mollification.Monotone
public import PDE.Analysis.Integration.PrimitiveConvergence
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Smooth convex approximation of scalar entropy pairs

For a smooth characteristic speed, every convex C¹ entropy pair is a locally uniform
limit of smooth convex compatible pairs. We mollify the monotone entropy derivative,
then integrate it and its product with the speed. Both primitives retain their values
at the origin. `SmoothTesting` uses this to pass from the smooth entropy pairs (36)-(37) of
Evans, §11.4.3, to `C¹` pairs.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, definition of entropy/entropy-flux pair,
  equations (36)-(38).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ContDiff

namespace PDE.Hyperbolic.ConservationLaw.Scalar

open PDE.Analysis.Calculus

private theorem locallyUniform_const_family (f : ℝ → ℝ) :
    TendstoLocallyUniformly (fun _ : ℕ ↦ f) f atTop :=
  (show TendstoUniformly (fun _ : ℕ ↦ f) f atTop from
    fun _ hV ↦ Eventually.of_forall fun _ _ ↦ refl_mem_uniformity hV).tendstoLocallyUniformly

private theorem hasDerivAt_normalized_primitive {g : ℝ → ℝ} (hg : Continuous g) (c x : ℝ) :
    HasDerivAt (fun r ↦ c + ∫ s in (0 : ℝ)..r, g s) (g x) x := by
  simpa using (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 x)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add c

private theorem contDiff_normalized_primitive {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (c : ℝ) :
    ContDiff ℝ ∞ (fun r ↦ c + ∫ s in (0 : ℝ)..r, g s) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x ↦ (hasDerivAt_normalized_primitive hg.continuous c x).differentiableAt, ?_⟩
  simpa only [funext (fun x ↦ (hasDerivAt_normalized_primitive hg.continuous c x).deriv)] using hg

/-- A convex C¹ entropy pair for a smooth speed has smooth convex compatible approximants.
Both components converge uniformly on every compact state set. -/
theorem EntropyPair.exists_smooth_convex_approximation {a : ℝ → ℝ} (E : EntropyPair a)
    (ha : ContDiff ℝ ∞ a) (hconvex : ConvexOn ℝ univ E.η) :
    ∃ A : ℕ → EntropyPair a, (∀ j, ContDiff ℝ ∞ (A j).η ∧ ContDiff ℝ ∞ (A j).q ∧
      ConvexOn ℝ univ (A j).η) ∧ TendstoLocallyUniformly (fun j ↦ (A j).η) E.η atTop ∧
      TendstoLocallyUniformly (fun j ↦ (A j).q) E.q atTop := by
  let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hεpos : ∀ j, 0 < ε j := fun j ↦
    one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_one)
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun j ↦
    ⟨ε j / 2, ε j, half_pos (hεpos j), half_lt_self (hεpos j)⟩
  let g : ℕ → ℝ → ℝ := fun j ↦ realMollify (φ j) (deriv E.η)
  have hg (j : ℕ) : ContDiff ℝ ∞ (g j) :=
    contDiff_realMollify (φ j) E.eta_contDiff.continuous_deriv_one
  have hmono (j : ℕ) : Monotone (g j) :=
    monotone_realMollify (φ j) E.eta_contDiff.continuous_deriv_one
      (fun x y hxy ↦ hconvex.monotoneOn_deriv
        (fun z _ ↦ E.eta_contDiff.differentiable_one z) (mem_univ x) (mem_univ y) hxy)
  let η : ℕ → ℝ → ℝ := fun j r ↦ E.η 0 + ∫ s in (0 : ℝ)..r, g j s
  let q : ℕ → ℝ → ℝ := fun j r ↦ E.q 0 + ∫ s in (0 : ℝ)..r, g j s * a s
  have hη (j : ℕ) : ContDiff ℝ ∞ (η j) := contDiff_normalized_primitive (hg j) _
  have hq (j : ℕ) : ContDiff ℝ ∞ (q j) := contDiff_normalized_primitive ((hg j).mul ha) _
  have hηder (j : ℕ) : deriv (η j) = g j :=
    funext fun x ↦ (hasDerivAt_normalized_primitive (hg j).continuous _ x).deriv
  have hqder (j : ℕ) : deriv (q j) = fun x ↦ g j x * a x := funext fun x ↦
      (hasDerivAt_normalized_primitive ((hg j).continuous.mul ha.continuous) _ x).deriv
  let A : ℕ → EntropyPair a := fun j ↦
    { η := η j
      q := q j
      eta_contDiff := (hη j).of_le (by simp)
      entropyFlux_contDiff := (hq j).of_le (by simp)
      hq := fun x ↦ by rw [hηder, hqder] }
  have hlim : TendstoLocallyUniformly g (deriv E.η) atTop :=
    realMollify_tendstoLocallyUniformly tendsto_one_div_add_atTop_nhds_zero_nat
      E.eta_contDiff.continuous_deriv_one
  have hfluxlim : TendstoLocallyUniformly (fun j x ↦ g j x * a x)
      (fun x ↦ deriv E.η x * a x) atTop := hlim.mul₀ (locallyUniform_const_family a)
      E.eta_contDiff.continuous_deriv_one ha.continuous
  have hetaEq : (fun r ↦ E.η 0 + ∫ s in (0 : ℝ)..r, deriv E.η s) = E.η := by
    funext r
    rw [intervalIntegral.integral_deriv_of_contDiffOn_uIcc E.eta_contDiff.contDiffOn]
    abel
  have hfluxEq : (fun r ↦ E.q 0 + ∫ s in (0 : ℝ)..r, deriv E.η s * a s) = E.q := by
    funext r
    simp_rw [← E.hq]
    rw [intervalIntegral.integral_deriv_of_contDiffOn_uIcc E.entropyFlux_contDiff.contDiffOn]
    abel
  refine ⟨A, ?_, ?_, ?_⟩
  · intro j
    refine ⟨hη j, hq j, Monotone.convexOn_univ_of_deriv ((hη j).differentiable (by simp)) ?_⟩
    change Monotone (deriv (η j))
    simpa only [hηder] using hmono j
  · have hl := (locallyUniform_const_family (fun _ ↦ E.η 0)).add
      (hlim.intervalIntegral (fun j ↦ (hg j).continuous) 0)
    change TendstoLocallyUniformly η (fun r ↦ E.η 0 + ∫ s in (0 : ℝ)..r, deriv E.η s) atTop at hl
    simpa only [hetaEq] using hl
  · have hl := (locallyUniform_const_family (fun _ ↦ E.q 0)).add
      (hfluxlim.intervalIntegral (fun j ↦ (hg j).continuous.mul ha.continuous) 0)
    change TendstoLocallyUniformly q
      (fun r ↦ E.q 0 + ∫ s in (0 : ℝ)..r, deriv E.η s * a s) atTop at hl
    simpa only [hfluxEq] using hl

end PDE.Hyperbolic.ConservationLaw.Scalar
