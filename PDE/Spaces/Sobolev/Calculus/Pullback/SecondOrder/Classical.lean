/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import PDE.FDeriv.Calculus
import PDE.Spaces.Sobolev.Approximation.Density.ClassicalDerivatives
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability

/-!
# Classical second-order pullback calculus

We prove the pointwise second-order chain rule for scalar pullbacks and
identify the resulting expression as a weak derivative for smooth data.
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory Set Function ENNReal
open SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The `(i,k)` second derivative row of the scalar pullback `u ∘ Φ`, written
in terms of derivatives of `u` and of the chart `Φ`. -/
def secondPullbackRow
    (i k : Fin n) (u : ℝ^n → ℝ) (Φ : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ :=
  (∑ j : Fin n, ∑ l : Fin n,
    (∂[l]
        (fun z ↦ (∂[j] u) z)) (Φ x) *
      (∂[i] (fun y ↦ Φ y l)) x *
      (∂[k] (fun y ↦ Φ y j)) x) +
  ∑ j : Fin n,
    (∂[j] u) (Φ x) *
      (∂[i]
        (fun y ↦ (∂[k] (fun z ↦ Φ z j)) y)) x

/-- Pointwise semantics of `secondPullbackRow` for `C²` data. -/
theorem secondPullbackRow_eq
    (i k : Fin n) (u : ℝ^n → ℝ) (Φ : ℝ^n → ℝ^n) (x : ℝ^n)
    (hu : ContDiff ℝ 2 u) (hΦ : ContDiff ℝ 2 Φ) :
    (∂[i]
        (fun y ↦ (∂[k] (fun z ↦ u (Φ z))) y)) x =
      secondPullbackRow i k u Φ x := by
  exact PDE.partialDeriv_partialDeriv_comp (n := n) i k u Φ x hu hΦ

/-- For `C²` data, every explicit second-order pullback row is continuous. -/
theorem continuous_secondPullbackRow
    (i k : Fin n) (u : ℝ^n → ℝ) (Φ : ℝ^n → ℝ^n)
    (hu : ContDiff ℝ 2 u) (hΦ : ContDiff ℝ 2 Φ) :
    Continuous (secondPullbackRow i k u Φ) := by
  let w : ℝ^n → ℝ := fun x ↦ u (Φ x)
  have hw : ContDiff ℝ 2 w := hu.comp hΦ
  have hDk : ContDiff ℝ 1
      (fun y ↦ (∂[k] w) y) := by
    have hfd : ContDiff ℝ 1 (fderiv ℝ w) := hw.fderiv_right (by norm_num)
    simpa [partialDeriv, partialDeriv] using
      hfd.clm_apply (contDiff_const : ContDiff ℝ 1
        (fun _ : ℝ^n ↦ EuclideanSpace.single k (1 : ℝ)))
  have hDiDk : ContDiff ℝ 0
      (fun x ↦ (∂[i]
        (fun y ↦ (∂[k] w) y)) x) := by
    have hfd : ContDiff ℝ 0
        (fderiv ℝ (fun y ↦ (∂[k] w) y)) :=
      hDk.fderiv_right (by norm_num)
    simpa [partialDeriv, partialDeriv] using
      hfd.clm_apply (contDiff_const : ContDiff ℝ 0
        (fun _ : ℝ^n ↦ EuclideanSpace.single i (1 : ℝ)))
  have heq :
      (fun x ↦ (∂[i]
        (fun y ↦ (∂[k] w) y)) x) =
        secondPullbackRow i k u Φ := by
    funext x
    exact secondPullbackRow_eq (n := n) i k u Φ x hu hΦ
  rw [← heq]
  exact hDiDk.continuous

/-- A second-order pullback row of `C²` data is an `L²` function on every
compact chart patch. -/
theorem memLp_secondPullbackRow_on_compact
    {K : Set (ℝ^n)} (hK : IsCompact K)
    (i k : Fin n) (u : ℝ^n → ℝ) (Φ : ℝ^n → ℝ^n)
    (hu : ContDiff ℝ 2 u) (hΦ : ContDiff ℝ 2 Φ) :
    MemLp (secondPullbackRow i k u Φ) 2 (domainMeasure n K) :=
  memLp_on_compact_of_continuous (n := n) (p := (2 : ENNReal)) hK
    (continuous_secondPullbackRow (n := n) i k u Φ hu hΦ)

/-- The explicit second-order pullback row is the weak derivative of
`u ∘ Φ` on every set. This is the weak-calculus bridge used before
transporting elliptic equations to flattened boundary coordinates. -/
theorem hasWeakDerivativeOn_secondPullbackRow
    (i k : Fin n) (u : ℝ^n → ℝ) (Φ : ℝ^n → ℝ^n)
    (hu : ContDiff ℝ 2 u) (hΦ : ContDiff ℝ 2 Φ) :
    HasWeakDerivativeOn (n := n) Ω [i, k] (fun x ↦ u (Φ x))
      (secondPullbackRow i k u Φ) := by
  have hcomp : ContDiff ℝ 2 (fun x ↦ u (Φ x)) := hu.comp hΦ
  have hweak := SobolevSpace.GraphSpace.hasWeakDerivativeOn_iteratedPartialDeriv_finite
    (n := n) (Ω := Ω) [i, k] hcomp
  apply (SobolevSpace.hasWeakDerivativeOn_congr_ae
    (n := n) (Ω := Ω) (α := [i, k])
    (Filter.Eventually.of_forall fun _ ↦ rfl) ?_).1 hweak
  filter_upwards with x
  simpa [iteratedPartialDeriv, secondPullbackRow,
    partialDeriv] using
      PDE.partialDeriv_partialDeriv_comp (n := n) i k u Φ x hu hΦ


end SobolevSpace.WeakChangeOfVariables
