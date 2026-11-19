/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Operators
public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.ExtensionByZero
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.CompactSupportTranslation
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.CoefficientCommutator
public import PDE.Spaces.Sobolev.Localization.Cutoff.ZeroBoundary -- shake: keep

/-!
# Localized difference quotients

Localized difference fields and backward-quotient test functions for the interior elliptic
regularity argument in Evans, PDE, §6.3.1. There one tests the weak form of a divergence-form
equation on `Ω` against

`v = -Dᵢ⁻ʰ(η² Dᵢʰ u)`,

where `η` is a smooth cutoff compactly supported in `Ω` and `Dᵢ^{±h}` are the forward and
backward difference quotients in direction `eᵢ`. We build that test function as an
element of `H¹₀(Ω)`: `u` is extended by zero to `ℝ^n`, differenced, restricted back to `Ω`, and
multiplied by `η²`. Compact support of `η` in `Ω` is what keeps the localized field in `H¹₀(Ω)`;
for the backward quotient one also needs the translated support to stay a positive distance
(a collar) inside `Ω`, which holds uniformly for all sufficiently small `|h|`.

We also record the `L²` estimates for the cutoff: `Dᵢ(η²) = 2η Dᵢη` as a multiplier,
the resulting quantitative bounds, and the Young-absorbed estimates for pairing a coefficient
against the cutoff-derivative error terms.

## Main results

* `restrict_differenceQuotientH1_zeroExtend_mem_H10`: a difference quotient of a zero-extended
  `H¹₀(Ω)` field, restricted to `Ω`, is again in `H¹₀(Ω)` under the collar hypothesis.
* `squaredCutoff`, `partialSquaredCutoff_smul`, `norm_partialSquaredCutoff_smul_le`,
  `norm_squaredCutoff_smul_le`: the squared cutoff and its `L²` multiplier estimates.
* `abs_inner_lpSMul_partialSquaredCutoff_le_young`, `abs_inner_lpSMul_squaredCutoff_le`: the
  cutoff error terms in the energy identity, in absorbed form.
* `localizedDifferenceH10`: the forward field `η² Dᵢʰ(E₀u)` in `H¹₀(Ω)`, with its coordinate
  formula `localizedDifferenceH10_coordinate`.
* `exists_uniform_shiftedSupport_collar`, `collarStep`: a uniform collar for small steps and a
  canonical sequence of steps `ρ/(m+1) → 0` inside it.
* `backwardLocalizedDifferenceH10`: the full test `-Dᵢ⁻ʰ(η² Dᵢʰ(E₀u))` in `H¹₀(Ω)`, with
  `backwardLocalizedDifferenceH10_coordinate`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 1, pp. 327-331: the cutoff of step 1 of the
  proof and the test function (11) of step 3, p. 328, and the estimate of `A₂` in step 4, p. 330,
  where the terms carrying a derivative of the cutoff are absorbed by Cauchy's inequality with `ε`.
  Evans allows any `u ∈ H¹(U)` (Remark (i), p. 328); we take `u ∈ H¹₀(Ω)`, so that `u` can be
  extended by zero before it is differenced.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open MeasureTheory Set Function
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace Sobolev
open SobolevSpace.GraphSpace.Rellich

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A difference quotient of a zero-boundary field remains zero-boundary
after restriction, provided the translated compact representative stays a
positive distance inside the domain.  The proof is the linear combination
`h⁻¹(T_h E₀u - E₀u)` together with the translated compact-support theorem. -/
theorem restrict_differenceQuotientH1_zeroExtend_mem_H10
    (hΩopen : IsOpen Ω) (μ : Approximation.Mollifier n)
    (i : Fin n) (h : ℝ) (u : H¹₀(Ω))
    (f : ℝ^n → ℝ)
    (hbase :
      (((((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet u :
          H¹(ℝ^n)) : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
            DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume] f)
    (hfcs : HasCompactSupport f)
    {R δ : ℝ} (hRnonneg : 0 ≤ R) (hδ : 0 < δ)
    (hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R)
    (hcollar : Metric.cthickening δ
      (tsupport (fun x ↦ f (x + coordinateStep i h))) ⊆ Ω) :
    restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
        (subset_univ Ω)
        (differenceQuotientH1 i h
          (ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
            hΩopen.measurableSet u)) ∈
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  have htrans := restrict_translateH1_mem_H10_of_compactSupport_collar hΩopen μ
    (coordinateStep i h)
    (ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet u)
    f hbase hfcs hRnonneg hδ hR hcollar
  have hzero := ZeroTrace.restrict_zeroExtendH10 (n := n) (Ω := Ω) hΩopen u
  rw [differenceQuotientH1_apply, map_smul, map_sub, hzero]
  exact (h10SubmoduleOn (n := n) (Ω := Ω)).smul_mem
    _ ((h10SubmoduleOn (n := n) (Ω := Ω)).sub_mem
      htrans u.property)

/-- The squared cutoff as a smooth test function. -/
noncomputable def squaredCutoff (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
  TestFunction.mul η η

/-- Squaring a cutoff does not enlarge its topological support. -/
theorem tsupport_squaredCutoff_subset (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    tsupport (squaredCutoff η).toFun ⊆ tsupport η.toFun := by
  change tsupport (fun x ↦ η.toFun x * η.toFun x) ⊆ tsupport η.toFun
  exact tsupport_mul_subset_left

/-- Multiplier form of `Dᵢ(η²) = (Dᵢη)η + η(Dᵢη)`. -/
theorem partialTestFunctionLpTop_squaredCutoff
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n) :
    partialTestFunctionLpTop (n := n) (Ω := Ω) (squaredCutoff η) i =
      partialTestFunctionLpTop (n := n) (Ω := Ω) η i •
          testFunctionLpTop (n := n) (Ω := Ω) η +
        testFunctionLpTop (n := n) (Ω := Ω) η •
          partialTestFunctionLpTop (n := n) (Ω := Ω) η i := by
  simpa [squaredCutoff] using
    (partialTestFunctionLpTop_mul (n := n) (Ω := Ω) η η i)

/-- Acting on an `L²` field, the derivative of a squared cutoff is twice the
same localized multiplier.  The duplicated sum is retained instead of using
the scalar `2`, which keeps the heterogeneous `Lp` exponents explicit. -/
theorem partialSquaredCutoff_smul
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n)
    (u : DerivLp n 2 Ω) :
    partialTestFunctionLpTop (n := n) (Ω := Ω) (squaredCutoff η) i • u =
      testFunctionLpTop (n := n) (Ω := Ω) η •
          (partialTestFunctionLpTop (n := n) (Ω := Ω) η i • u) +
        testFunctionLpTop (n := n) (Ω := Ω) η •
          (partialTestFunctionLpTop (n := n) (Ω := Ω) η i • u) := by
  rw [partialTestFunctionLpTop_squaredCutoff]
  rw [MeasureTheory.Lp.smul_add]
  rw [← lpSMul_top_top_two_assoc, lpSMul_top_top_two_comm]
  rw [← lpSMul_top_top_two_assoc]

/-- Quantitative `L²` bound for multiplication by `Dᵢ(η²)`. -/
theorem norm_partialSquaredCutoff_smul_le
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n)
    (u : DerivLp n 2 Ω) :
    ‖partialTestFunctionLpTop (n := n) (Ω := Ω) (squaredCutoff η) i • u‖ ≤
      2 * ‖testFunctionLpTop (n := n) (Ω := Ω) η‖ *
        ‖partialTestFunctionLpTop (n := n) (Ω := Ω) η i‖ * ‖u‖ := by
  rw [partialSquaredCutoff_smul]
  calc
    ‖testFunctionLpTop (n := n) (Ω := Ω) η •
          (partialTestFunctionLpTop (n := n) (Ω := Ω) η i • u) +
        testFunctionLpTop (n := n) (Ω := Ω) η •
          (partialTestFunctionLpTop (n := n) (Ω := Ω) η i • u)‖
        ≤ 2 * ‖testFunctionLpTop (n := n) (Ω := Ω) η •
          (partialTestFunctionLpTop (n := n) (Ω := Ω) η i • u)‖ := by
      simpa [two_mul] using norm_add_le
        (testFunctionLpTop (n := n) (Ω := Ω) η •
          (partialTestFunctionLpTop (n := n) (Ω := Ω) η i • u))
        (testFunctionLpTop (n := n) (Ω := Ω) η •
          (partialTestFunctionLpTop (n := n) (Ω := Ω) η i • u))
    _ ≤ 2 * (‖testFunctionLpTop (n := n) (Ω := Ω) η‖ *
          ‖partialTestFunctionLpTop (n := n) (Ω := Ω) η i • u‖) := by
      gcongr
      exact MeasureTheory.Lp.norm_smul_le _ _
    _ ≤ 2 * (‖testFunctionLpTop (n := n) (Ω := Ω) η‖ *
          (‖partialTestFunctionLpTop (n := n) (Ω := Ω) η i‖ * ‖u‖)) := by
      gcongr
      exact MeasureTheory.Lp.norm_smul_le _ _
    _ = 2 * ‖testFunctionLpTop (n := n) (Ω := Ω) η‖ *
        ‖partialTestFunctionLpTop (n := n) (Ω := Ω) η i‖ * ‖u‖ := by ring

/-- Multiplication by `η²` retains one localized factor `η • u`. -/
theorem norm_squaredCutoff_smul_le
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (u : DerivLp n 2 Ω) :
    ‖testFunctionLpTop (n := n) (Ω := Ω) (squaredCutoff η) • u‖ ≤
      ‖testFunctionLpTop (n := n) (Ω := Ω) η‖ *
        ‖testFunctionLpTop (n := n) (Ω := Ω) η • u‖ := by
  let q := testFunctionLpTop (n := n) (Ω := Ω) η
  have hsq :
      testFunctionLpTop (n := n) (Ω := Ω) (squaredCutoff η) =
        (q • q : DerivLp n ∞ Ω) := by
    simpa [q, squaredCutoff] using
      (testFunctionLpTop_mul (n := n) (Ω := Ω) η η)
  rw [hsq, ← lpSMul_top_top_two_assoc]
  exact MeasureTheory.Lp.norm_smul_le _ _

/-- Pairing a field against the derivative of a squared cutoff retains one cutoff
on that field. This applies directly to nonlinear flux quotients. -/
theorem abs_inner_partialSquaredCutoff_le
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n)
    (v u : DerivLp n 2 Ω) :
    |inner ℝ v
        (partialTestFunctionLpTop (n := n) (Ω := Ω) (squaredCutoff η) i • u)| ≤
      2 * ‖testFunctionLpTop (n := n) (Ω := Ω) η • v‖ *
        ‖partialTestFunctionLpTop (n := n) (Ω := Ω) η i‖ * ‖u‖ := by
  let q := testFunctionLpTop (n := n) (Ω := Ω) η
  let d := partialTestFunctionLpTop (n := n) (Ω := Ω) η i
  have hone : |inner ℝ v (q • (d • u))| ≤ ‖q • v‖ * (‖d‖ * ‖u‖) := by
    rw [← inner_lpSMul_left_eq_right]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (MeasureTheory.Lp.norm_smul_le d u) (norm_nonneg _))
  rw [partialSquaredCutoff_smul, inner_add_right]
  calc
    |inner ℝ v (q • (d • u)) + inner ℝ v (q • (d • u))| ≤
        |inner ℝ v (q • (d • u))| + |inner ℝ v (q • (d • u))| := abs_add_le _ _
    _ ≤ 2 * (‖q • v‖ * (‖d‖ * ‖u‖)) := by
      simpa only [two_mul] using add_le_add hone hone
    _ = _ := by ring

/-- A principal coefficient paired against the derivative-of-cutoff error
retains one cutoff on the principal field.  This is the form that can be
absorbed into elliptic coercivity in Evans' interior estimate. -/
theorem abs_inner_lpSMul_partialSquaredCutoff_le
    (a : DerivLp n ∞ Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n)
    (v u : DerivLp n 2 Ω) :
    |inner ℝ (a • v)
        (partialTestFunctionLpTop (n := n) (Ω := Ω)
          (squaredCutoff η) i • u)| ≤
      2 * ‖a‖ *
        ‖testFunctionLpTop (n := n) (Ω := Ω) η • v‖ *
        ‖partialTestFunctionLpTop (n := n) (Ω := Ω) η i‖ * ‖u‖ := by
  have h := abs_inner_partialSquaredCutoff_le η i (a • v) u
  rw [lpSMul_top_top_two_comm] at h
  refine h.trans ?_
  calc
    _ ≤ 2 * (‖a‖ * ‖testFunctionLpTop (n := n) (Ω := Ω) η • v‖) *
        ‖partialTestFunctionLpTop (n := n) (Ω := Ω) η i‖ * ‖u‖ := by
      gcongr
      exact MeasureTheory.Lp.norm_smul_le _ _
    _ = _ := by ring

/-- Young-absorbed version of the principal cutoff-error estimate. -/
theorem abs_inner_lpSMul_partialSquaredCutoff_le_young
    (a : DerivLp n ∞ Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n)
    (v u : DerivLp n 2 Ω) {alpha : ℝ} (halpha : 0 < alpha) :
    |inner ℝ (a • v)
        (partialTestFunctionLpTop (n := n) (Ω := Ω)
          (squaredCutoff η) i • u)| ≤
      (2 * ‖a‖ *
          ‖partialTestFunctionLpTop (n := n) (Ω := Ω) η i‖ * ‖u‖) ^ 2 /
          alpha +
        (alpha / 4) *
          ‖testFunctionLpTop (n := n) (Ω := Ω) η • v‖ ^ 2 := by
  calc
    |inner ℝ (a • v)
        (partialTestFunctionLpTop (n := n) (Ω := Ω)
          (squaredCutoff η) i • u)| ≤
        2 * ‖a‖ *
          ‖testFunctionLpTop (n := n) (Ω := Ω) η • v‖ *
          ‖partialTestFunctionLpTop (n := n) (Ω := Ω) η i‖ * ‖u‖ :=
      abs_inner_lpSMul_partialSquaredCutoff_le a η i v u
    _ = (2 * ‖a‖ *
          ‖partialTestFunctionLpTop (n := n) (Ω := Ω) η i‖ * ‖u‖) *
        ‖testFunctionLpTop (n := n) (Ω := Ω) η • v‖ := by ring
    _ ≤ (2 * ‖a‖ *
          ‖partialTestFunctionLpTop (n := n) (Ω := Ω) η i‖ * ‖u‖) ^ 2 /
          alpha +
        (alpha / 4) *
          ‖testFunctionLpTop (n := n) (Ω := Ω) η • v‖ ^ 2 :=
      mul_le_sq_div_add_quarter halpha _ _

/-- Pairing against `η²v` places one cutoff on each `L²` field.  This is the
localized form of a coefficient-commutator term. -/
theorem abs_inner_lpSMul_squaredCutoff_le
    (a : DerivLp n ∞ Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (u v : DerivLp n 2 Ω) :
    |inner ℝ (a • u)
        (testFunctionLpTop (n := n) (Ω := Ω) (squaredCutoff η) • v)| ≤
      ‖a‖ * ‖testFunctionLpTop (n := n) (Ω := Ω) η • u‖ *
        ‖testFunctionLpTop (n := n) (Ω := Ω) η • v‖ := by
  let q := testFunctionLpTop (n := n) (Ω := Ω) η
  have hsq :
      testFunctionLpTop (n := n) (Ω := Ω) (squaredCutoff η) =
        (q • q : DerivLp n ∞ Ω) := by
    simpa [q, squaredCutoff] using
      (testFunctionLpTop_mul (n := n) (Ω := Ω) η η)
  calc
    |inner ℝ (a • u)
        (testFunctionLpTop (n := n) (Ω := Ω) (squaredCutoff η) • v)| =
        |inner ℝ (a • u) ((q • q : DerivLp n ∞ Ω) • v)| := by rw [hsq]
    _ = |inner ℝ (a • u) (q • (q • v))| := by
      rw [lpSMul_top_top_two_assoc]
    _ = |inner ℝ (q • (a • u)) (q • v)| := by
      exact congrArg abs
        (inner_lpSMul_left_eq_right q (a • u) (q • v)).symm
    _ = |inner ℝ (a • (q • u)) (q • v)| := by
      rw [lpSMul_top_top_two_comm]
    _ ≤ ‖a • (q • u)‖ * ‖q • v‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖a‖ * ‖q • u‖) * ‖q • v‖ := by
      gcongr
      exact MeasureTheory.Lp.norm_smul_le _ _

/-- The local `H¹(Ω)` field represented by
`η² D_i^h(E₀u)`, before remembering its zero-boundary membership. -/
noncomputable def localizedDifferenceField
    (hΩopen : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (i : Fin n) (h : ℝ) (u : H¹₀(Ω)) :
    H¹(Ω) :=
  cutoffCLM (n := n) (p := 2) (Ω := Ω) (squaredCutoff η)
    (restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
      (subset_univ Ω)
      (differenceQuotientH1 i h
        (ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet u)))

/-- Evans' localized forward-difference field is an admissible element of
`H¹₀(Ω)` whenever the cutoff is compactly supported in `Ω`. -/
noncomputable def localizedDifferenceH10
    (hΩopen : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (i : Fin n) (h : ℝ) (u : H¹₀(Ω)) :
    H¹₀(Ω) :=
  ⟨localizedDifferenceField hΩopen η i h u,
    cutoffCLM_mem_H10 hΩopen (squaredCutoff η)
      ((tsupport_squaredCutoff_subset η).trans hηΩ)
      (restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
        (subset_univ Ω)
        (differenceQuotientH1 i h
          (ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet u)))⟩

/-- Forgetting the `H¹₀(Ω)` membership proof recovers the underlying `H¹(Ω)` field. -/
@[simp]
theorem localizedDifferenceH10_coe
    (hΩopen : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (i : Fin n) (h : ℝ) (u : H¹₀(Ω)) :
    ((localizedDifferenceH10 hΩopen η hηΩ i h u :
      H¹₀(Ω)) : H¹(Ω)) =
      localizedDifferenceField hΩopen η i h u :=
  rfl

/-- Coordinate formula for the localized forward-difference field. -/
theorem localizedDifferenceH10_coordinate
    (hΩopen : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (i : Fin n) (h : ℝ) (u : H¹₀(Ω))
    (q : DerivIndex n 1) :
    let G : H¹(ℝ^n) := differenceQuotientH1 i h
      (ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet u);
    (((localizedDifferenceH10 hΩopen η hηΩ i h u :
      H¹₀(Ω)) : H¹(Ω)) :
        WkpAmbientOn n 1 2 Ω) q =
      cutoffLpAt (n := n) (p := 2) (Ω := Ω) (squaredCutoff η) q
        (restrictAmbient (n := n) (k := 1) (p := 2)
          (subset_univ Ω) (G : WkpAmbientOn n 1 2 Set.univ)) := by
  dsimp only
  rfl

/-- Preimage of a support set under translation by `a`. -/
def shiftedSupport (a : ℝ^n) (K : Set (ℝ^n)) : Set (ℝ^n) :=
  {x | x + a ∈ K}

/-- A coordinate-shifted support lies in the closed `|h|`-thickening of
the original support. -/
theorem shiftedSupport_coordinateStep_subset_cthickening
    (i : Fin n) (h : ℝ) (K : Set (ℝ^n)) :
    shiftedSupport (coordinateStep i h) K ⊆ Metric.cthickening |h| K := by
  intro x hx
  apply Metric.mem_cthickening_of_dist_le
    x (x + coordinateStep i h) |h| K hx
  rw [dist_eq_norm]
  simp [norm_coordinateStep]

/-- A compact cutoff supported in an open domain has one uniform collar for
all sufficiently small coordinate shifts.  This is the geometric fact used
implicitly when Evans tests with `-Dᵢ⁻ʰ(η²Dᵢʰu)`. -/
theorem exists_uniform_shiftedSupport_collar
    (hΩopen : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hηΩ : tsupport η.toFun ⊆ Ω) (i : Fin n) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ h : ℝ, |h| ≤ ρ →
      Metric.cthickening ρ
        (shiftedSupport (coordinateStep i h) (tsupport η.toFun)) ⊆ Ω := by
  have hKcompact : IsCompact (tsupport η.toFun) := by
    simpa [HasCompactSupport] using η.hasCompactSupport
  obtain ⟨r, hr, hrΩ⟩ :=
    hKcompact.exists_cthickening_subset_open hΩopen hηΩ
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro h hh
  calc
    Metric.cthickening (r / 2)
        (shiftedSupport (coordinateStep i h) (tsupport η.toFun)) ⊆
        Metric.cthickening (r / 2)
          (Metric.cthickening |h| (tsupport η.toFun)) :=
      Metric.cthickening_subset_of_subset _
        (shiftedSupport_coordinateStep_subset_cthickening i h _)
    _ ⊆ Metric.cthickening (r / 2 + |h|) (tsupport η.toFun) :=
      Metric.cthickening_cthickening_subset (half_pos hr).le (abs_nonneg h) _
    _ ⊆ Metric.cthickening r (tsupport η.toFun) := by
      apply Metric.cthickening_mono
      linarith
    _ ⊆ Ω := hrΩ

/-- Canonical nonzero sequence of difference-quotient steps inside a collar
of radius `ρ`. -/
def collarStep (ρ : ℝ) (m : ℕ) : ℝ :=
  ρ / ((m : ℝ) + 1)

/-- Collar steps are nonzero, so they are admissible difference-quotient steps. -/
theorem collarStep_ne_zero {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) :
    collarStep ρ m ≠ 0 := by
  exact div_ne_zero hρ.ne' (by positivity)

/-- Collar steps stay within the collar radius `ρ`. -/
theorem abs_collarStep_le {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) :
    |collarStep ρ m| ≤ ρ := by
  rw [collarStep, abs_of_pos (div_pos hρ (by positivity))]
  exact div_le_self hρ.le (by norm_num)

/-- The collar steps `ρ/(m+1)` tend to zero, which is what the limit `h → 0` in the
difference-quotient argument runs along. -/
theorem tendsto_collarStep_zero (ρ : ℝ) :
    Filter.Tendsto (collarStep ρ) Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun m : ℕ ↦ (1 : ℝ) / (m + 1))
      Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  change Filter.Tendsto
    (fun m : ℕ ↦ ρ * ((m : ℝ) + 1)⁻¹) Filter.atTop (nhds 0)
  have hρlim : Filter.Tendsto (fun _ : ℕ ↦ ρ)
      Filter.atTop (nhds ρ) :=
    tendsto_const_nhds
  simpa only [one_div, mul_zero] using hρlim.mul hbase

/-- The support of a translated function lies in the translated preimage of
any closed set containing the original support. -/
theorem tsupport_comp_add_subset_shiftedSupport
    (a : ℝ^n) {f : ℝ^n → ℝ} {K : Set (ℝ^n)}
    (hKclosed : IsClosed K) (hfK : Function.support f ⊆ K) :
    tsupport (fun x ↦ f (x + a)) ⊆ shiftedSupport a K := by
  apply closure_minimal
  · intro x hx
    exact hfK hx
  · exact hKclosed.preimage (continuous_id.add continuous_const)

/-- The full Evans test
`-D_i^{-h}(η² D_i^h(E₀u))`, bundled in `H¹₀(Ω)`.

The geometric hypothesis says that the support of the translated localized
field has a positive collar in `Ω`.  A standard compactness argument supplies
such a collar uniformly for all sufficiently small `|h|`. -/
noncomputable def backwardLocalizedDifferenceH10
    (hΩopen : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (i : Fin n) (h : ℝ) (u : H¹₀(Ω))
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep i (-h)) (tsupport η.toFun)) ⊆ Ω) :
    H¹₀(Ω) := by
  let w : H¹₀(Ω) :=
    localizedDifferenceH10 hΩopen η hηΩ i h u
  let K : Set (ℝ^n) := tsupport η.toFun
  let v : ℝ^n → ℝ := fun x ↦
    ((((w : H¹(Ω)) : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) :
      DerivLp n 2 Ω) : ℝ^n → ℝ) x
  let f : ℝ^n → ℝ := K.indicator v
  have hKcompact : IsCompact K := by
    simpa [K, HasCompactSupport] using η.hasCompactSupport
  have hKlocal : K.indicator v =ᵐ[domainMeasure n Ω] v := by
    have hsquared := cutoffCLM_base_tsupport_indicator_ae
      (n := n) (p := 2) (Ω := Ω) (squaredCutoff η)
      (restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
        (subset_univ Ω)
        (differenceQuotientH1 i h
          (ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
            hΩopen.measurableSet u)))
    filter_upwards [hsquared] with x hx
    by_cases hxK : x ∈ K
    · simp [hxK]
    · have hxSq : x ∉ tsupport (squaredCutoff η).toFun := fun hx' ↦
        hxK (tsupport_squaredCutoff_subset η hx')
      have hvzero : v x = 0 := by
        have := hx
        rw [Set.indicator_of_notMem hxSq] at this
        simpa [v, w, localizedDifferenceH10, localizedDifferenceField] using this.symm
      simp [hxK, hvzero]
  have hfSupport : Function.support f ⊆ K := by
    intro x hx
    by_contra hxK
    exact hx (by simp [f, hxK])
  have hfcs : HasCompactSupport f := by
    simpa [HasCompactSupport, tsupport] using hKcompact.closure_of_subset hfSupport
  have hzero := ZeroTrace.zeroExtendH10_coordinate_apply_ae
    (n := n) (Ω := Ω) hΩopen.measurableSet w (baseIndex n 1)
  have hindicatorGlobal :
      Ω.indicator (K.indicator v) =ᵐ[MeasureTheory.volume] Ω.indicator v :=
    (ae_eq_restrict_iff_indicator_ae_eq hΩopen.measurableSet).1
      (by simpa [domainMeasure] using hKlocal)
  have hKΩ : K ⊆ Ω := by simpa [K] using hηΩ
  have hΩK : Ω.indicator (K.indicator v) = K.indicator v := by
    funext x
    by_cases hxK : x ∈ K
    · simp [hxK, hKΩ hxK]
    · simp [hxK]
  have hbase :
      (((((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet w :
        H¹(ℝ^n)) : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
          DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume] f := by
    simpa [f, v, hΩK] using hzero.trans hindicatorGlobal.symm
  have htranslatedSupport :
      tsupport (fun x ↦ f (x + coordinateStep i (-h))) ⊆
        shiftedSupport (coordinateStep i (-h)) K :=
    tsupport_comp_add_subset_shiftedSupport _ hKcompact.isClosed hfSupport
  have hactualCollar : Metric.cthickening δ
      (tsupport (fun x ↦ f (x + coordinateStep i (-h)))) ⊆ Ω :=
    (Metric.cthickening_subset_of_subset δ htranslatedSupport).trans hshift
  let μ := Approximation.standardMollifier n
  have hμcompact : IsCompact (tsupport μ.ρ) := by
    simpa [μ, HasCompactSupport] using μ.compactSupport
  let radiusWitness := hμcompact.isBounded.subset_closedBall (0 : ℝ^n)
  let R0 : ℝ := Classical.choose radiusWitness
  have hR0 : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R0 :=
    Classical.choose_spec radiusWitness
  let R : ℝ := max R0 0
  have hRnonneg : 0 ≤ R := le_max_right _ _
  have hμR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R :=
    hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  let q : H¹(Ω) :=
    restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
      (subset_univ Ω)
      (differenceQuotientH1 i (-h)
        (ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet w))
  have hqmem := restrict_differenceQuotientH1_zeroExtend_mem_H10
    hΩopen μ i (-h) w f hbase hfcs hRnonneg hδ hμR hactualCollar
  exact ⟨-q,
    (h10SubmoduleOn (n := n) (Ω := Ω)).neg_mem
      (by simpa [q] using hqmem)⟩

/-- Forgetting the membership proof exposes the standard signed backward
difference quotient used as the weak test function. -/
theorem backwardLocalizedDifferenceH10_coe
    (hΩopen : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (i : Fin n) (h : ℝ) (u : H¹₀(Ω))
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep i (-h)) (tsupport η.toFun)) ⊆ Ω) :
    ((backwardLocalizedDifferenceH10 hΩopen η hηΩ i h u hδ hshift :
      H¹₀(Ω)) : H¹(Ω)) =
      -restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
        (subset_univ Ω)
        (differenceQuotientH1 i (-h)
          (ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet
            (localizedDifferenceH10 hΩopen η hηΩ i h u))) := by
  rfl

/-- Every coordinate of the signed backward test is the negative restricted
`L²` backward quotient of the corresponding localized coordinate. -/
theorem backwardLocalizedDifferenceH10_coordinate
    (hΩopen : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (i : Fin n) (h : ℝ) (u : H¹₀(Ω))
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep i (-h)) (tsupport η.toFun)) ⊆ Ω)
    (q : DerivIndex n 1) :
    let w := localizedDifferenceH10 hΩopen η hηΩ i h u;
    let Z : H¹(ℝ^n) := ZeroTrace.zeroExtendH10
      (n := n) (Ω := Ω) hΩopen.measurableSet w;
    (((backwardLocalizedDifferenceH10 hΩopen η hηΩ i h u hδ hshift :
      H¹₀(Ω)) : H¹(Ω)) :
        WkpAmbientOn n 1 2 Ω) q =
      -restrictDerivLp (n := n) (p := 2)
        (subset_univ Ω)
        (differenceQuotientLp 2 i (-h)
          ((Z : WkpAmbientOn n 1 2 Set.univ) q)) := by
  dsimp only
  rw [backwardLocalizedDifferenceH10_coe]
  change -restrictDerivLp (n := n) (p := 2)
      (subset_univ Ω)
      (((differenceQuotientH1 i (-h)
        (ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet
          (localizedDifferenceH10 hΩopen η hηΩ i h u)) : H¹(ℝ^n)) :
            WkpAmbientOn n 1 2 Set.univ) q) = _
  rw [differenceQuotientH1_coordinate]

end SobolevSpace.GraphSpace.DifferenceQuotient
