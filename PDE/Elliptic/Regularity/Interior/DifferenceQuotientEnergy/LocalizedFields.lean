/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DifferenceQuotientEnergy.Quantities
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized.Coordinates
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.CoefficientCommutator
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative

/-!
# Localized fields for interior difference-quotient energy

Evans' interior `H²` argument uses two fields built from `u ∈ H¹₀(Ω)`, a
cutoff `η ∈ C_c^∞(Ω)` and a step `h`: the localized forward field
`w = η² Dₖʰ(E₀ u)`, where `E₀` is extension by zero to `ℝ^n`, and the signed
backward test `v = -Dₖ⁻ʰ w`. The coordinate formulas are in the Sobolev
difference-quotient library. We estimate the `H¹` norm of `w` and the
forcing term `⟪f, v⟫`.

## Main results

* `norm_localizedDifferenceH10_sq`, `norm_localizedDifferenceH10_sq_le`:
  the exact and estimated `H¹` norm of the forward test.
* `norm_baseCoord_backwardLocalizedDifferenceH10_le`,
  `abs_source_pairing_backwardLocalizedDifferenceH10_le_young`: the base
  coordinate of `v` is bounded by `‖w‖_{H¹}`, so `|⟪f, v⟫|` is absorbed by
  Young's inequality with a free parameter `gamma`.

## Implementation notes

The backward test is admissible only if the translated support of `η` stays
inside `Ω`; this is the `cthickening` hypothesis `hshift`. Because the cutoff
has compact support in `Ω`, extending the product-rule terms by zero produces
no boundary contribution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, proof of Theorem 1, step 3 (the test function
  (11)) and step 5 (the estimate of the right-hand side, (21)-(22)).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open scoped Topology InnerProductSpace
open DifferenceQuotient

variable {n : ℕ} {Ω : Set (ℝ^n)}

private theorem norm_add_sq_le_two {E : Type*} [SeminormedAddCommGroup E]
    (x y : E) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hadd := norm_add_le x y
  have hsquare : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hadd
  calc
    ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := hsquare
    _ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Exact decomposition of the norm of Evans' localized forward test into
its base quotient and the product-rule expansion of every first derivative. -/
theorem norm_localizedDifferenceH10_sq
    (hΩopen : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) (h : ℝ)
    (u : H¹₀(Ω)) :
    let q0 := zeroExtendedBaseQuotient hΩopen.measurableSet k h u
    let v := zeroExtendedGradientQuotient hΩopen.measurableSet k h u
    ‖localizedDifferenceH10 hΩopen η hηΩ k h u‖ ^ 2 =
      ‖testFunctionLpTop (n := n) (Ω := Set.univ) (squaredCutoff η) • q0‖ ^ 2 +
        ∑ i : Fin n,
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) (squaredCutoff η) • v i +
            partialTestFunctionLpTop (n := n) (Ω := Set.univ)
              (squaredCutoff η) i • q0‖ ^ 2 := by
  dsimp only [zeroExtendedBaseQuotient, zeroExtendedGradientQuotient,
    zeroExtendedGradient]
  have hdecomp := norm_sq_eq_base_sq_add_sum_deriv_sq
    (n := n) (Ω := Ω)
    (localizedDifferenceH10 hΩopen η hηΩ k h u)
  have hdecomp' :
      ‖localizedDifferenceH10 hΩopen η hηΩ k h u‖ ^ 2 =
        ‖baseCoordCLM (n := n) (Ω := Ω)
          (localizedDifferenceH10 hΩopen η hηΩ k h u)‖ ^ 2 +
        ∑ i : Fin n,
          ‖derivCoordCLM (n := n) (Ω := Ω) i
            (localizedDifferenceH10 hΩopen η hηΩ k h u)‖ ^ 2 := by
    exact hdecomp
  rw [hdecomp']
  congr 1
  · rw [← Extension.Lp.norm_zeroExtendLp
      (n := n) (p := 2) (Ω := Ω) hΩopen.measurableSet]
    change
      ‖(((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
        hΩopen.measurableSet
        (localizedDifferenceH10 hΩopen η hηΩ k h u) : H¹((Set.univ : Set (ℝ^n)))) :
          WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))‖ ^ 2 = _
    rw [zeroExtendedBase_localizedDifferenceH10]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Extension.Lp.norm_zeroExtendLp
      (n := n) (p := 2) (Ω := Ω) hΩopen.measurableSet]
    change
      ‖(((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
        hΩopen.measurableSet
        (localizedDifferenceH10 hΩopen η hηΩ k h u) : H¹((Set.univ : Set (ℝ^n)))) :
          WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i))‖ ^ 2 = _
    rw [zeroExtendedDeriv_localizedDifferenceH10]

/-- Quantitative form of the localized-test norm decomposition.  Every
second-difference term remains weighted by one cutoff, while all remaining
terms involve only the first difference quotient `q0`. -/
theorem norm_localizedDifferenceH10_sq_le
    (hΩopen : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) (h : ℝ)
    (u : H¹₀(Ω)) :
    let q0 := zeroExtendedBaseQuotient hΩopen.measurableSet k h u
    let v := zeroExtendedGradientQuotient hΩopen.measurableSet k h u
    let q := testFunctionLpTop (n := n) (Ω := Set.univ) η
    ‖localizedDifferenceH10 hΩopen η hηΩ k h u‖ ^ 2 ≤
      (‖q‖ * ‖q • q0‖) ^ 2 +
        ∑ i : Fin n,
          (2 * (‖q‖ * ‖q • v i‖) ^ 2 +
            2 * (2 * ‖q‖ *
              ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ *
                ‖q0‖) ^ 2) := by
  dsimp only [zeroExtendedBaseQuotient, zeroExtendedGradientQuotient,
    zeroExtendedGradient]
  have hnorm := norm_localizedDifferenceH10_sq hΩopen η hηΩ k h u
  dsimp only [zeroExtendedBaseQuotient, zeroExtendedGradientQuotient,
    zeroExtendedGradient] at hnorm
  rw [hnorm]
  apply add_le_add
  · exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_squaredCutoff_smul_le η
        (differenceQuotientLp 2 k h
          ((((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
            hΩopen.measurableSet u : H¹((Set.univ : Set (ℝ^n)))) :
              WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))))) 2
  · apply Finset.sum_le_sum
    intro i _
    let vi := differenceQuotientLp 2 k h
      ((((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
        hΩopen.measurableSet u : H¹((Set.univ : Set (ℝ^n)))) :
          WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i)))
    let q0 := differenceQuotientLp 2 k h
      ((((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
        hΩopen.measurableSet u : H¹((Set.univ : Set (ℝ^n)))) :
          WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)))
    calc
      ‖testFunctionLpTop (n := n) (Ω := Set.univ) (squaredCutoff η) • vi +
          partialTestFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) i • q0‖ ^ 2 ≤
          2 * ‖testFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) • vi‖ ^ 2 +
          2 * ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) i • q0‖ ^ 2 :=
        norm_add_sq_le_two _ _
      _ ≤ 2 * (‖testFunctionLpTop (n := n) (Ω := Set.univ) η‖ *
              ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • vi‖) ^ 2 +
          2 * (2 * ‖testFunctionLpTop (n := n) (Ω := Set.univ) η‖ *
              ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ *
                ‖q0‖) ^ 2 := by
        gcongr
        · exact norm_squaredCutoff_smul_le η vi
        · exact norm_partialSquaredCutoff_smul_le η i q0
/-- The base coordinate of Evans' signed test is controlled by the localized
forward field.  This is the difference-quotient estimate used on the source
term in the interior `H²` argument. For `h = 0` the difference quotient is `0`. -/
theorem norm_baseCoord_backwardLocalizedDifferenceH10_le
    (hΩopen : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) {h : ℝ}
    (u : H¹₀(Ω))
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω) :
    ‖baseCoordCLM (n := n) (Ω := Ω)
      (backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift)‖ ≤
        ‖localizedDifferenceH10 hΩopen η hηΩ k h u‖ := by
  rw [baseCoord_backwardLocalizedDifferenceH10]
  rw [norm_neg]
  calc
    ‖restrictDerivLp (n := n) (p := 2)
        (subset_univ Ω)
        (differenceQuotientLp 2 k (-h)
          (((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet
            (localizedDifferenceH10 hΩopen η hηΩ k h u) : H¹((Set.univ : Set (ℝ^n)))) :
              WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)))‖
        ≤ ‖differenceQuotientLp 2 k (-h)
          (((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet
            (localizedDifferenceH10 hΩopen η hηΩ k h u) : H¹((Set.univ : Set (ℝ^n)))) :
              WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))‖ :=
      norm_restrictDerivLp_le (subset_univ Ω) _
    _ = ‖zeroExtensionDifferenceQuotient hΩopen.measurableSet k (-h)
        (localizedDifferenceH10 hΩopen η hηΩ k h u)‖ := by
      rfl
    _ ≤ ‖localizedDifferenceH10 hΩopen η hηΩ k h u‖ := by
      rcases eq_or_ne h 0 with rfl | hh
      · simp [zeroExtensionDifferenceQuotient]
      · exact zeroExtensionDifferenceQuotient.norm_le hΩopen.measurableSet k
          (neg_ne_zero.mpr hh) _

/-- Cauchy–Schwarz and the signed-test estimate control the source pairing
by the norm of the localized forward difference field. -/
theorem abs_source_pairing_backwardLocalizedDifferenceH10_le
    (hΩopen : IsOpen Ω)
    (f : DerivLp n 2 Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) {h : ℝ}
    (u : H¹₀(Ω))
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω) :
    |inner ℝ f (baseCoordCLM (n := n) (Ω := Ω)
      (backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift))| ≤
      ‖f‖ * ‖localizedDifferenceH10 hΩopen η hηΩ k h u‖ := by
  calc
    |inner ℝ f
        (baseCoordCLM (n := n) (Ω := Ω)
          (backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift))|
        ≤ ‖f‖ * ‖baseCoordCLM (n := n) (Ω := Ω)
          (backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift)‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖f‖ * ‖localizedDifferenceH10 hΩopen η hηΩ k h u‖ :=
      mul_le_mul_of_nonneg_left
        (norm_baseCoord_backwardLocalizedDifferenceH10_le
          hΩopen η hηΩ k u hδ hshift)
        (norm_nonneg f)

/-- Young-absorbed `L²` source estimate with the localized test norm fully
expanded.  The free parameter `gamma` determines how much of the elliptic
energy is spent on the forcing term. -/
theorem abs_source_pairing_backwardLocalizedDifferenceH10_le_young
    (hΩopen : IsOpen Ω)
    (f : DerivLp n 2 Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) {h : ℝ}
    (u : H¹₀(Ω))
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω)
    {gamma : ℝ} (hgamma : 0 < gamma) :
    |inner ℝ f (baseCoordCLM (n := n) (Ω := Ω)
      (backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift))| ≤
      localizedDifferenceSourceRemainder η ‖f‖ gamma
        (zeroExtendedBaseQuotient hΩopen.measurableSet k h u)
        (zeroExtendedGradientQuotient hΩopen.measurableSet k h u) := by
  dsimp only [zeroExtendedBaseQuotient, zeroExtendedGradientQuotient,
    zeroExtendedGradient, localizedDifferenceSourceRemainder]
  let w := localizedDifferenceH10 hΩopen η hηΩ k h u
  have hsource := abs_source_pairing_backwardLocalizedDifferenceH10_le
    hΩopen f η hηΩ k u hδ hshift
  have htest := norm_localizedDifferenceH10_sq_le hΩopen η hηΩ k h u
  dsimp only [zeroExtendedBaseQuotient, zeroExtendedGradientQuotient,
    zeroExtendedGradient] at htest
  calc
    |inner ℝ f
        (baseCoordCLM (n := n) (Ω := Ω)
          (backwardLocalizedDifferenceH10
            hΩopen η hηΩ k h u hδ hshift))| ≤ ‖f‖ * ‖w‖ := hsource
    _ ≤ ‖f‖ ^ 2 / gamma + (gamma / 4) * ‖w‖ ^ 2 :=
      mul_le_sq_div_add_quarter hgamma _ _
    _ ≤ ‖f‖ ^ 2 / gamma + (gamma / 4) *
        ((‖testFunctionLpTop (n := n) (Ω := Set.univ) η‖ *
            ‖testFunctionLpTop (n := n) (Ω := Set.univ) η •
              differenceQuotientLp 2 k h
                ((((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
                  hΩopen.measurableSet u : H¹((Set.univ : Set (ℝ^n)))) :
                    WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)))‖) ^ 2 +
          ∑ i : Fin n,
            (2 * (‖testFunctionLpTop (n := n) (Ω := Set.univ) η‖ *
                ‖testFunctionLpTop (n := n) (Ω := Set.univ) η •
                  differenceQuotientLp 2 k h
                    ((((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
                      hΩopen.measurableSet u : H¹((Set.univ : Set (ℝ^n)))) :
                        WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i)))‖) ^ 2 +
              2 * (2 * ‖testFunctionLpTop (n := n) (Ω := Set.univ) η‖ *
                ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ *
                  ‖differenceQuotientLp 2 k h
                    ((((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
                      hΩopen.measurableSet u : H¹((Set.univ : Set (ℝ^n)))) :
                        WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)))‖) ^ 2)) := by
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_left htest
        (div_nonneg hgamma.le (show (0 : ℝ) ≤ 4 by norm_num))

end SobolevSpace.GraphSpace
