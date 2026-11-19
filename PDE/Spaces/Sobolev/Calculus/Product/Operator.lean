/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

-- The graph-space definitions are used directly; the import is kept explicit.
public import PDE.Spaces.Sobolev.Variational.Spaces.H1
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing

/-!
# Bounded first-order Sobolev multipliers

For a fixed coefficient `A ∈ W^{1,∞}(Ω)` on an open set `Ω ⊆ ℝ^n`, multiplication by `A` is
a continuous linear endomorphism of `W^{1,2}(Ω)` with operator norm at most
`2 √(n+1) ‖A‖_{W^{1,∞}}`. The ambient map on the derivative bundle is defined coordinatewise
by

* `u ↦ Au` in the base coordinate;
* `∂ᵢu ↦ A ∂ᵢu + (∂ᵢA) u` in the first-derivative coordinates.

Each coordinate is an `L^∞`-by-`L^2` product and so is bounded. The weak Leibniz rule
`WkpSpaceOn.hasWeakDerivativeOn_mul_W1Top_first` from `Product.FirstOrder` shows that this
bounded ambient map carries the Sobolev graph subspace into itself. This is the
`W^{1,∞} × W^{1,2}` case of the product rule for weak derivatives.

## Main results

* `w1TopMultiplierAmbient`: the coordinatewise multiplier on `WkpAmbientOn n 1 2 Ω`, with the
  coordinate formulas `w1TopMultiplierAmbient_base` and `w1TopMultiplierAmbient_singleDeriv`.
* `w1TopMultiplierCLM`: its restriction to `W^{1,2}(Ω) →L[ℝ] W^{1,2}(Ω)`, with the estimates
  `norm_w1TopMultiplierCLM_apply_le` and `norm_w1TopMultiplierCLM_le`.
* `w1TopMultiplicationCLM`: multiplication as a bounded bilinear map
  `W^{1,∞}(Ω) →L[ℝ] W^{1,2}(Ω) →L[ℝ] W^{1,2}(Ω)`, with `norm_w1TopMultiplicationCLM_le`.
* `w1TopMultiplierCLM_base_ae`, `w1TopMultiplierCLM_singleDeriv_apply_ae`: the base and
  first-derivative coordinates of the product are `Au` and `A ∂ᵢu + (∂ᵢA) u` almost
  everywhere.

## Implementation notes

The constant `w1TopMultiplierNormBound n = 2 √(card (DerivIndex n 1))` comes from the
coordinatewise bound `‖(AU)_a‖ ≤ 2 ‖A‖ ‖U‖` summed in `ℓ²` over the `n + 1` coordinates. It is
not sharp.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for the product rule in `W^{1,p}`.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 1(iv), (7), pp. 261-262, the Leibniz formula
  for `ζ u` with `ζ ∈ C_c^∞(U)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- One output coordinate of multiplication by a fixed `W^{1,∞}`
coefficient on the ambient `W^{1,2}` derivative bundle. -/
noncomputable def w1TopMultiplierLpAt
    (A : W^{1,∞}(Ω)) (a : DerivIndex n 1) :
    WkpAmbientOn n 1 2 Ω →L[ℝ] DerivLp n 2 Ω :=
  firstOrderRows
    ((mulLpLeft (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω)
      ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))).comp
      (PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
        (β := fun _ : DerivIndex n 1 ↦ DerivLp n 2 Ω)
        (baseIndex n 1)))
    (fun i ↦
      (mulLpLeft (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω)
        ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))).comp
          (PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
            (β := fun _ : DerivIndex n 1 ↦ DerivLp n 2 Ω)
            (singleDerivIndex n i)) +
      (mulLpLeft (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω)
        ((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i))).comp
          (PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
            (β := fun _ : DerivIndex n 1 ↦ DerivLp n 2 Ω)
            (baseIndex n 1)))
    a

/-- Multiplication by a fixed `W^{1,∞}` coefficient as a bounded linear map
on the ambient `W^{1,2}` derivative bundle. -/
noncomputable def w1TopMultiplierAmbient
    (A : W^{1,∞}(Ω)) :
    WkpAmbientOn n 1 2 Ω →L[ℝ] WkpAmbientOn n 1 2 Ω := by
  classical
  let e := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
    (β := fun _ : DerivIndex n 1 ↦ DerivLp n 2 Ω)
  exact e.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      w1TopMultiplierLpAt (n := n) (Ω := Ω) A a)

/-- Applying the ambient multiplier and then selecting a coordinate is the
same as applying the corresponding coordinate map. -/
@[simp]
theorem w1TopMultiplierAmbient_apply
    (A : W^{1,∞}(Ω)) (U : WkpAmbientOn n 1 2 Ω)
    (a : DerivIndex n 1) :
    w1TopMultiplierAmbient (n := n) (Ω := Ω) A U a =
      w1TopMultiplierLpAt (n := n) (Ω := Ω) A a U := by
  classical
  simp [w1TopMultiplierAmbient]

/-- Formula for the base coordinate map defining the ambient multiplier. -/
@[simp]
theorem w1TopMultiplierLpAt_base
    (A : W^{1,∞}(Ω)) (U : WkpAmbientOn n 1 2 Ω) :
    w1TopMultiplierLpAt (n := n) (Ω := Ω) A (baseIndex n 1) U =
      ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
        U (baseIndex n 1) := by
  simp [w1TopMultiplierLpAt]

/-- Formula for the base coordinate of the ambient multiplier. -/
theorem w1TopMultiplierAmbient_base
    (A : W^{1,∞}(Ω)) (U : WkpAmbientOn n 1 2 Ω) :
    w1TopMultiplierAmbient (n := n) (Ω := Ω) A U (baseIndex n 1) =
      ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
        U (baseIndex n 1) := by
  rw [w1TopMultiplierAmbient_apply]
  exact w1TopMultiplierLpAt_base (n := n) (Ω := Ω) A U

/-- Formula for a first-derivative coordinate map defining the ambient
multiplier. -/
@[simp]
theorem w1TopMultiplierLpAt_singleDeriv
    (A : W^{1,∞}(Ω)) (U : WkpAmbientOn n 1 2 Ω)
    (i : Fin n) :
    w1TopMultiplierLpAt (n := n) (Ω := Ω) A
        (singleDerivIndex n i) U =
      ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
          U (singleDerivIndex n i) +
        ((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)) •
          U (baseIndex n 1) := by
  simp [w1TopMultiplierLpAt]

/-- Formula for a first-derivative coordinate of the ambient multiplier. -/
theorem w1TopMultiplierAmbient_singleDeriv
    (A : W^{1,∞}(Ω)) (U : WkpAmbientOn n 1 2 Ω)
    (i : Fin n) :
    w1TopMultiplierAmbient (n := n) (Ω := Ω) A U
        (singleDerivIndex n i) =
      ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
          U (singleDerivIndex n i) +
        ((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)) •
          U (baseIndex n 1) := by
  rw [w1TopMultiplierAmbient_apply]
  exact w1TopMultiplierLpAt_singleDeriv (n := n) (Ω := Ω) A U i

/-- The ambient multiplier is additive in its coefficient. -/
theorem w1TopMultiplierAmbient_add_left
    (A B : W^{1,∞}(Ω)) (U : WkpAmbientOn n 1 2 Ω) :
    w1TopMultiplierAmbient (n := n) (Ω := Ω) (A + B) U =
      w1TopMultiplierAmbient (n := n) (Ω := Ω) A U +
        w1TopMultiplierAmbient (n := n) (Ω := Ω) B U := by
  classical
  apply PiLp.ext
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    simp only
      [w1TopMultiplierAmbient_base, Submodule.coe_add, PiLp.add_apply]
    exact MeasureTheory.Lp.smul_add _ _ _
  · subst a
    simp only
      [w1TopMultiplierAmbient_singleDeriv, Submodule.coe_add,
        PiLp.add_apply]
    rw [MeasureTheory.Lp.smul_add, MeasureTheory.Lp.smul_add]
    abel

/-- The ambient multiplier is homogeneous in its coefficient. -/
theorem w1TopMultiplierAmbient_smul_left
    (c : ℝ) (A : W^{1,∞}(Ω)) (U : WkpAmbientOn n 1 2 Ω) :
    w1TopMultiplierAmbient (n := n) (Ω := Ω) (c • A) U =
      c • w1TopMultiplierAmbient (n := n) (Ω := Ω) A U := by
  classical
  apply PiLp.ext
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    simp only
      [w1TopMultiplierAmbient_base, Submodule.coe_smul, PiLp.smul_apply]
    exact MeasureTheory.Lp.smul_assoc _ _ _
  · subst a
    simp only
      [w1TopMultiplierAmbient_singleDeriv, Submodule.coe_smul,
        PiLp.smul_apply]
    rw [MeasureTheory.Lp.smul_assoc, MeasureTheory.Lp.smul_assoc]
    exact (smul_add c _ _).symm

/-- Uniform estimate for every coordinate of the ambient first-order
multiplier. -/
theorem norm_w1TopMultiplierAmbient_apply_le
    (A : W^{1,∞}(Ω)) (U : WkpAmbientOn n 1 2 Ω)
    (a : DerivIndex n 1) :
    ‖w1TopMultiplierAmbient (n := n) (Ω := Ω) A U a‖ ≤
      2 * ‖A‖ * ‖U‖ := by
  classical
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    rw [w1TopMultiplierAmbient_base]
    calc
      ‖((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
          U (baseIndex n 1)‖
          ≤ ‖(A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)‖ *
              ‖U (baseIndex n 1)‖ :=
        MeasureTheory.Lp.norm_smul_le _ _
      _ ≤ ‖A‖ * ‖U‖ := by
        gcongr
        · simpa using
            (PiLp.norm_apply_le
              (A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))
        · exact PiLp.norm_apply_le U (baseIndex n 1)
      _ ≤ 2 * ‖A‖ * ‖U‖ := by
        nlinarith [mul_nonneg (norm_nonneg A) (norm_nonneg U)]
  · subst a
    rw [w1TopMultiplierAmbient_singleDeriv]
    calc
      ‖((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
            U (singleDerivIndex n i) +
          ((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)) •
            U (baseIndex n 1)‖
          ≤ ‖((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
              U (singleDerivIndex n i)‖ +
            ‖((A : WkpAmbientOn n 1 ∞ Ω)
                (singleDerivIndex n i)) • U (baseIndex n 1)‖ :=
        norm_add_le _ _
      _ ≤
          ‖(A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)‖ *
              ‖U (singleDerivIndex n i)‖ +
            ‖(A : WkpAmbientOn n 1 ∞ Ω)
                (singleDerivIndex n i)‖ *
              ‖U (baseIndex n 1)‖ :=
        add_le_add
          (MeasureTheory.Lp.norm_smul_le _ _)
          (MeasureTheory.Lp.norm_smul_le _ _)
      _ ≤ ‖A‖ * ‖U‖ + ‖A‖ * ‖U‖ := by
        gcongr
        · simpa using
            (PiLp.norm_apply_le
              (A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))
        · exact PiLp.norm_apply_le U (singleDerivIndex n i)
        · simpa using
            (PiLp.norm_apply_le
              (A : WkpAmbientOn n 1 ∞ Ω)
              (singleDerivIndex n i))
        · exact PiLp.norm_apply_le U (baseIndex n 1)
      _ = 2 * ‖A‖ * ‖U‖ := by ring

/-- Explicit dimension-dependent bound for multiplication by a fixed
`W^{1,∞}` coefficient on `W^{1,2}`. -/
noncomputable def w1TopMultiplierNormBound (n : ℕ) : ℝ :=
  2 * Real.sqrt (Fintype.card (DerivIndex n 1))

/-- The first-order multiplier bound is nonnegative. -/
theorem w1TopMultiplierNormBound_nonneg :
    0 ≤ w1TopMultiplierNormBound n := by
  unfold w1TopMultiplierNormBound
  positivity

/-- Quantitative graph-norm estimate for the ambient first-order multiplier. -/
theorem norm_w1TopMultiplierAmbient_le
    (A : W^{1,∞}(Ω)) (U : WkpAmbientOn n 1 2 Ω) :
    ‖w1TopMultiplierAmbient (n := n) (Ω := Ω) A U‖ ≤
      w1TopMultiplierNormBound n * ‖A‖ * ‖U‖ := by
  classical
  let C : ℝ := 2 * ‖A‖ * ‖U‖
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hsum :
      ∑ a : DerivIndex n 1,
          ‖w1TopMultiplierAmbient (n := n) (Ω := Ω) A U a‖ ^ 2 ≤
        (Fintype.card (DerivIndex n 1) : ℝ) * C ^ 2 := by
    calc
      ∑ a : DerivIndex n 1,
          ‖w1TopMultiplierAmbient (n := n) (Ω := Ω) A U a‖ ^ 2
          ≤ ∑ _a : DerivIndex n 1, C ^ 2 :=
        Finset.sum_le_sum fun a _ ↦
          pow_le_pow_left₀
            (norm_nonneg
              (w1TopMultiplierAmbient (n := n) (Ω := Ω) A U a))
            (by
              simpa [C] using
                norm_w1TopMultiplierAmbient_apply_le
                  (n := n) (Ω := Ω) A U a)
            2
      _ = (Fintype.card (DerivIndex n 1) : ℝ) * C ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [PiLp.norm_eq_of_L2, w1TopMultiplierNormBound]
  calc
    Real.sqrt
          (∑ a : DerivIndex n 1,
            ‖w1TopMultiplierAmbient (n := n) (Ω := Ω) A U a‖ ^ 2)
        ≤ Real.sqrt
            ((Fintype.card (DerivIndex n 1) : ℝ) * C ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Fintype.card (DerivIndex n 1)) * C := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC]
    _ = (2 * Real.sqrt (Fintype.card (DerivIndex n 1))) *
          ‖A‖ * ‖U‖ := by
      simp only [C]
      ring

private theorem w1TopMultiplierAmbient_base_apply_ae
    (A : W^{1,∞}(Ω)) (U : WkpAmbientOn n 1 2 Ω) :
    ((w1TopMultiplierAmbient (n := n) (Ω := Ω) A U
        (baseIndex n 1) : DerivLp n 2 Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦
          ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
            DerivLp n ∞ Ω) x *
          (U (baseIndex n 1) : DerivLp n 2 Ω) x := by
  rw [w1TopMultiplierAmbient_base]
  exact MeasureTheory.Lp.coeFn_lpSMul
    ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))
    (U (baseIndex n 1))

private theorem w1TopMultiplierAmbient_singleDeriv_apply_ae
    (A : W^{1,∞}(Ω)) (U : WkpAmbientOn n 1 2 Ω)
    (i : Fin n) :
    ((w1TopMultiplierAmbient (n := n) (Ω := Ω) A U
        (singleDerivIndex n i) : DerivLp n 2 Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦
          ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
            DerivLp n ∞ Ω) x *
              (U (singleDerivIndex n i) : DerivLp n 2 Ω) x +
          ((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) :
            DerivLp n ∞ Ω) x *
              (U (baseIndex n 1) : DerivLp n 2 Ω) x := by
  rw [w1TopMultiplierAmbient_singleDeriv]
  filter_upwards
    [MeasureTheory.Lp.coeFn_add
      (((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
        U (singleDerivIndex n i))
      (((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)) •
        U (baseIndex n 1)),
      MeasureTheory.Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
        ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))
        (U (singleDerivIndex n i)),
      MeasureTheory.Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
        ((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i))
        (U (baseIndex n 1))]
    with x hadd hbase hderiv
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hbase, hderiv]
  simp only [smul_eq_mul, Pi.mul_apply]

/-- The coordinatewise ambient multiplier sends graph-space elements to
graph-space elements: multiplying a `W^{1,2}` element by a `W^{1,∞}`
coefficient preserves the weak-derivative compatibility conditions. -/
theorem w1TopMultiplierAmbient_mapsIsWkpOn
    (hΩopen : IsOpen Ω) (A : W^{1,∞}(Ω))
    (U : WkpAmbientOn n 1 2 Ω)
    (hU : IsWkpOn (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) U) :
    IsWkpOn (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Ω)
      (w1TopMultiplierAmbient (n := n) (Ω := Ω) A U) := by
  classical
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    have hloc := memLp_locallyIntegrableOn_domain
      (MeasureTheory.Lp.memLp
        (w1TopMultiplierAmbient (n := n) (Ω := Ω) A U
          (baseIndex n 1)))
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa only [baseIndex_toList] using hasWeakDerivativeOn_nil hloc
  · subst a
    rw [singleDerivIndex_toList]
    have hweak :
        HasWeakDerivativeOn (n := n) Ω [i]
          (U (baseIndex n 1) : ℝ^n → ℝ)
          (U (singleDerivIndex n i) : ℝ^n → ℝ) := by
      simpa [singleDerivIndex_toList] using
        hU (singleDerivIndex n i)
    exact (hasWeakDerivativeOn_congr_ae
      (n := n) (Ω := Ω) (α := [i])
      (w1TopMultiplierAmbient_base_apply_ae
        (n := n) (Ω := Ω) A U)
      (w1TopMultiplierAmbient_singleDeriv_apply_ae
        (n := n) (Ω := Ω) A U i)).2
        (A.hasWeakDerivativeOn_mul_W1Top_first hΩopen i
          (U (baseIndex n 1)) (U (singleDerivIndex n i)) hweak)

/-- Multiplication by a fixed `W^{1,∞}` coefficient as a continuous linear
endomorphism of `W^{1,2}(Ω)`. -/
noncomputable def w1TopMultiplierCLM
    (hΩopen : IsOpen Ω) (A : W^{1,∞}(Ω)) :
    W^{1,2}(Ω) →L[ℝ] W^{1,2}(Ω) :=
  ContinuousLinearMap.codRestrict
    ((w1TopMultiplierAmbient (n := n) (Ω := Ω) A).comp
      (Submodule.subtypeL (wkpSubmoduleOn n 1 2 Ω)))
    (wkpSubmoduleOn n 1 2 Ω)
    (fun U ↦ w1TopMultiplierAmbient_mapsIsWkpOn
      (n := n) (Ω := Ω) hΩopen A U U.property)

/-- Coercing the graph-space multiplier to the ambient derivative bundle
recovers the coordinatewise ambient multiplier. -/
@[simp]
theorem w1TopMultiplierCLM_apply_coe
    (hΩopen : IsOpen Ω) (A : W^{1,∞}(Ω))
    (U : W^{1,2}(Ω)) :
    ((w1TopMultiplierCLM (n := n) (Ω := Ω) hΩopen A U :
        W^{1,2}(Ω)) : WkpAmbientOn n 1 2 Ω) =
      w1TopMultiplierAmbient (n := n) (Ω := Ω) A U :=
  rfl

/-- Quantitative graph-norm estimate for the bounded first-order
multiplier. -/
theorem norm_w1TopMultiplierCLM_apply_le
    (hΩopen : IsOpen Ω) (A : W^{1,∞}(Ω))
    (U : W^{1,2}(Ω)) :
    ‖w1TopMultiplierCLM (n := n) (Ω := Ω) hΩopen A U‖ ≤
      w1TopMultiplierNormBound n * ‖A‖ * ‖U‖ := by
  change
    ‖((w1TopMultiplierCLM (n := n) (Ω := Ω) hΩopen A U :
        W^{1,2}(Ω)) : WkpAmbientOn n 1 2 Ω)‖ ≤
      w1TopMultiplierNormBound n * ‖A‖ * ‖U‖
  rw [w1TopMultiplierCLM_apply_coe]
  exact norm_w1TopMultiplierAmbient_le (n := n) (Ω := Ω) A U

/-- Operator-norm estimate for multiplication by a fixed `W^{1,∞}`
coefficient on `W^{1,2}`. -/
theorem norm_w1TopMultiplierCLM_le
    (hΩopen : IsOpen Ω) (A : W^{1,∞}(Ω)) :
    ‖w1TopMultiplierCLM (n := n) (Ω := Ω) hΩopen A‖ ≤
      w1TopMultiplierNormBound n * ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg w1TopMultiplierNormBound_nonneg (norm_nonneg A)) ?_
  intro U
  simpa [mul_assoc] using
    norm_w1TopMultiplierCLM_apply_le
      (n := n) (Ω := Ω) hΩopen A U

/-- First-order Sobolev multiplication as a bilinear map, before the operator
norm bound is attached. -/
noncomputable def w1TopMultiplicationLinearMap
    (hΩopen : IsOpen Ω) :
    W^{1,∞}(Ω) →ₗ[ℝ]
      W^{1,2}(Ω) →ₗ[ℝ] W^{1,2}(Ω) :=
  LinearMap.mk₂ ℝ
    (fun A U ↦ w1TopMultiplierCLM (n := n) (Ω := Ω) hΩopen A U)
    (by
      intro A B U
      apply Subtype.ext
      exact w1TopMultiplierAmbient_add_left
        (n := n) (Ω := Ω) A B (U : WkpAmbientOn n 1 2 Ω))
    (by
      intro c A U
      apply Subtype.ext
      exact w1TopMultiplierAmbient_smul_left
        (n := n) (Ω := Ω) c A (U : WkpAmbientOn n 1 2 Ω))
    (by
      intro A U V
      exact (w1TopMultiplierCLM
        (n := n) (Ω := Ω) hΩopen A).map_add U V)
    (by
      intro c A U
      exact (w1TopMultiplierCLM
        (n := n) (Ω := Ω) hΩopen A).map_smul c U)

/-- First-order Sobolev multiplication as a bounded bilinear map
`W^{1,∞}(Ω) →L[ℝ] W^{1,2}(Ω) →L[ℝ] W^{1,2}(Ω)`. -/
noncomputable def w1TopMultiplicationCLM
    (hΩopen : IsOpen Ω) :
    W^{1,∞}(Ω) →L[ℝ]
      W^{1,2}(Ω) →L[ℝ] W^{1,2}(Ω) :=
  (w1TopMultiplicationLinearMap (n := n) (Ω := Ω) hΩopen).mkContinuous₂
    (w1TopMultiplierNormBound n)
    (norm_w1TopMultiplierCLM_apply_le (n := n) (Ω := Ω) hΩopen)

/-- The bounded bilinear multiplication map agrees with the fixed-coefficient
multiplier. -/
@[simp]
theorem w1TopMultiplicationCLM_apply
    (hΩopen : IsOpen Ω) (A : W^{1,∞}(Ω))
    (U : W^{1,2}(Ω)) :
    w1TopMultiplicationCLM (n := n) (Ω := Ω) hΩopen A U =
      w1TopMultiplierCLM (n := n) (Ω := Ω) hΩopen A U :=
  rfl

section BilinearOperatorNorm

-- Naming these two inferred structures avoids an expensive nested typeclass
-- search when Lean equips the curried bilinear map with its operator norm.
/-- The standard seminormed additive structure on first-order Sobolev
endomorphisms, named locally to keep nested typeclass search bounded. -/
local instance w1EndomorphismSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (W^{1,2}(Ω) →L[ℝ] W^{1,2}(Ω)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- The standard real normed-space structure on first-order Sobolev
endomorphisms, named locally to keep nested typeclass search bounded. -/
local instance w1EndomorphismNormedSpace :
    NormedSpace ℝ
      (W^{1,2}(Ω) →L[ℝ] W^{1,2}(Ω)) :=
  ContinuousLinearMap.toNormedSpace

/-- Operator-norm estimate for first-order Sobolev multiplication viewed as a
bounded bilinear map. -/
theorem norm_w1TopMultiplicationCLM_le
    (hΩopen : IsOpen Ω) :
    ‖w1TopMultiplicationCLM (n := n) (Ω := Ω) hΩopen‖ ≤
      w1TopMultiplierNormBound n :=
  LinearMap.mkContinuous₂_norm_le _
    w1TopMultiplierNormBound_nonneg _

end BilinearOperatorNorm

/-- The base representative of the bounded multiplier is the pointwise
product `Au` almost everywhere. -/
theorem w1TopMultiplierCLM_base_ae
    (hΩopen : IsOpen Ω) (A : W^{1,∞}(Ω))
    (U : W^{1,2}(Ω)) :
    baseRepresentative
        (w1TopMultiplierCLM (n := n) (Ω := Ω) hΩopen A U)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ baseRepresentative A x * baseRepresentative U x := by
  simpa only [baseRepresentative, w1TopMultiplierCLM_apply_coe] using
    w1TopMultiplierAmbient_base_apply_ae
      (n := n) (Ω := Ω) A (U : WkpAmbientOn n 1 2 Ω)

/-- The product of a `W^{1,∞}` coefficient and a `W^{1,2}` field has a
canonical realization in `W^{1,2}`. -/
theorem WkpSpaceOn.exists_mul_W1Top_W1Two
    (hΩopen : IsOpen Ω)
    (A : W^{1,∞}(Ω))
    (U : W^{1,2}(Ω)) :
    ∃ V : W^{1,2}(Ω),
      baseRepresentative V =ᵐ[domainMeasure n Ω]
        fun x ↦ baseRepresentative A x * baseRepresentative U x := by
  refine ⟨w1TopMultiplierCLM (n := n) (Ω := Ω) hΩopen A U, ?_⟩
  exact w1TopMultiplierCLM_base_ae
    (n := n) (Ω := Ω) hΩopen A U

/-- Every first-derivative coordinate of the bounded multiplier satisfies the
weak Leibniz formula almost everywhere. -/
theorem w1TopMultiplierCLM_singleDeriv_apply_ae
    (hΩopen : IsOpen Ω) (A : W^{1,∞}(Ω))
    (U : W^{1,2}(Ω)) (i : Fin n) :
    ((((w1TopMultiplierCLM (n := n) (Ω := Ω) hΩopen A U :
        W^{1,2}(Ω)) : WkpAmbientOn n 1 2 Ω)
        (singleDerivIndex n i) : DerivLp n 2 Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦
          (((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
            DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
              (((U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i) :
                DerivLp n 2 Ω) : ℝ^n → ℝ) x +
          (((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) :
            DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
              (((U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) :
                DerivLp n 2 Ω) : ℝ^n → ℝ) x := by
  exact w1TopMultiplierAmbient_singleDeriv_apply_ae
    (n := n) (Ω := Ω) A (U : WkpAmbientOn n 1 2 Ω) i

end SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- The weak derivative commutator with a matrix multiplier is controlled by the
coefficient derivatives and the component L2 energy. Spatial directions and component
indices are combined only in Mathlib's finite product index type. -/
theorem abs_sum_inner_w1TopMultiplier_derivative_commutator_le
    {ι : Type*} [Fintype ι]
    (A : Fin n → ι → ι → W^{1,∞}(ℝ^n))
    (U : Fin n → ι → W^{1,2}(ℝ^n)) :
    |∑ l, ∑ p, ∑ j, ∑ q,
      ⟪((w1TopMultiplierCLM isOpen_univ (A j p q) (U j q) :
          WkpAmbientOn n 1 2 univ) (singleDerivIndex n l)) -
        ((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          ((U j q : WkpAmbientOn n 1 2 univ) (singleDerivIndex n l)),
        ((U l p : WkpAmbientOn n 1 2 univ) (baseIndex n 1))⟫_ℝ| ≤
      (∑ l, ∑ p, ∑ j, ∑ q,
        ‖(A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖) *
      (∑ l, ∑ p, ‖(U l p : WkpAmbientOn n 1 2 univ) (baseIndex n 1)‖ ^ 2) := by
  classical
  simp only [w1TopMultiplierCLM_apply_coe, w1TopMultiplierAmbient_singleDeriv,
    add_sub_cancel_left]
  simpa only [Fintype.sum_prod_type] using
    MeasureTheory.Lp.abs_sum_inner_lpSMul_le
      (fun a b : Fin n × ι ↦
        (A b.1 a.2 b.2 : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n a.1))
      (fun a : Fin n × ι ↦ (U a.1 a.2 : WkpAmbientOn n 1 2 univ) (baseIndex n 1))

end SobolevSpace.GraphSpace
