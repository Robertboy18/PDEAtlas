/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Continuous linear maps on finite products

The usual finite product carries a maximum norm. This estimate converts an
operator bound for that norm into a bound for the sum of squared coordinate
norms. Coordinatewise continuous linear maps act on `PiLp` products, with
their product topology. On scalar products, the images of the coordinate
unit vectors also give an explicit operator-norm bound. Both index sets may be empty.
-/

@[expose] public noncomputable section

namespace ContinuousLinearMap

open scoped ENNReal

/-- Coordinatewise continuous linear maps on a `PiLp` product, obtained by transporting
the product map through Mathlib's equivalence with the plain product. -/
def piLpMap {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*}
    {E F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    (p : ℝ≥0∞) (A : ∀ i, E i →L[𝕜] F i) :
    PiLp p E →L[𝕜] PiLp p F :=
  (PiLp.continuousLinearEquiv p 𝕜 F).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ (A i).comp (PiLp.proj p E i))

/-- The coordinatewise map applies the specified map in each coordinate. -/
@[simp]
theorem piLpMap_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*}
    {E F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    (p : ℝ≥0∞) (A : ∀ i, E i →L[𝕜] F i)
    (u : PiLp p E) (i : ι) :
    piLpMap p A u i = A i (u i) :=
  rfl

/-- A finite family of compact maps with a common domain gives a compact product map. -/
theorem isCompactOperator_pi
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Finite ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    (A : ∀ i, E →L[𝕜] F i) (hA : ∀ i, IsCompactOperator (A i)) :
    IsCompactOperator (ContinuousLinearMap.pi A) := by
  let := Fintype.ofFinite ι
  classical
  have hsum : ContinuousLinearMap.pi A =
      ∑ i, (ContinuousLinearMap.single 𝕜 F i).comp (A i) := by
    ext v i
    simp
  change ContinuousLinearMap.pi A ∈ compactOperator (RingHom.id 𝕜) E (∀ i, F i)
  rw [hsum]
  apply Submodule.sum_mem
  intro i _
  exact (hA i).clm_comp (ContinuousLinearMap.single 𝕜 F i)

/-- A finite product of compact coordinate maps is compact for every `PiLp`
product norm. The choice of norm does not change the finite product topology. -/
theorem isCompactOperator_piLpMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Finite ι]
    {E F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    (p : ℝ≥0∞) (A : ∀ i, E i →L[𝕜] F i) (hA : ∀ i, IsCompactOperator (A i)) :
    IsCompactOperator (piLpMap p A) := by
  let := Fintype.ofFinite ι
  classical
  have hsum : ContinuousLinearMap.piMap A =
      ∑ i, (ContinuousLinearMap.single 𝕜 F i).comp ((A i).comp (ContinuousLinearMap.proj i)) := by
    ext v i
    simp [ContinuousLinearMap.piMap]
  have hplain : IsCompactOperator (ContinuousLinearMap.piMap A) := by
    change ContinuousLinearMap.piMap A ∈ compactOperator (RingHom.id 𝕜) (∀ i, E i) (∀ i, F i)
    rw [hsum]
    apply Submodule.sum_mem
    intro i _
    exact ((hA i).comp_clm (ContinuousLinearMap.proj i)).clm_comp
      (ContinuousLinearMap.single 𝕜 F i)
  have hmap : piLpMap p A = (PiLp.continuousLinearEquiv p 𝕜 F).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.piMap A).comp
        (PiLp.continuousLinearEquiv p 𝕜 E).toContinuousLinearMap) := by
    ext v i
    rfl
  rw [hmap]
  exact (hplain.comp_clm (PiLp.continuousLinearEquiv p 𝕜 E).toContinuousLinearMap).clm_comp
    (PiLp.continuousLinearEquiv p 𝕜 F).symm.toContinuousLinearMap

/-- The images of the coordinate unit vectors bound an operator on a finite scalar
product with its maximum norm. This includes the empty product. -/
theorem norm_le_sum_norm_apply_pi_single
    {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (L : (ι → 𝕜) →L[𝕜] F) :
    ‖L‖ ≤ ∑ i, ‖L (Pi.single i 1)‖ := by
  classical
  apply L.opNorm_le_bound (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)
  intro x
  have hx : (∑ i : ι, x i • Pi.single i (1 : 𝕜)) = x := by
    ext j
    simp [Pi.single_apply]
  calc
    ‖L x‖ = ‖∑ i : ι, x i • L (Pi.single i 1)‖ := by
      conv_lhs => rw [← hx, map_sum]
      simp only [map_smul]
    _ ≤ ∑ i : ι, ‖x i • L (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : ι, ‖L (Pi.single i 1)‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i : ι, ‖L (Pi.single i 1)‖) * ‖x‖ := by rw [Finset.sum_mul]

/-- An operator bounded for the finite product norms also controls the quadratic
coordinate energy, with a factor equal to the number of output coordinates. -/
theorem sum_norm_sq_apply_le {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {E : ι → Type*} {F : κ → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [∀ j, SeminormedAddCommGroup (F j)] [∀ j, NormedSpace 𝕜 (F j)]
    (A : (∀ i, E i) →L[𝕜] (∀ j, F j)) (x : ∀ i, E i) :
    (∑ j, ‖A x j‖ ^ 2) ≤ (Fintype.card κ : ℝ) * ‖A‖ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
  have hx : ‖x‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
    have hnorm : ‖x‖ ≤ ‖WithLp.toLp 2 x‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
        (fun i ↦ PiLp.norm_apply_le (WithLp.toLp 2 x) i)
    simpa only [PiLp.norm_sq_eq_of_L2, PiLp.toLp_apply] using
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
  have hrow (j : κ) : ‖A x j‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
    calc
      ‖A x j‖ ^ 2 ≤ (‖A‖ * ‖x‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
          ((norm_le_pi_norm (A x) j).trans (A.le_opNorm x))
      _ = ‖A‖ ^ 2 * ‖x‖ ^ 2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hx (sq_nonneg _)
  calc
    _ ≤ ∑ _j : κ, ‖A‖ ^ 2 * ∑ i, ‖x i‖ ^ 2 :=
      Finset.sum_le_sum fun j _ ↦ hrow j
    _ = _ := by simp [mul_assoc]

end ContinuousLinearMap
