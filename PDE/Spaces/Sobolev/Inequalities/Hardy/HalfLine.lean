/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Hardy.Weighted
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.HigherOrder
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import PDE.Spaces.Sobolev.Inequalities.Hardy.Classical -- shake: keep

/-!
# Completed Hardy operators on the positive half-line

The weighted Hardy chain of `Hardy.Weighted` bounds `‖u / x^j‖_{L²(0,∞)}` by the `L²` norm of
the `j`-th derivative for smooth `u` compactly supported in `(0, ∞)`. Here that
estimate becomes a bounded linear operator on the completed zero-trace space
`Wk0SpaceOn 1 j (HalfSpace.upper 1)`, the closure of the smooth test core in `W^{j,2}`.

The one-dimensional lemmas are about functions `ℝ → ℝ`, while the Sobolev spaces live on
`ℝ^1`, the one-dimensional Euclidean space. The first lemmas pull a test function back along
`PiLp.equivOfUnique` and check that smoothness, compact support, and support in `(0, ∞)`
survive. The quotient `u ↦ u / x^j` is then a linear map from the test core into `L²(ℝ)`, bounded
by `2^j` times the `W^{j,2}` graph norm, and `LinearMap.extendOfNorm` extends it to the
completion. The sharper constant `4^j / ∏ (2l-1)²`, with only the top derivative coordinate on
the right, holds on the core and passes to the completion because both sides are continuous.

## Main results

* `iteratedHardyTestQuotientLp`, `iteratedHardyTestQuotientLinear`: `u / x^j` on the test core.
* `iteratedHardyTestQuotientLinear_bound_sq`: the chain inequality on the core in `L²`-norm form.
* `norm_iteratedDeriv_pullback_eq_testFunctionToWk_top_coordinate`: the `L²` norm of the `j`-th
  derivative of the pullback equals the norm of the top coordinate of the Sobolev bundle.
* `iteratedHardyWk0Quotient`: the bounded extension to `Wk0SpaceOn 1 j (HalfSpace.upper 1)`.
* `iterated_weighted_hardy_Wk0`: the completed inequality
  `∏_{l=1}^{j} (2l-1)² ‖u / x^j‖² ≤ 4^j ‖∂^j u‖²`, with the same constant as on the core.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace


namespace Hardy

open Set MeasureTheory
open scoped ENNReal Sobolev



/-- A test function on the upper half-line, pulled back to `ℝ`, has
topological support inside `(0,∞)`. -/
theorem testFunctionOn_positiveHalfLine_comp_tsupport
    (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    tsupport
        (φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) ⊆
      Set.Ioi (0 : ℝ) := by
  intro t ht
  have htpre := tsupport_comp_subset_preimage φ.1.toFun
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.continuous ht
  have htΩ := φ.2 htpre
  exact htΩ

/-- The pullback of a half-line test function to `ℝ` is smooth. -/
theorem testFunctionOn_positiveHalfLine_comp_contDiff
    (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) :=
  φ.1.contDiff.comp (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.contDiff

/-- The pullback of a half-line test function to `ℝ` has compact support, because
`PiLp.equivOfUnique` is a homeomorphism. -/
theorem testFunctionOn_positiveHalfLine_comp_hasCompactSupport
    (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    HasCompactSupport (φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) :=
  φ.1.hasCompactSupport.comp_homeomorph
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.toHomeomorph

/-- The order-`j` Hardy quotient on the positive-half-line test core. -/
noncomputable def iteratedHardyTestQuotientLp
    (j : ℕ) (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    Lp ℝ 2 (volume : Measure ℝ) :=
  let u : ℝ → ℝ := φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  (memLp_div_pow_of_hasCompactSupport j
    (testFunctionOn_positiveHalfLine_comp_contDiff φ).continuous
    (testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ)
    (testFunctionOn_positiveHalfLine_comp_tsupport φ)).toLp
      (fun r ↦ u r / r ^ j)

/-- The order-`j` test quotient is represented almost everywhere by literal
division by the `j`th power of the positive half-line coordinate. -/
theorem iteratedHardyTestQuotientLp_apply_ae
    (j : ℕ) (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    ((iteratedHardyTestQuotientLp j φ : Lp ℝ 2
      (volume : Measure ℝ)) : ℝ → ℝ) =ᵐ[volume]
        fun r ↦ φ.1.toFun ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm r) / r ^ j := by
  exact (memLp_div_pow_of_hasCompactSupport j
    (testFunctionOn_positiveHalfLine_comp_contDiff φ).continuous
    (testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ)
    (testFunctionOn_positiveHalfLine_comp_tsupport φ)).coeFn_toLp

/-- Linearity of the arbitrary-order quotient on the smooth test core. -/
noncomputable def iteratedHardyTestQuotientLinear (j : ℕ) :
    GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure ℝ) where
  toFun := iteratedHardyTestQuotientLp j
  map_add' := by
    intro φ ψ
    apply Lp.ext
    filter_upwards [iteratedHardyTestQuotientLp_apply_ae j (φ + ψ),
      iteratedHardyTestQuotientLp_apply_ae j φ,
      iteratedHardyTestQuotientLp_apply_ae j ψ,
      Lp.coeFn_add (iteratedHardyTestQuotientLp j φ)
        (iteratedHardyTestQuotientLp j ψ)] with r hrs hrφ hrψ hradd
    rw [hrs, hradd]
    simp only [Pi.add_apply]
    rw [hrφ, hrψ]
    change
      (φ.1.toFun ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm r) +
          ψ.1.toFun ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm r)) / r ^ j = _
    ring
  map_smul' := by
    intro c φ
    apply Lp.ext
    filter_upwards [iteratedHardyTestQuotientLp_apply_ae j (c • φ),
      iteratedHardyTestQuotientLp_apply_ae j φ,
      Lp.coeFn_smul ((RingHom.id ℝ) c)
        (iteratedHardyTestQuotientLp j φ)] with r hrs hrφ hrsmul
    rw [hrs, hrsmul]
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [hrφ]
    change (c * φ.1.toFun ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm r)) / r ^ j = _
    ring

private theorem div_pow_sq_eq_mul_rpow (j : ℕ) (u x : ℝ) (hx : 0 < x) :
    (u / x ^ j) ^ 2 = u ^ 2 * x ^ (-2 * (j : ℝ)) := by
  have hexp : (-2 : ℝ) * (j : ℝ) = -((2 * j : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_neg hx.le, Real.rpow_natCast]
  field_simp [pow_ne_zero _ hx.ne']
  ring

/-- Exact compact-core Hardy chain expressed as an `L²` quotient norm on the
left and the ordinary top derivative norm on the right. -/
theorem iteratedHardyTestQuotientLinear_bound_sq
    (j : ℕ) (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    let u : ℝ → ℝ := φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
    let hd : MemLp (iteratedDeriv j u) 2 volume :=
      ((testFunctionOn_positiveHalfLine_comp_contDiff φ).continuous_iteratedDeriv
        j (WithTop.coe_le_coe.mpr le_top)).memLp_of_hasCompactSupport
          ((testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ).of_isClosed_subset
            (isClosed_tsupport _)
            (tsupport_iteratedDeriv_subset j _))
    (∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2) *
        ‖iteratedHardyTestQuotientLinear j φ‖ ^ 2 ≤
      (4 : ℝ) ^ j * ‖hd.toLp (iteratedDeriv j u)‖ ^ 2 := by
  dsimp only
  let u : ℝ → ℝ := φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  let hq := memLp_div_pow_of_hasCompactSupport j
    (testFunctionOn_positiveHalfLine_comp_contDiff φ).continuous
    (testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ)
    (testFunctionOn_positiveHalfLine_comp_tsupport φ)
  let hd : MemLp (iteratedDeriv j u) 2 volume :=
    ((testFunctionOn_positiveHalfLine_comp_contDiff φ).continuous_iteratedDeriv
      j (WithTop.coe_le_coe.mpr le_top)).memLp_of_hasCompactSupport
        ((testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ).of_isClosed_subset
          (isClosed_tsupport _)
          (tsupport_iteratedDeriv_subset j _))
  have hqSq := norm_toLp_two_sq_eq_integral_sq hq
  have hdSq := norm_toLp_two_sq_eq_integral_sq hd
  have hqIntegral :
      (∫ x : ℝ, (u x / x ^ j) ^ 2) =
        ∫ x in Set.Ioi (0 : ℝ), u x ^ 2 * x ^ (-2 * (j : ℝ)) := by
    calc
      (∫ x : ℝ, (u x / x ^ j) ^ 2) =
          ∫ x in Set.Ioi (0 : ℝ), (u x / x ^ j) ^ 2 := by
        apply integral_sq_eq_integral_Ioi_of_tsupport_subset
        apply (closure_minimal ?_ (isClosed_tsupport u)).trans
          (testFunctionOn_positiveHalfLine_comp_tsupport φ)
        intro x hx
        apply subset_tsupport u
        intro hux
        exact hx (by simp [hux])
      _ = ∫ x in Set.Ioi (0 : ℝ),
          u x ^ 2 * x ^ (-2 * (j : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact div_pow_sq_eq_mul_rpow j (u x) x hx
  have hdIntegral :
      (∫ x : ℝ, (iteratedDeriv j u x) ^ 2) =
        ∫ x in Set.Ioi (0 : ℝ), (iteratedDeriv j u x) ^ 2 :=
    integral_sq_eq_integral_Ioi_of_tsupport_subset
      ((tsupport_iteratedDeriv_subset j u).trans
        (testFunctionOn_positiveHalfLine_comp_tsupport φ))
  have hHardy := iterated_weighted_hardy_Ioi_nat_of_hasCompactSupport
    j 0 ((testFunctionOn_positiveHalfLine_comp_contDiff φ).of_le
      (WithTop.coe_le_coe.mpr le_top))
    (testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ)
    (testFunctionOn_positiveHalfLine_comp_tsupport φ)
  change (∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2) *
      ‖hq.toLp (fun x ↦ u x / x ^ j)‖ ^ 2 ≤
    (4 : ℝ) ^ j * ‖hd.toLp (iteratedDeriv j u)‖ ^ 2
  rw [hqSq, hdSq, hqIntegral, hdIntegral]
  simpa [u, Nat.zero_add] using hHardy

/-- The ordinary top derivative after one-dimensional pullback has exactly
the norm of the top coordinate in the smooth `W^{j,2}` bundle. -/
theorem norm_iteratedDeriv_pullback_eq_testFunctionToWk_top_coordinate
    (j : ℕ) (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    let u : ℝ → ℝ := φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
    let hd : MemLp (iteratedDeriv j u) 2 volume :=
      ((testFunctionOn_positiveHalfLine_comp_contDiff φ).continuous_iteratedDeriv
        j (WithTop.coe_le_coe.mpr le_top)).memLp_of_hasCompactSupport
          ((testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ).of_isClosed_subset
            (isClosed_tsupport _) (tsupport_iteratedDeriv_subset j _))
    ‖hd.toLp (iteratedDeriv j u)‖ =
      ‖((GraphSpace.testFunctionToWk (n := 1) (k := j)
          (Ω := (HalfSpace.upper 1)) φ :
            GraphSpace.WkpAmbientOn 1 j 2 (HalfSpace.upper 1))
        (GraphSpace.topDerivIndexOne j))‖ := by
  dsimp only
  let d : ℝ^1 → ℝ := fun x ↦ iteratedPartialDeriv (n := 1)
    (List.replicate j (0 : Fin 1)) φ.1.toFun x
  have hdcont : Continuous d :=
    (PDE.contDiff_top_iteratedPartialDeriv (n := 1) φ.1.contDiff
      (List.replicate j (0 : Fin 1))).continuous
  have hdsupp : Function.support d ⊆ (HalfSpace.upper 1) :=
    (subset_tsupport d).trans
      ((tsupport_iteratedPartialDeriv_subset_tsupport
        (n := 1) (α := List.replicate j (0 : Fin 1))
        (f := φ.1.toFun)).trans φ.2)
  have heLp :
      eLpNorm (iteratedDeriv j
          (φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm)) 2
          (volume : Measure ℝ) =
        eLpNorm d 2 (domainMeasure 1 (HalfSpace.upper 1)) := by
    calc
      eLpNorm (iteratedDeriv j
          (φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm)) 2
          (volume : Measure ℝ) =
          eLpNorm (d ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) 2
            (volume : Measure ℝ) := by
        apply eLpNorm_congr_ae
        filter_upwards [] with t
        exact PDE.iteratedDeriv_comp_equivOfUnique_symm
          j φ.1.toFun (φ.1.contDiff.of_le (by exact_mod_cast le_top)) t
      _ = eLpNorm d 2 (volume : Measure (ℝ^1)) :=
        eLpNorm_comp_measurePreserving hdcont.aestronglyMeasurable
          ((PiLp.volume_preserving_toLp (Fin 1)).comp
            ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _))
      _ = eLpNorm d 2 (domainMeasure 1 (HalfSpace.upper 1)) := by
        simpa [domainMeasure] using
          (eLpNorm_restrict_eq_of_support_subset
            (p := (2 : ℝ≥0∞)) (f := d) hdcont.aestronglyMeasurable hdsupp).symm
  rw [Lp.norm_toLp,
    GraphSpace.norm_testFunctionToWk_top_coordinate_one_eq_eLpNorm_toReal]
  exact congrArg ENNReal.toReal heLp

/-- A convenient full-`W^{j,2}` bound used to construct the completed
quotient operator.  Density later restores the sharper product of odd
squares; no constant is lost in the final theorem. -/
theorem iteratedHardyTestQuotientLinear_bound
    (j : ℕ) (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    ‖iteratedHardyTestQuotientLinear j φ‖ ≤
      (2 : ℝ) ^ j *
        ‖GraphSpace.testFunctionToWk0 (n := 1) (k := j)
          (Ω := (HalfSpace.upper 1)) φ‖ := by
  let u : ℝ → ℝ := φ.1.toFun ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  let hd : MemLp (iteratedDeriv j u) 2 volume :=
    ((testFunctionOn_positiveHalfLine_comp_contDiff φ).continuous_iteratedDeriv
      j (WithTop.coe_le_coe.mpr le_top)).memLp_of_hasCompactSupport
        ((testFunctionOn_positiveHalfLine_comp_hasCompactSupport φ).of_isClosed_subset
          (isClosed_tsupport _) (tsupport_iteratedDeriv_subset j _))
  have hsq := iteratedHardyTestQuotientLinear_bound_sq j φ
  have htop : ‖hd.toLp (iteratedDeriv j u)‖ =
      ‖((GraphSpace.testFunctionToWk (n := 1) (k := j)
          (Ω := (HalfSpace.upper 1)) φ :
            GraphSpace.WkpAmbientOn 1 j 2 (HalfSpace.upper 1))
        (GraphSpace.topDerivIndexOne j))‖ :=
    norm_iteratedDeriv_pullback_eq_testFunctionToWk_top_coordinate j φ
  dsimp only at hsq
  rw [htop] at hsq
  have hprod :
      1 ≤ ∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2 := by
    apply Finset.one_le_prod₀
    intro l hl
    have hlone : (1 : ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.mp hl).1
    nlinarith [sq_nonneg (2 * (l : ℝ) - 1)]
  have hsq' :
      ‖iteratedHardyTestQuotientLinear j φ‖ ^ 2 ≤
        (4 : ℝ) ^ j *
          ‖((GraphSpace.testFunctionToWk (n := 1) (k := j)
              (Ω := (HalfSpace.upper 1)) φ :
                GraphSpace.WkpAmbientOn 1 j 2 (HalfSpace.upper 1))
            (GraphSpace.topDerivIndexOne j))‖ ^ 2 := by
    nlinarith [sq_nonneg ‖iteratedHardyTestQuotientLinear j φ‖]
  have hpow : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    calc
      ((2 : ℝ) ^ j) ^ 2 = (2 : ℝ) ^ (j * 2) := (pow_mul _ _ _).symm
      _ = (2 : ℝ) ^ (2 * j) := by rw [Nat.mul_comm]
      _ = ((2 : ℝ) ^ 2) ^ j := pow_mul _ _ _
      _ = (4 : ℝ) ^ j := by norm_num
  have hnormTop :
      ‖iteratedHardyTestQuotientLinear j φ‖ ≤
        (2 : ℝ) ^ j *
          ‖((GraphSpace.testFunctionToWk (n := 1) (k := j)
              (Ω := (HalfSpace.upper 1)) φ :
                GraphSpace.WkpAmbientOn 1 j 2 (HalfSpace.upper 1))
            (GraphSpace.topDerivIndexOne j))‖ := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (by positivity) (norm_nonneg _))).mp
    rw [mul_pow, hpow]
    exact hsq'
  calc
    ‖iteratedHardyTestQuotientLinear j φ‖ ≤
        (2 : ℝ) ^ j *
          ‖((GraphSpace.testFunctionToWk (n := 1) (k := j)
              (Ω := (HalfSpace.upper 1)) φ :
                GraphSpace.WkpAmbientOn 1 j 2 (HalfSpace.upper 1))
            (GraphSpace.topDerivIndexOne j))‖ := hnormTop
    _ ≤ (2 : ℝ) ^ j *
        ‖GraphSpace.testFunctionToWk0 (n := 1) (k := j)
          (Ω := (HalfSpace.upper 1)) φ‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [GraphSpace.testFunctionToWk0_coe] using
        (PiLp.norm_apply_le
          (x := (GraphSpace.testFunctionToWk (n := 1) (k := j)
            (Ω := (HalfSpace.upper 1)) φ :
              GraphSpace.WkpAmbientOn 1 j 2 (HalfSpace.upper 1)))
          (i := GraphSpace.topDerivIndexOne j))

/-- The order-`j` Hardy quotient on the completed higher-order zero-trace
space.  It is the unique bounded extension of literal division by `r^j` on
compactly supported smooth functions. -/
noncomputable def iteratedHardyWk0Quotient (j : ℕ) :
    W₀^{j,2}((HalfSpace.upper 1)) →L[ℝ]
      Lp ℝ 2 (volume : Measure ℝ) :=
  (iteratedHardyTestQuotientLinear j).extendOfNorm
    (GraphSpace.testFunctionToWk0Linear (n := 1) (k := j)
      (Ω := (HalfSpace.upper 1)))

/-- The completed operator agrees with literal division on every test
function. -/
theorem iteratedHardyWk0Quotient_testFunction
    (j : ℕ) (φ : GraphSpace.TestFunctionOn 1 (HalfSpace.upper 1)) :
    iteratedHardyWk0Quotient j
        (GraphSpace.testFunctionToWk0 (n := 1) (k := j)
          (Ω := (HalfSpace.upper 1)) φ) =
      iteratedHardyTestQuotientLp j φ := by
  exact LinearMap.extendOfNorm_eq
    (GraphSpace.denseRange_testFunctionToWk0Linear
      (n := 1) (k := j) (Ω := (HalfSpace.upper 1)))
    ⟨(2 : ℝ) ^ j, iteratedHardyTestQuotientLinear_bound j⟩ φ

/-- Exact repeated Hardy inequality on the completed `W^{j,2}_0` half-line
space.  The compact-core product of odd squares survives completion exactly. -/
theorem iterated_weighted_hardy_Wk0
    (j : ℕ)
    (u : W₀^{j,2}((HalfSpace.upper 1))) :
    (∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2) *
        ‖iteratedHardyWk0Quotient j u‖ ^ 2 ≤
      (4 : ℝ) ^ j *
        ‖((((u : W^{j,2}(HalfSpace.upper 1)) :
            GraphSpace.WkpAmbientOn 1 j 2 (HalfSpace.upper 1))
          (GraphSpace.topDerivIndexOne j)))‖ ^ 2 := by
  refine DenseRange.induction_on
    (GraphSpace.denseRange_testFunctionToWk0Linear
      (n := 1) (k := j) (Ω := (HalfSpace.upper 1))) u ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro φ
    change (∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2) *
        ‖iteratedHardyWk0Quotient j
          (GraphSpace.testFunctionToWk0 (n := 1) (k := j)
            (Ω := (HalfSpace.upper 1)) φ)‖ ^ 2 ≤ _
    rw [iteratedHardyWk0Quotient_testFunction]
    have h := iteratedHardyTestQuotientLinear_bound_sq j φ
    dsimp only at h
    rw [norm_iteratedDeriv_pullback_eq_testFunctionToWk_top_coordinate] at h
    change
      (∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2) *
          ‖iteratedHardyTestQuotientLp j φ‖ ^ 2 ≤
        (4 : ℝ) ^ j *
          ‖((GraphSpace.testFunctionToWk (n := 1) (k := j)
              (Ω := (HalfSpace.upper 1)) φ :
                GraphSpace.WkpAmbientOn 1 j 2 (HalfSpace.upper 1))
            (GraphSpace.topDerivIndexOne j))‖ ^ 2 at h
    change
      (∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2) *
          ‖iteratedHardyTestQuotientLp j φ‖ ^ 2 ≤
        (4 : ℝ) ^ j *
          ‖((GraphSpace.testFunctionToWk (n := 1) (k := j)
              (Ω := (HalfSpace.upper 1)) φ :
                GraphSpace.WkpAmbientOn 1 j 2 (HalfSpace.upper 1))
            (GraphSpace.topDerivIndexOne j))‖ ^ 2
    exact h

end Hardy

end SobolevSpace
