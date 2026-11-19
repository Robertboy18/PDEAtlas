/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.ZeroTrace.HalfSpaceCutoff
public import PDE.Spaces.Sobolev.Approximation.ZeroTrace.Translation
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent

/-!
# Interior approximation of a Sobolev zero extension

A whole-space Sobolev function vanishing below the boundary restricts to
`W^{1,p}_0` on the upper half-space, for every finite `p ≥ 1`.

First apply a fixed normal cutoff to the whole-space approximants constructed
by mollification and compact cutoffs. Boundedness of the normal multiplier
preserves convergence, and its vanishing strip puts every approximant in the
interior test core. Then translate a zero extension upward. A suitable fixed
normal cutoff leaves each translated function unchanged. Finally let the
translation tend to zero in the Sobolev norm.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.HalfSpace

open MeasureTheory Set GraphSpace
open scoped ENNReal Topology Sobolev

variable {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Applying the normal multiplier to a smooth Sobolev element agrees with the
classical cutoff, regarded as an interior test function. -/
theorem restrict_cutoffAwayCLM_testFunction {δ : ℝ} (hδ : 0 < δ)
    (φ : TestFunctionOn n Set.univ) :
    restrictCLM (measurableSet_upper n) (subset_univ (upper n))
        (cutoffAwayCLM δ Set.univ (testFunctionToWkp (k := 1) (p := p) φ)) =
      testFunctionToWkp (k := 1) (p := p)
        ⟨Extension.GraphSpace.HalfSpace.cutoffMul (n := n) δ φ.1,
          Extension.GraphSpace.HalfSpace.tsupport_cutoffMul_subset_upper (n := n) hδ φ.1⟩ := by
  apply WkpSpaceOn.ext_of_base_ae (isOpen_upper n)
  have hres := restrictCLM_apply_ae (k := 1) (p := p)
    (measurableSet_upper n) (subset_univ (upper n))
    (cutoffAwayCLM δ Set.univ (testFunctionToWkp (k := 1) (p := p) φ))
    (baseIndex n 1)
  have hcut := cutoffAwayCLM_base_ae δ Set.univ (testFunctionToWkp (k := 1) (p := p) φ)
  have hb := testFunctionToWkp_coordinate_ae (k := 1) (p := p) φ (baseIndex n 1)
  have ht := testFunctionToWkp_coordinate_ae (k := 1) (p := p)
    (⟨Extension.GraphSpace.HalfSpace.cutoffMul (n := n) δ φ.1,
      Extension.GraphSpace.HalfSpace.tsupport_cutoffMul_subset_upper (n := n) hδ φ.1⟩ :
        TestFunctionOn n (upper n)) (baseIndex n 1)
  have hm : domainMeasure n (upper n) ≤ domainMeasure n Set.univ :=
    Measure.restrict_mono (subset_univ _) le_rfl
  filter_upwards [hres, hcut.filter_mono (ae_mono hm), hb.filter_mono (ae_mono hm), ht]
    with x hxres hxcut hxb hxt
  change _ = ((testFunctionToWkp (k := 1) (p := p) _).val (baseIndex n 1)) x
  calc
    _ = baseRepresentative
        (cutoffAwayCLM δ Set.univ (testFunctionToWkp (k := 1) (p := p) φ)) x := hxres
    _ = cutoffAway (n := n) δ x *
        baseRepresentative (testFunctionToWkp (k := 1) (p := p) φ) x := hxcut
    _ = cutoffAway (n := n) δ x * φ.1.toFun x := by
      congr 1
      simpa only [baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using hxb
    _ = _ := by
      simpa only [baseIndex_toList, iteratedPartialDeriv,
        Extension.GraphSpace.HalfSpace.cutoffMul] using hxt.symm

private theorem map_mem_Wkp0_of_global_testFunctions (hp : p ≠ ∞)
    (F : W^{1,p}(ℝ^n) →L[ℝ] W^{1,p}(upper n))
    (hF : ∀ φ : TestFunctionOn n Set.univ,
      F (testFunctionToWkp (k := 1) (p := p) φ) ∈
        (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := upper n)).toSubmodule)
    (U : W^{1,p}(ℝ^n)) :
    F U ∈
      (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := upper n)).toSubmodule := by
  have hm : Set.MapsTo F
      (Set.range (testFunctionToWkpLinear (n := n) (k := 1) (p := p) (Ω := Set.univ)))
      ((wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := upper n)).toSubmodule :
        Set (W^{1,p}(upper n))) := by
    rintro _ ⟨φ, rfl⟩
    exact hF φ
  exact hm.closure_left F.continuous
    (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := upper n)).isClosed'
    (wkpSpace_mem_Wkp0_univ hp U)

/-- A fixed cutoff away from the boundary sends any global finite-exponent
Sobolev function into the interior test-function closure on the half-space. -/
theorem restrict_cutoffAway_mem_Wkp0 (hp : p ≠ ∞) {δ : ℝ} (hδ : 0 < δ)
    (U : W^{1,p}(ℝ^n)) :
    restrictCLM (measurableSet_upper n) (subset_univ (upper n))
        (cutoffAwayCLM δ Set.univ U) ∈
      (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := upper n)).toSubmodule := by
  apply map_mem_Wkp0_of_global_testFunctions hp
    ((restrictCLM (measurableSet_upper n) (subset_univ (upper n))).comp
      (cutoffAwayCLM δ Set.univ)) ?_ U
  intro φ
  simp only [ContinuousLinearMap.comp_apply, restrict_cutoffAwayCLM_testFunction hδ φ]
  exact testFunctionToWkp_mem_Wkp0 _

/-- A global Sobolev function vanishing below the boundary restricts to
`W^{1,p}_0` on the upper half-space. No compact-support assumption is needed. -/
theorem restrict_mem_Wkp0_of_zero_below (hp : p ≠ ∞) (U : W^{1,p}(ℝ^n))
    (hU : ∀ᵐ x ∂volume, x (PDE.Common.lastIndex (n := n)) ≤ 0 →
      baseRepresentative U x = 0) :
    restrictCLM (measurableSet_upper n) (subset_univ (upper n)) U ∈
      (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := upper n)).toSubmodule := by
  let δ : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have hδpos (m : ℕ) : 0 < δ m := by dsimp [δ]; positivity
  have hδ0 : Filter.Tendsto δ Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let e : ℝ^n := EuclideanSpace.single (PDE.Common.lastIndex (n := n)) 1
  let a : ℕ → ℝ^n := fun m ↦ -(2 * δ m) • e
  have ha : Filter.Tendsto a Filter.atTop (𝓝 0) := by
    simpa only [a, mul_zero, neg_zero, zero_smul] using
      (hδ0.const_mul 2).neg.smul_const e
  let V : ℕ → W^{1,p}(ℝ^n) := fun m ↦ translateW1p hp (a m) U
  have hV (m : ℕ) : cutoffAwayCLM (δ m) Set.univ (V m) = V m := by
    apply WkpSpaceOn.ext_of_base_ae isOpen_univ
    have hc := cutoffAwayCLM_base_ae (δ m) Set.univ (V m)
    have ht := Rellich.translateLp_apply_ae p (a m) (U.val (baseIndex n 1))
    have hU' : ∀ᵐ x ∂domainMeasure n Set.univ,
        x (PDE.Common.lastIndex (n := n)) ≤ 0 → baseRepresentative U x = 0 := by
      simpa only [domainMeasure, Measure.restrict_univ] using hU
    have hz := (Rellich.translationMeasurePreserving (a m)).quasiMeasurePreserving.ae hU'
    filter_upwards [hc, ht, hz] with x hcx htx hzx
    change baseRepresentative (cutoffAwayCLM (δ m) Set.univ (V m)) x =
      baseRepresentative (V m) x
    rw [hcx]
    by_cases hx : 2 * δ m ≤ x (PDE.Common.lastIndex (n := n))
    · rw [cutoffAway_eq_one_of_two_mul_le_last (n := n) (hδpos m) hx, one_mul]
    · have hlast : (x + a m) (PDE.Common.lastIndex (n := n)) ≤ 0 := by
        simp only [a, e, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single,
          PiLp.single_apply,
          ite_true, smul_eq_mul, mul_one]
        linarith [not_le.mp hx]
      have hvzero : baseRepresentative (V m) x = 0 := by
        change (translateW1p hp (a m) U).val (baseIndex n 1) x = 0
        rw [translateW1p_apply, htx]
        exact hzx hlast
      rw [hvzero, mul_zero]
  have hmem (m : ℕ) :
      restrictCLM (measurableSet_upper n) (subset_univ (upper n)) (V m) ∈
        (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := upper n)).toSubmodule := by
    rw [← hV m]
    exact restrict_cutoffAway_mem_Wkp0 hp (hδpos m) (V m)
  apply (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := upper n)).isClosed'.mem_of_tendsto
    (((restrictCLM (measurableSet_upper n) (subset_univ (upper n))).continuous.tendsto U).comp
      (tendsto_translateW1p_zero hp U ha))
  exact Filter.Eventually.of_forall hmem

end SobolevSpace.HalfSpace
