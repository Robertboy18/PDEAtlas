/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Normed.Operator.EnergySpace
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Derivative
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Product

/-!
# The Sobolev spaces of real order as Banach spaces, with their bounded operators

The estimates of real order are inequalities between the energies `E_σ` on `L²`. A fixed point
argument or a Bochner integral needs Banach spaces and bounded operators instead. The space is
already there: Mathlib's Bessel potential space `H^σ(ℝⁿ)`, a Hilbert space. For `σ ≥ 0` its `L²`
representative `toL2Fun` realizes it as the space of finite energy `E_σ`, in the sense of
`PDE.Analysis.IsEnergySpace`, and the same holds for finite families with the Hilbert sum
`HsFamily ι n σ`. Every energy estimate then gives a bounded operator, with the square root of
its constant as a bound for the norm: here the inclusions, the weak derivatives and the
multiplication above the critical order. Negative orders are not covered, since there `H^σ` is
not a space of `L²` functions, and neither is the multiplication of families, which is a finite
sum of `mulCLM`. Two comparisons are not proved: that `derivCLM [i]` is `lineDerivCLM` in the
direction of the `i`-th coordinate followed by an inclusion (this needs the weak derivative of
the representative of a distributional derivative), and that the map
`BesselPotentialSpace.euclideanTuple` from tuples of elements of `H^σ(ℝⁿ)` into Mathlib's space
`H^σ(ℝⁿ, ℂ^m)` of vector-valued data is an isometric isomorphism, which would make that space
another model of `HsFamily (Fin m) n σ`.

## Main results

* `isEnergySpace_toL2Fun`, `isEnergySpace_toL2`: for `σ ≥ 0`, `H^σ(ℝⁿ)` and `HsFamily ι n σ` are
  the spaces of finite energy `E_σ`.
* `inclusion` (`0 ≤ τ ≤ σ`): the inclusion `HsFamily ι n σ → HsFamily ι n τ`, of norm at most one;
  `inclusion_apply`: in every component it is `inclCLM`.
* `derivCLM` (all words `α`, `0 ≤ τ` and `τ + |α| ≤ σ`): the weak derivative
  `∂^α : H^σ(ℝⁿ) → H^τ(ℝⁿ)`, of norm at most `(2π)^{|α|}`.
* `mulCLM` (`σ > n/2`): the multiplication `H^σ(ℝⁿ) × H^σ(ℝⁿ) → H^σ(ℝⁿ)`, bounded and bilinear, of
  norm at most `√(4^{σ+1} c)` with `c = wienerConst n σ`.
* `eLpNorm_toL2Fun_le` (`σ > n/2`, `2 ≤ q ≤ ∞`): `‖u‖_q ≤ (1 + √c) ‖u‖_{H^σ}`.

## How it works

`besselEnergy_toL2Fun` and `exists_toL2Fun_eq_of_besselEnergy_lt_top` say that `toL2Fun` is an
energy space. Then `IsEnergySpace.exists_clm` and `IsEnergySpace.exists_clm₂` turn an energy
bound for a linear or bilinear map on the `L²` representatives into a bounded operator. The
derivative comes from `besselEnergy_le_of_hasComplexWeakDerivativeOn`, the multiplication from
`besselEnergy_mul_le_mul`, and the inclusion from `besselEnergy_mono`; the inclusion has the same
`L²` representative as `inclCLM` (`toL2Fun_inclLinear`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter FourierTransform BesselPotentialSpace TemperedDistribution
open PDE.Analysis
open scoped ENNReal NNReal BesselPotentialSpace SchwartzMap

namespace SobolevSpace.Fractional

variable {n : ℕ} {σ τ : ℝ}

/-! ## Scalar functions -/

/-- **`H^σ(ℝⁿ)` is the space of finite energy of order `σ`**, for `σ ≥ 0`: the `L²`
representative of `u` has energy `‖u‖²`, and every `L²` function of finite energy is a
representative. -/
theorem isEnergySpace_toL2Fun (hσ : 0 ≤ σ) :
    IsEnergySpace (fun g : Lp ℂ 2 (volume : Measure (ℝ^n)) ↦ besselEnergy σ (fun _ : Unit ↦ g))
      (toL2FunLinear n hσ) where
  energy_apply u := besselEnergy_toL2Fun hσ u
  exists_apply_eq g h := exists_toL2Fun_eq_of_besselEnergy_lt_top hσ g h

/-- The energy of order `τ ≤ σ` of the representative of `u ∈ H^σ` is at most `‖u‖²`. -/
theorem besselEnergy_toL2Fun_le (hσ : 0 ≤ σ) (hτσ : τ ≤ σ) (u : H^{σ}(ℝ^n)) :
    besselEnergy τ (fun _ : Unit ↦ toL2Fun hσ u) ≤ ENNReal.ofReal (‖u‖ ^ 2) :=
  (besselEnergy_mono hτσ _).trans_eq (besselEnergy_toL2Fun hσ u)

/-! ## Finite families -/

section Family

variable {ι : Type*} [Fintype ι]

/-- **The Sobolev space `H^σ(ℝⁿ; ℂ^ι)` of real order**: finite families of elements of
`H^σ(ℝⁿ)`, with the Hilbert norm `‖u‖² = ∑ⱼ ‖u j‖²`. -/
abbrev HsFamily (ι : Type*) (n : ℕ) (σ : ℝ) : Type _ := PiLp 2 (fun _ : ι ↦ H^{σ}(ℝ^n))

/-- The family of `L²` representatives of an element of `H^σ(ℝⁿ; ℂ^ι)`, `σ ≥ 0`. -/
def toL2 (ι : Type*) [Fintype ι] (n : ℕ) (hσ : 0 ≤ σ) :
    HsFamily ι n σ →ₗ[ℂ] (ι → Lp ℂ 2 (volume : Measure (ℝ^n))) where
  toFun u j := toL2Fun hσ (u j)
  map_add' u v := funext fun j ↦ toL2Fun_add hσ (u j) (v j)
  map_smul' c u := funext fun j ↦ toL2Fun_smul hσ c (u j)

/-- The representatives of a family, member by member. -/
@[simp] theorem toL2_apply (hσ : 0 ≤ σ) (u : HsFamily ι n σ) (j : ι) :
    toL2 ι n hσ u j = toL2Fun hσ (u j) := rfl

/-- **`H^σ(ℝⁿ; ℂ^ι)` is the space of finite energy of order `σ`**, for `σ ≥ 0`: the family of
representatives of `u` has energy `‖u‖²`, and every family of `L²` functions of finite energy is
a family of representatives. -/
theorem isEnergySpace_toL2 (hσ : 0 ≤ σ) : IsEnergySpace (besselEnergy σ) (toL2 ι n hσ) where
  energy_apply u := by
    rw [besselEnergy_eq_sum, PiLp.norm_sq_eq_of_L2,
      ENNReal.ofReal_sum_of_nonneg fun j _ ↦ sq_nonneg _]
    exact Finset.sum_congr rfl fun j _ ↦ besselEnergy_toL2Fun hσ (u j)
  exists_apply_eq f h := by
    rw [besselEnergy_eq_sum] at h
    have hj (j : ι) : besselEnergy σ (fun _ : Unit ↦ f j) < ⊤ :=
      lt_of_le_of_lt (Finset.single_le_sum
        (f := fun j ↦ besselEnergy σ (fun _ : Unit ↦ f j)) (fun _ _ ↦ zero_le)
        (Finset.mem_univ j)) h
    choose u hu using fun j ↦ exists_toL2Fun_eq_of_besselEnergy_lt_top hσ (f j) (hj j)
    exact ⟨WithLp.toLp 2 u, funext hu⟩

/-- **The inclusion `H^σ(ℝⁿ; ℂ^ι) → H^τ(ℝⁿ; ℂ^ι)`** for `0 ≤ τ ≤ σ`. -/
def inclusion (ι : Type*) [Fintype ι] (n : ℕ) (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) :
    HsFamily ι n σ →L[ℂ] HsFamily ι n τ :=
  (isEnergySpace_toL2 (hτ.trans hτσ)).lift (isEnergySpace_toL2 hτ) LinearMap.id 1
    fun u ↦ by simpa using besselEnergy_mono hτσ (toL2 ι n (hτ.trans hτσ) u)

/-- The inclusion does not change the representatives. -/
@[simp] theorem toL2_inclusion (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) (u : HsFamily ι n σ) :
    toL2 ι n hτ (inclusion ι n hτ hτσ u) = toL2 ι n (hτ.trans hτσ) u :=
  (isEnergySpace_toL2 (hτ.trans hτσ)).apply_lift (isEnergySpace_toL2 hτ) LinearMap.id 1 _ u

/-- The inclusion has norm at most one. -/
theorem norm_inclusion_le (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) :
    ‖inclusion ι n (σ := σ) hτ hτσ‖ ≤ 1 := by
  have h := (isEnergySpace_toL2 (ι := ι) (n := n) (hτ.trans hτσ)).norm_lift_le
    (isEnergySpace_toL2 hτ) LinearMap.id 1
    fun u ↦ by simpa using besselEnergy_mono hτσ (toL2 ι n (hτ.trans hτσ) u)
  rwa [NNReal.sqrt_one, NNReal.coe_one] at h

/-- **The inclusion of families is the inclusion `inclCLM` in every component**: the two have
the same `L²` representative (`toL2Fun_inclLinear`). -/
theorem inclusion_apply (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) (u : HsFamily ι n σ) (j : ι) :
    inclusion ι n hτ hτσ u j = inclCLM n hτσ (u j) := by
  apply (isEnergySpace_toL2Fun hτ).injective
  change toL2Fun hτ (inclusion ι n hτ hτσ u j) = toL2Fun hτ (inclCLM n hτσ (u j))
  rw [inclCLM_apply, toL2Fun_inclLinear hτσ hτ (hτ.trans hτσ)]
  exact congrFun (toL2_inclusion hτ hτσ u) j

end Family

/-! ## The derivative -/

/-- **The derivative `∂^α` is bounded from `H^σ(ℝⁿ)` to `H^τ(ℝⁿ)`** when `τ + |α| ≤ σ`, with
norm at most `(2π)^{|α|}`: there is a bounded operator `G` such that the representative of `G u`
is the weak derivative `∂^α` of the representative of `u`. -/
theorem exists_derivCLM (α : List (Fin n)) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ)
    (hστ : τ + α.length ≤ σ) :
    ∃ G : H^{σ}(ℝ^n) →L[ℂ] H^{τ}(ℝ^n),
      (∀ u, HasComplexWeakDerivativeOn univ α (toL2Fun hσ u) (toL2Fun hτ (G u))) ∧
        ‖G‖ ≤ (2 * Real.pi) ^ α.length := by
  have hk : (α.length : ℝ) ≤ σ := by linarith
  -- the weak derivative of every representative
  choose v hv using fun u : H^{σ}(ℝ^n) ↦
    exists_hasComplexWeakDerivativeOn_of_besselEnergy_lt_top α (toL2Fun hσ u)
      ((besselEnergy_toL2Fun_le hσ hk u).trans_lt ENNReal.ofReal_lt_top)
  let G₀ : H^{σ}(ℝ^n) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (ℝ^n)) :=
    { toFun := v
      map_add' := fun u u' ↦ by
        have h := hv (u + u')
        rw [toL2Fun_add] at h
        exact h.unique_L2 ((hv u).add_L2 (hv u'))
      map_smul' := fun c u ↦ by
        have h := hv (c • u)
        rw [toL2Fun_smul] at h
        exact h.unique_L2 ((hv u).smul_L2 c) }
  -- its energy
  set c : ℝ≥0 := (2 * NNReal.pi) ^ α.length with hc
  have hcoe : ((c ^ 2 : ℝ≥0) : ℝ) = (2 * Real.pi) ^ (2 * α.length) := by
    rw [hc]
    push_cast [NNReal.coe_real_pi]
    ring
  have hbound (u : H^{σ}(ℝ^n)) : besselEnergy τ (fun _ : Unit ↦ G₀ u) ≤
      (c ^ 2 : ℝ≥0) * ENNReal.ofReal (‖u‖ ^ 2) := by
    rw [← ENNReal.ofReal_coe_nnreal, hcoe]
    exact (besselEnergy_le_of_hasComplexWeakDerivativeOn τ α _ _ (hv u)).trans
      (mul_le_mul' le_rfl (besselEnergy_toL2Fun_le hσ hστ u))
  obtain ⟨G, hG, hnorm⟩ := (isEnergySpace_toL2Fun hτ).exists_clm G₀ hbound
  refine ⟨G, fun u ↦ ?_, ?_⟩
  · have h := hG u
    rw [toL2FunLinear_apply] at h
    rw [h]
    exact hv u
  · rw [NNReal.sqrt_sq] at hnorm
    simpa [hc] using hnorm

/-- **The derivative `∂^α : H^σ(ℝⁿ) → H^τ(ℝⁿ)`**, for `0 ≤ τ` and `τ + |α| ≤ σ`. -/
def derivCLM (α : List (Fin n)) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hστ : τ + α.length ≤ σ) :
    H^{σ}(ℝ^n) →L[ℂ] H^{τ}(ℝ^n) :=
  Classical.choose (exists_derivCLM α hσ hτ hστ)

/-- The representative of `derivCLM α u` is the weak derivative `∂^α` of the representative of
`u`. -/
theorem hasComplexWeakDerivativeOn_derivCLM (α : List (Fin n)) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ)
    (hστ : τ + α.length ≤ σ) (u : H^{σ}(ℝ^n)) :
    HasComplexWeakDerivativeOn univ α (toL2Fun hσ u) (toL2Fun hτ (derivCLM α hσ hτ hστ u)) :=
  (Classical.choose_spec (exists_derivCLM α hσ hτ hστ)).1 u

/-- The derivative has norm at most `(2π)^{|α|}`. -/
theorem norm_derivCLM_le (α : List (Fin n)) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ)
    (hστ : τ + α.length ≤ σ) : ‖derivCLM α hσ hτ hστ‖ ≤ (2 * Real.pi) ^ α.length :=
  (Classical.choose_spec (exists_derivCLM α hσ hτ hστ)).2

/-! ## The multiplication -/

/-- **`H^σ(ℝⁿ)` is a Banach algebra for `σ > n/2`, up to a constant**: there is a bounded
bilinear operator `G` on `H^σ` such that the representative of `G u v` is the product of the
representatives, with `‖G‖ ≤ √(4^{σ+1} c)`, `c = wienerConst n σ`. -/
theorem exists_mulCLM (hσ0 : 0 ≤ σ) (hσ : (n : ℝ) < 2 * σ) :
    ∃ G : H^{σ}(ℝ^n) →L[ℂ] H^{σ}(ℝ^n) →L[ℂ] H^{σ}(ℝ^n),
      (∀ u v, (toL2Fun hσ0 (G u v) : ℝ^n → ℂ) =ᵐ[volume]
        fun x ↦ toL2Fun hσ0 u x * toL2Fun hσ0 v x) ∧
        ‖G‖ ≤ √(4 ^ (σ + 1) * (wienerConst n σ).toReal) := by
  have hfin (u : H^{σ}(ℝ^n)) : besselEnergy σ (fun _ : Unit ↦ toL2Fun hσ0 u) < ⊤ := by
    rw [besselEnergy_toL2Fun]
    exact ENNReal.ofReal_lt_top
  -- the product of the representatives, in `L²`
  choose p hp using fun u v : H^{σ}(ℝ^n) ↦
    exists_ae_eq_mul hσ (toL2Fun hσ0 u) (toL2Fun hσ0 v) (hfin u)
  let B : H^{σ}(ℝ^n) →ₗ[ℂ] H^{σ}(ℝ^n) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (ℝ^n)) :=
    LinearMap.mk₂ ℂ p
      (fun u u' v ↦ Lp.ext (by
        filter_upwards [hp (u + u') v, hp u v, hp u' v, Lp.coeFn_add (p u v) (p u' v),
          Lp.coeFn_add (toL2Fun hσ0 u) (toL2Fun hσ0 u')] with x h1 h2 h3 h4 h5
        rw [h1, h4, Pi.add_apply, h2, h3, toL2Fun_add, h5, Pi.add_apply, add_mul]))
      (fun c u v ↦ Lp.ext (by
        filter_upwards [hp (c • u) v, hp u v, Lp.coeFn_smul c (p u v),
          Lp.coeFn_smul c (toL2Fun hσ0 u)] with x h1 h2 h3 h4
        rw [h1, h3, Pi.smul_apply, h2, toL2Fun_smul, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          mul_assoc]))
      (fun u v v' ↦ Lp.ext (by
        filter_upwards [hp u (v + v'), hp u v, hp u v', Lp.coeFn_add (p u v) (p u v'),
          Lp.coeFn_add (toL2Fun hσ0 v) (toL2Fun hσ0 v')] with x h1 h2 h3 h4 h5
        rw [h1, h4, Pi.add_apply, h2, h3, toL2Fun_add, h5, Pi.add_apply, mul_add]))
      (fun c u v ↦ Lp.ext (by
        filter_upwards [hp u (c • v), hp u v, Lp.coeFn_smul c (p u v),
          Lp.coeFn_smul c (toL2Fun hσ0 v)] with x h1 h2 h3 h4
        rw [h1, h3, Pi.smul_apply, h2, toL2Fun_smul, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          mul_left_comm]))
  -- the algebra property
  set C : ℝ≥0 := (4 ^ (σ + 1) * (wienerConst n σ).toReal).toNNReal with hC
  have hCcoe : (C : ℝ≥0∞) = ENNReal.ofReal (4 ^ (σ + 1)) * wienerConst n σ := by
    rw [hC, ← ENNReal.ofReal, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_toReal (wienerConst_lt_top hσ).ne]
  have hbound (u v : H^{σ}(ℝ^n)) : besselEnergy σ (fun _ : Unit ↦ B u v) ≤
      C * (ENNReal.ofReal (‖u‖ ^ 2) * ENNReal.ofReal (‖v‖ ^ 2)) := by
    rw [hCcoe, ← besselEnergy_toL2Fun hσ0 u, ← besselEnergy_toL2Fun hσ0 v]
    exact besselEnergy_mul_le_mul hσ _ _ _ (hp u v)
  obtain ⟨G, hG, hnorm⟩ := (isEnergySpace_toL2Fun hσ0).exists_clm₂ B hbound
  refine ⟨G, fun u v ↦ ?_, ?_⟩
  · have h := hG u v
    rw [toL2FunLinear_apply] at h
    rw [h]
    exact hp u v
  · refine hnorm.trans_eq ?_
    rw [hC, Real.coe_sqrt, Real.coe_toNNReal _ (by positivity)]

/-- **The multiplication on `H^σ(ℝⁿ)`, `σ > n/2`**, as a bounded bilinear operator. -/
def mulCLM (hσ0 : 0 ≤ σ) (hσ : (n : ℝ) < 2 * σ) :
    H^{σ}(ℝ^n) →L[ℂ] H^{σ}(ℝ^n) →L[ℂ] H^{σ}(ℝ^n) :=
  Classical.choose (exists_mulCLM hσ0 hσ)

/-- The representative of `mulCLM u v` is the product of the representatives. -/
theorem toL2Fun_mulCLM (hσ0 : 0 ≤ σ) (hσ : (n : ℝ) < 2 * σ) (u v : H^{σ}(ℝ^n)) :
    (toL2Fun hσ0 (mulCLM hσ0 hσ u v) : ℝ^n → ℂ) =ᵐ[volume]
      fun x ↦ toL2Fun hσ0 u x * toL2Fun hσ0 v x :=
  (Classical.choose_spec (exists_mulCLM hσ0 hσ)).1 u v

/-- The multiplication has norm at most `√(4^{σ+1} c)`, `c = wienerConst n σ`. -/
theorem norm_mulCLM_le (hσ0 : 0 ≤ σ) (hσ : (n : ℝ) < 2 * σ) :
    ‖mulCLM hσ0 hσ‖ ≤ √(4 ^ (σ + 1) * (wienerConst n σ).toReal) :=
  (Classical.choose_spec (exists_mulCLM hσ0 hσ)).2

/-! ## The embedding into `L^q` -/

/-- **The Sobolev embedding `H^σ(ℝⁿ) ⊂ L^q(ℝⁿ)` above the critical order**: for `σ > n/2` and
`2 ≤ q ≤ ∞`, `‖u‖_q ≤ (1 + √c) ‖u‖_{H^σ}` with `c = wienerConst n σ`. -/
theorem eLpNorm_toL2Fun_le (hσ0 : 0 ≤ σ) (hσ : (n : ℝ) < 2 * σ) (u : H^{σ}(ℝ^n))
    {q : ℝ≥0∞} (hq : 2 ≤ q) :
    eLpNorm (toL2Fun hσ0 u) q volume ≤
      (1 + wienerConst n σ ^ (1 / 2 : ℝ)) * ENNReal.ofReal ‖u‖ := by
  refine (eLpNorm_le_of_two_le hσ (toL2Fun hσ0 u) hq).trans_eq ?_
  rw [besselEnergy_toL2Fun, ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
    ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

end SobolevSpace.Fractional
