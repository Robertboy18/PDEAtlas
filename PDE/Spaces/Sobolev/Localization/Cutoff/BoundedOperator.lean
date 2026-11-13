/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HigherOrder.Cutoff
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Quantitative bounds for cutoff extension at every Sobolev exponent

For open sets `V ⊆ Ω`, multiplication by a smooth cutoff compactly supported in
`V`, followed by extension by zero, is bounded from `W^{k,p}(V)` to `W^{k,p}(Ω)`.
The order may be zero and the exponent may be either endpoint `1` or `∞`.

We give an explicit bound for `cutoffExtensionCLM` and identify its exact weak
Leibniz representatives. The bound is the finite `ℓᵖ`
norm of the row sums of cutoff-derivative `L∞` norms; each input derivative is
controlled by the input graph norm.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

open TopologicalSpace
open scoped Distributions ENNReal

namespace SobolevSpace.CompactSupportLocalization.HigherOrderLocalizedCutoff

open MeasureTheory Set GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The sum of the cutoff-derivative sup norms in one Leibniz row, retaining
the multiplicities of derivative-word splittings. -/
noncomputable def cutoffLeibnizRowBound (V : Set (ℝ^n))
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (α : List (Fin n)) : ℝ :=
  ((derivativeSplits α).map fun split ↦
    (eLpNorm (iteratedPartialDeriv (n := n) split.1 ψ.toFun) ∞
      (domainMeasure n V)).toReal).sum

/-- Each Leibniz row bound is nonnegative. -/
theorem cutoffLeibnizRowBound_nonneg (V : Set (ℝ^n))
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (α : List (Fin n)) :
    0 ≤ cutoffLeibnizRowBound V ψ α := by
  exact List.sum_nonneg fun r hr ↦ by
    obtain ⟨split, _, rfl⟩ := List.mem_map.mp hr
    exact ENNReal.toReal_nonneg

/-- Every word coordinate is bounded by the Sobolev graph norm. -/
theorem eLpNorm_wkpWordRepresentative_toReal_le {V : Set (ℝ^n)}
    (U : W^{k,p}(V)) (α : List (Fin n)) (hα : α.length ≤ k) :
    (eLpNorm (wkpWordRepresentative U α) p (domainMeasure n V)).toReal ≤ ‖U‖ := by
  simp only [wkpWordRepresentative, dite_eq_left hα]
  exact PiLp.norm_apply_le U.val _

/-- The finite Leibniz estimate separates the cutoff coefficients from the
norm of the input, uniformly over all Sobolev exponents. -/
theorem cutoffLeibnizENormBound_toReal_le {V : Set (ℝ^n)}
    (U : W^{k,p}(V)) (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (α : List (Fin n)) (hα : α.length ≤ k) :
    (cutoffLeibnizENormBound U ψ α).toReal ≤ cutoffLeibnizRowBound V ψ α * ‖U‖ := by
  let A (split : List (Fin n) × List (Fin n)) :=
    eLpNorm (iteratedPartialDeriv (n := n) split.1 ψ.toFun) ∞ (domainMeasure n V)
  let B (split : List (Fin n) × List (Fin n)) :=
    eLpNorm (wkpWordRepresentative U split.2) p (domainMeasure n V)
  have hsum (splits : List (List (Fin n) × List (Fin n)))
      (hsplits : ∀ split ∈ splits, split.2.length ≤ k) :
      ((splits.map fun split ↦ A split * B split).sum).toReal ≤
        (splits.map fun split ↦ (A split).toReal).sum * ‖U‖ := by
    induction splits with
    | nil => simp
    | cons split rest ih =>
        simp only [List.map_cons, List.sum_cons]
        calc
          _ ≤ (A split * B split).toReal +
              ((rest.map fun q ↦ A q * B q).sum).toReal := ENNReal.toReal_add_le
          _ ≤ (A split).toReal * ‖U‖ +
              (rest.map fun q ↦ (A q).toReal).sum * ‖U‖ := by
            apply add_le_add
            · rw [ENNReal.toReal_mul]
              exact mul_le_mul_of_nonneg_left
                (eLpNorm_wkpWordRepresentative_toReal_le U split.2
                  (hsplits split (by simp))) ENNReal.toReal_nonneg
            · exact ih fun q hq ↦ hsplits q (by simp [hq])
          _ = _ := (add_mul _ _ _).symm
  apply hsum
  intro split hsplit
  have := derivativeSplits_length hsplit
  omega

/-- The finite `ℓᵖ` norm of all Leibniz row bounds. At `p = ∞` this is
their maximum; no restriction on the Sobolev order is needed. -/
noncomputable def cutoffExtensionNormBound (k : ℕ) (p : ℝ≥0∞)
    (V : Set (ℝ^n)) (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : ℝ :=
  ‖WithLp.toLp p fun a : DerivIndex n k ↦ cutoffLeibnizRowBound V ψ a.toList.reverse‖

/-- The cutoff extension bound is nonnegative. -/
theorem cutoffExtensionNormBound_nonneg (V : Set (ℝ^n))
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    0 ≤ cutoffExtensionNormBound k p V ψ :=
  norm_nonneg _

/-- The graph norm of cutoff extension is bounded for every order and exponent. -/
theorem norm_extendByCutoff_le_cutoffExtensionNormBound
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}(V)) :
    ‖extendByCutoff hV hVΩ ψ hψ U‖ ≤ cutoffExtensionNormBound k p V ψ * ‖U‖ := by
  let _ : MeasurableSpace (DerivIndex n k) := ⊤
  let A : PiLp p (fun _ : DerivIndex n k ↦ ℝ) :=
    WithLp.toLp p fun a ↦ cutoffLeibnizRowBound V ψ a.toList.reverse
  have hrow (a : DerivIndex n k) :
      ‖(extendByCutoff hV hVΩ ψ hψ U).val a‖ ≤ ‖U‖ * ‖A a‖ := by
    have hα : a.toList.reverse.length ≤ k := by simpa using a.toList_length_le
    change ‖(extendByCutoff hV hVΩ ψ hψ U).val a‖ ≤
      ‖U‖ * ‖cutoffLeibnizRowBound V ψ a.toList.reverse‖
    rw [Real.norm_of_nonneg (cutoffLeibnizRowBound_nonneg V ψ a.toList.reverse), mul_comm]
    exact (norm_extendByCutoff_coordinate_le hV hVΩ ψ hψ U a).trans
      (cutoffLeibnizENormBound_toReal_le U ψ a.toList.reverse hα)
  have h := PiLp.norm_le_card_rpow_mul_of_coordinate_norm_le
    le_rfl ‖U‖ (norm_nonneg U) A (extendByCutoff hV hVΩ ψ hψ U).val hrow
  change ‖(extendByCutoff hV hVΩ ψ hψ U).val‖ ≤ ‖A‖ * ‖U‖
  simpa only [sub_self, ENNReal.rpow_zero, ENNReal.toReal_one, one_mul,
    mul_comm] using h

end SobolevSpace.CompactSupportLocalization.HigherOrderLocalizedCutoff

namespace SobolevSpace.Extension.HigherOrder

open MeasureTheory Set GraphSpace
open CompactSupportLocalization.HigherOrderLocalizedCutoff

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The bounded operator evaluates to the canonical extension `extendByCutoff`. -/
@[simp]
theorem cutoffExtensionCLM_apply
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}(V)) :
    cutoffExtensionCLM hV hΩ hVΩ ψ hψ U = extendByCutoff hV hVΩ ψ hψ U :=
  rfl

/-- The operator norm is bounded by the finite jet of cutoff sup norms. -/
theorem norm_cutoffExtensionCLM_le
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V) :
    ‖cutoffExtensionCLM (k := k) (p := p) hV hΩ hVΩ ψ hψ‖ ≤
      cutoffExtensionNormBound k p V ψ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (cutoffExtensionNormBound_nonneg (k := k) (p := p) V ψ)
  exact norm_extendByCutoff_le_cutoffExtensionNormBound hV hVΩ ψ hψ

/-- The base representative of the bounded extension is the literal cutoff product. -/
theorem cutoffExtensionCLM_base_ae
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}(V)) :
    baseRepresentative (cutoffExtensionCLM hV hΩ hVΩ ψ hψ U)
      =ᵐ[domainMeasure n Ω] fun x ↦ ψ.toFun x * baseRepresentative U x :=
  extendByCutoff_base_ae hV hVΩ ψ hψ U

/-- Every derivative row of the bounded extension is the original weak Leibniz
expansion, including the base row when `k = 0`. -/
theorem cutoffExtensionCLM_coordinate_ae
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}(V)) (a : DerivIndex n k) :
    ⇑((cutoffExtensionCLM hV hΩ hVΩ ψ hψ U).val a)
      =ᵐ[domainMeasure n Ω]
        weakLeibnizExpansion ψ.toFun (wkpWordRepresentative U) a.toList.reverse :=
  extendByCutoff_coordinate_ae hV hVΩ ψ hψ U a

/-- The bounded operator retains the finer input-dependent Leibniz bound on each row. -/
theorem norm_cutoffExtensionCLM_coordinate_le
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}(V)) (a : DerivIndex n k) :
    ‖(cutoffExtensionCLM hV hΩ hVΩ ψ hψ U).val a‖ ≤
      (cutoffLeibnizENormBound U ψ a.toList.reverse).toReal :=
  norm_extendByCutoff_coordinate_le hV hVΩ ψ hψ U a

/-- At positive order and exponent two, the general operator agrees with the
Hilbert-space operator `extendByCutoffCLM`, so the bounds proved for it apply. -/
theorem cutoffExtensionCLM_eq_extendByCutoffCLM
    {V Ω : Set (ℝ^n)} (hk : 0 < k)
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V) :
    cutoffExtensionCLM (k := k) (p := 2) hV hΩ hVΩ ψ hψ =
      extendByCutoffCLM hk hV hΩ hVΩ ψ hψ := by
  ext U
  rfl

end SobolevSpace.Extension.HigherOrder
