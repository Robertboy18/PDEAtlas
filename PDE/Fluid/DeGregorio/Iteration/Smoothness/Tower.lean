/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Smoothness.Step
public import PDE.Fluid.DeGregorio.Iteration.Picard.CoupledShapeRepresentative
public import PDE.Fluid.DeGregorio.Characteristics
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.SmoothData

/-!
# Towers of derivative graphs

For a coupled De Gregorio output `w` on `[0, T]` with H² graphs `W`, a derivative tower of height
`n ≥ 1` is a family `q 0, q 1, …, q n` of bounded strongly measurable H² families such that the
first weak derivative of `q j` is `q (j + 1)` for `j < n`, and the representative of the top
family `q n` satisfies, along the characteristics,

  `q n (X a t) = q n (a, 0) + ∫₀ᵗ (B (q 0, q n) + (1 - n) B (q n, q 0) + F_n) (X a s) ds`,

where `B (A, Q) = A H Q` and `F_n` is given by `forcingList n`. That `q 0 = W` represents the
vorticity is recorded separately. The integrand `levelSource q n` is meant for `n ≥ 1`; at order
zero the stretching identity `IsHkFrozenOutput.integral_eq_source` has the integrand `B (W, W)`.

## Main results

* `levelSource`, `IsDerivTower`: the integrand of the `n`-th identity and the towers.
* `IsHkFrozenOutput.integral_eq_source`: the stretching identity along the characteristics.
* `IsHkFrozenOutput.coefficient_eq_realHilbertH1`: the coefficient is the Hilbert transform.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology Sobolev ContDiff
open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

variable {T : ℝ}

/-- The integrand of the characteristic identity of the `n`-th derivative graph `q n` of the
vorticity graph `q 0`, for `n ≥ 1`: `B (q 0, q n) + (1 - n) B (q n, q 0) + F_n`. -/
def levelSource (q : ℕ → Icc (0 : ℝ) T → W^{2,2}(ℝ^1)) (n : ℕ) (t : Icc (0 : ℝ) T) :
    W^{2,2}(ℝ^1) :=
  firstDerivativeSourceH2CLM (q 0 t) (q n t) +
    (1 - (n : ℝ)) • firstDerivativeSourceH2CLM (q n t) (q 0 t) +
      sourceSum (fun j ↦ q j t) (forcingList n)

/-- A derivative tower of height `n ≥ 1`: `q 0, …, q n` are bounded strongly measurable H²
families, the weak derivative of `q j` is `q (j + 1)` for `j < n`, and the top family `q n`
satisfies its characteristic identity along `X`. -/
structure IsDerivTower (hT : 0 ≤ T) (X : ℝ → ℝ → ℝ)
    (q : ℕ → Icc (0 : ℝ) T → W^{2,2}(ℝ^1)) (n : ℕ) : Prop where
  /-- Each graph family is strongly measurable. -/
  measurable : ∀ j ≤ n, StronglyMeasurable (q j)
  /-- The graph families have a common bound. -/
  bounded : ∃ C, ∀ j ≤ n, ∀ t, ‖q j t‖ ≤ C
  /-- Each graph is the weak derivative of the previous one. -/
  deriv_eq : ∀ j < n, ∀ t, ∂[0] (q j t) = lowerOrderCLM (by decide : 1 ≤ 2) (q (j + 1) t)
  /-- The top graph satisfies its characteristic identity. -/
  integral_eq : ∀ a (t : Icc (0 : ℝ) T),
    realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (q n t)) (X a t) =
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (q n ⟨0, le_rfl, hT⟩)) a +
        ∫ s in 0..(t : ℝ), realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2)
          (levelSource q n (projIcc 0 T hT s))) (X a s)

/-- Combinations of measurable graph families are measurable. -/
theorem stronglyMeasurable_sourceSum {q : ℕ → Icc (0 : ℝ) T → W^{2,2}(ℝ^1)}
    {l : List (ℕ × ℕ × ℝ)}
    (hq : ∀ e ∈ l, StronglyMeasurable (q e.1) ∧ StronglyMeasurable (q e.2.1)) :
    StronglyMeasurable (fun t ↦ sourceSum (fun j ↦ q j t) l) := by
  induction l with
  | nil => simpa using stronglyMeasurable_const
  | cons e l ih =>
    simp only [sourceSum_cons]
    have he := hq e (by simp)
    exact ((firstDerivativeSourceH2CLM.continuous₂.comp_stronglyMeasurable
      (he.1.prodMk he.2)).const_smul e.2.2).add (ih fun e' he' ↦ hq e' (by simp [he']))

/-- Combinations of bounded graph families are bounded. -/
theorem exists_norm_sourceSum_le {q : ℕ → Icc (0 : ℝ) T → W^{2,2}(ℝ^1)}
    {l : List (ℕ × ℕ × ℝ)} {C : ℝ}
    (hq : ∀ e ∈ l, ∀ t, ‖q e.1 t‖ ≤ C ∧ ‖q e.2.1 t‖ ≤ C) :
    ∃ D, ∀ t, ‖sourceSum (fun j ↦ q j t) l‖ ≤ D := by
  induction l with
  | nil => exact ⟨0, fun t ↦ by simp⟩
  | cons e l ih =>
    obtain ⟨D, hD⟩ := ih fun e' he' ↦ hq e' (by simp [he'])
    refine ⟨|e.2.2| * (36 * succOrderAssemblyNormBound 1 1 * C * C) + D, fun t ↦ ?_⟩
    simp only [sourceSum_cons]
    have he := hq e (by simp) t
    have hk : 0 ≤ 36 * succOrderAssemblyNormBound 1 1 :=
      mul_nonneg (by norm_num) succOrderAssemblyNormBound_nonneg
    apply (norm_add_le _ _).trans
    gcongr
    · rw [norm_smul, Real.norm_eq_abs]
      gcongr
      apply (norm_firstDerivativeSourceH2CLM_apply_le _ _).trans
      have hC : 0 ≤ C := (norm_nonneg _).trans he.1
      gcongr
      · exact he.1
      · exact he.2
    · exact hD t

variable {B : NNReal} {R : ℝ} {hT : 0 ≤ T}
  {F : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
  {W₀ : W^{2,2}(ℝ^1)} {w₀ : ℝ → ℝ} {c w X Y : ℝ → ℝ → ℝ}

/-- The stretching identity along the characteristics, written with the graphs `W` of the
output: `w (X a t) t = w a 0 + ∫₀ᵗ (w H w) (X a s) s ds`. -/
theorem IsHkFrozenOutput.integral_eq_source
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) (hchar : HkCharacteristics hT F c X Y)
    {W : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)}
    (hWrep : ∀ t, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) =
      fun x ↦ w x t)
    (hc : ∀ (t : Icc (0 : ℝ) T) x, c x t =
      realLineRepresentative (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) (W t))) x)
    (a : ℝ) (t : Icc (0 : ℝ) T) :
    realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) (X a t) =
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W ⟨0, le_rfl, hT⟩)) a +
        ∫ s in 0..(t : ℝ), realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2)
          (firstDerivativeSourceH2CLM (W (projIcc 0 T hT s)) (W (projIcc 0 T hT s)))) (X a s) := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right t.property.2
  have hpath : ContinuousOn (fun s ↦ (X a s, s)) (Icc 0 T) := by
    refine ContinuousOn.prodMk ?_ continuousOn_id
    rw [continuousOn_iff_continuous_domRestrict]
    exact hchar.flow_continuous.comp (continuous_const.prodMk continuous_id)
  have hwc : ContinuousOn (fun s ↦ w (X a s) s) (Icc 0 T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact h.continuous.comp
      ((hchar.flow_continuous.comp (continuous_const.prodMk continuous_id)).prodMk continuous_id)
  have hcc : ContinuousOn (fun s ↦ c (X a s) s) (Icc 0 T) :=
    h.coefficient_continuous.comp_continuousOn hpath
  have hderiv (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) t) :
      HasDerivAt (fun r ↦ w (X a r) r) (c (X a s) s * w (X a s) s) s := by
    have hsT : s ∈ Ioo (0 : ℝ) T := ⟨hs.1, hs.2.trans_le t.property.2⟩
    have hd := hasDerivAt_vorticity_characteristic (fields := ⟨w, hkCurveHilbertVelocity hT F⟩)
      h.isClassicalSolutionOn.regularity h.isClassicalSolutionOn.transport hsT
      (by simpa only [one_mul] using hchar.flow_derivative a s (Ioo_subset_Icc_self hsT))
    rwa [(h.velocity_derivative (X a s) s).deriv] at hd
  have hint : IntervalIntegrable (fun s ↦ c (X a s) s * w (X a s) s) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le t.property.1]
    exact (hcc.mul hwc).mono hsub
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    (hwc.mono hsub) hderiv hint
  rw [hWrep, hWrep]
  have hcongr : ∫ s in 0..(t : ℝ), realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2)
      (firstDerivativeSourceH2CLM (W (projIcc 0 T hT s)) (W (projIcc 0 T hT s)))) (X a s) =
      ∫ s in 0..(t : ℝ), c (X a s) s * w (X a s) s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    have hsI : s ∈ Icc (0 : ℝ) T := hsub hs
    simp only [realLineRepresentative_firstDerivativeSourceH2CLM, hWrep, projIcc_of_mem hT hsI]
    rw [← hc ⟨s, hsI⟩]
    ring
  simp only at hftc ⊢
  rw [hcongr, hftc, hchar.flow_initial]
  ring

/-- The coefficient of a coupled output is the continuous Hilbert transform of its graphs. -/
theorem IsHkFrozenOutput.coefficient_eq_realHilbertH1
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) {W : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)}
    (hWbase : ∀ t, wkpBaseCoordinateCLM (W t) = (F t).val) (t : Icc (0 : ℝ) T) (x : ℝ) :
    c x t = realLineRepresentative (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) (W t))) x := by
  have hp := h.hilbert_pair t
  rw [projIcc_val] at hp
  have hq := isHilbertPair_realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) (W t))
  rw [realLineCoordinateCLM_base_lowerOrder, hWbase] at hq
  have hae := hp.ae_eq_right hq
  have hcont : Continuous (fun y ↦ c y t) :=
    h.coefficient_continuous.comp (continuous_id.prodMk continuous_const)
  exact congrFun ((Continuous.ae_eq_iff_eq volume hcont
    (continuous_realLineRepresentative _)).mp hae) x

end DeGregorio.Iteration
