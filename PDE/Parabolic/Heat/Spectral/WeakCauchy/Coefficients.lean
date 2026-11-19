/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
public import PDE.Parabolic.Heat.Spectral.DirichletBasis
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import CAS.ExactTactic

/-!
# Eigenfunction coefficients of weak Dirichlet heat evolutions

The integrated dual derivative supplied by Lions–Magenes can be tested against
each Dirichlet eigenfunction. The variational heat equation then gives a scalar
integral equation with a continuous right-hand side. Its exponential decay follows
without a strong time derivative in the pivot space.
-/

@[expose] public noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution MeasureTheory Set Filter
open scoped Sobolev InnerProductSpace Topology

variable {n : ℕ} {Ω : Set (ℝ^n)} (S : DirichletHeatSpectrum n Ω)

/-- Testing the Dirichlet form against an eigenfunction extracts one pivot coefficient. -/
theorem dirichletForm_eigenfunction (hopen : IsOpen Ω) (u : H¹₀(Ω)) (i : ℕ) :
    dirichletForm u (S.eigenfunction i) =
      S.eigenvalue i * inner ℝ (baseCoordCLM u) (S.basis i) := by
  rw [dirichletForm_symm]
  have h := (isWeakSolution_iff_isWeakPoissonSolution hopen _ _).2
    (S.poisson_eigenfunction i) u
  rw [loadFunctional_apply, real_inner_smul_left, real_inner_comm] at h
  exact h

/-- The dual weak derivative and variational PDE give the scalar heat integral equation.
The exceptional null set in the PDE may depend on the spatial test. -/
theorem coefficient_eq_add_integral (hopen : IsOpen Ω) {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → H¹₀(Ω)} {g : ℝ → StrongDual ℝ (H¹₀(Ω))}
    (E : ContinuousPivotEvolutionOn (h10L2GelfandTriple hopen) u g a b)
    (heq : ∀ v : H¹₀(Ω), ∀ᵐ t ∂volume.restrict (Ioc a b),
      g t v + dirichletForm (u t) v = 0)
    (i : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    inner ℝ (E.representative t) (S.basis i) =
      inner ℝ (E.representative a) (S.basis i) +
        ∫ s in a..t, -S.eigenvalue i * inner ℝ (E.representative s) (S.basis i) := by
  have hae : E.representative =ᵐ[volume.restrict (Ioc a b)]
      fun s ↦ baseCoordCLM (u s) := by
    have h := E.ae_eq_inclusion
    rw [uIcc_of_le hab] at h
    exact h.filter_mono (ae_mono (volume.restrict_mono_set Ioc_subset_Icc_self))
  have hg : (fun s ↦ g s (S.eigenfunction i)) =ᵐ[volume.restrict (Ioc a b)]
      fun s ↦ -S.eigenvalue i * inner ℝ (E.representative s) (S.basis i) := by
    filter_upwards [heq (S.eigenfunction i), hae] with s hs hes
    rw [S.dirichletForm_eigenfunction hopen, ← hes] at hs
    linarith
  have h := E.integratedDerivative.pairing_eq_add_integral (S.eigenfunction i)
    (by rwa [uIcc_of_le hab])
  rw [h10L2GelfandTriple_inclusion_apply, S.base_eigenfunction] at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le ht.1]
  exact hg.filter_mono (ae_mono (volume.restrict_mono_set
    (Ioc_subset_Ioc_right ht.2)))

/-- Individual eigenfunction coefficients are differentiable on the closed time interval,
although the pivot-valued trajectory need only have a weak dual derivative. -/
theorem hasDerivWithinAt_coefficient (hopen : IsOpen Ω) {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → H¹₀(Ω)} {g : ℝ → StrongDual ℝ (H¹₀(Ω))}
    (E : ContinuousPivotEvolutionOn (h10L2GelfandTriple hopen) u g a b)
    (heq : ∀ v : H¹₀(Ω), ∀ᵐ t ∂volume.restrict (Ioc a b),
      g t v + dirichletForm (u t) v = 0)
    (i : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s ↦ inner ℝ (E.representative s) (S.basis i))
      (-S.eigenvalue i * inner ℝ (E.representative t) (S.basis i)) (Icc a b) t := by
  have hc : ContinuousOn (fun s ↦ inner ℝ (E.representative s) (S.basis i))
      (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      E.continuousOn.inner (continuousOn_const (c := S.basis i))
  have hr : ContinuousOn
      (fun s ↦ -S.eigenvalue i * inner ℝ (E.representative s) (S.basis i)) (Icc a b) :=
    continuousOn_const.mul hc
  have hint : IntervalIntegrable
      (fun s ↦ -S.eigenvalue i * inner ℝ (E.representative s) (S.basis i)) volume a t :=
    (hr.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  let : Fact (t ∈ Icc a b) := ⟨ht⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right
    (s := Icc a b) (t := Icc a b) hint
    (hr.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hr t ht)
  exact (hd.const_add (inner ℝ (E.representative a) (S.basis i))).congr_of_mem
    (fun s hs ↦ S.coefficient_eq_add_integral hopen hab E heq i hs) ht

/-- The variational heat equation forces exponential decay of every spectral coefficient,
including both time endpoints. -/
theorem coefficient_eq_exp (hopen : IsOpen Ω) {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → H¹₀(Ω)} {g : ℝ → StrongDual ℝ (H¹₀(Ω))}
    (E : ContinuousPivotEvolutionOn (h10L2GelfandTriple hopen) u g a b)
    (heq : ∀ v : H¹₀(Ω), ∀ᵐ t ∂volume.restrict (Ioc a b),
      g t v + dirichletForm (u t) v = 0)
    (i : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    inner ℝ (E.representative t) (S.basis i) =
      Real.exp (-S.eigenvalue i * (t - a)) *
        inner ℝ (E.representative a) (S.basis i) := by
  let c : ℝ → ℝ := fun s ↦ inner ℝ (E.representative s) (S.basis i)
  let p : ℝ → ℝ := fun s ↦ Real.exp (S.eigenvalue i * (s - a)) * c s
  have hc : ContinuousOn c (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      E.continuousOn.inner (continuousOn_const (c := S.basis i))
  have hp : ContinuousOn p (Icc a b) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.mul hc
  have hdp (s : ℝ) (hs : s ∈ Ioo a b) : HasDerivAt p 0 s := by
    have hd := (S.hasDerivWithinAt_coefficient hopen hab E heq i
      (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hexp : HasDerivAt (fun r : ℝ ↦ Real.exp (S.eigenvalue i * (r - a)))
        (S.eigenvalue i * Real.exp (S.eigenvalue i * (s - a))) s := by
      cas
    convert! hexp.mul hd using 1
    ring
  have hbalance := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hp.mono (Icc_subset_Icc le_rfl ht.2))
    (fun s hs ↦ hdp s ⟨hs.1, hs.2.trans_le ht.2⟩) (intervalIntegrable_const)
  have hvalue : Real.exp (S.eigenvalue i * (t - a)) * c t = c a := by
    simpa only [intervalIntegral.integral_zero, p, sub_self, mul_zero, Real.exp_zero,
      one_mul, sub_eq_zero] using hbalance.symm
  change c t = Real.exp (-S.eigenvalue i * (t - a)) * c a
  rw [← hvalue, ← mul_assoc, ← Real.exp_add]
  have hcancel : -S.eigenvalue i * (t - a) + S.eigenvalue i * (t - a) = 0 := by cas
  rw [hcancel, Real.exp_zero, one_mul]

end HeatEquation.DirichletHeatSpectrum
