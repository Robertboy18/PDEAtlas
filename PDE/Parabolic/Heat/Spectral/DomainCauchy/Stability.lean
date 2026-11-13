/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DomainCauchy.Bounds
public import PDE.Parabolic.Heat.Spectral.DomainCauchy.Data
public import PDE.Parabolic.Heat.Spectral.DomainCauchy.TestMaximum

/-!
# Supremum contraction for continuous domain data

The maximum principle for compact smooth approximants passes to the same spectral
construction through its fixed-time pivot-to-supremum estimate. Applying the resulting
bound to a difference gives contraction for continuous zero-boundary initial data.
-/

@[expose] public noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace MeasureTheory HolderSpace Set
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {γ : Exponent}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hγ : (γ : ℝ) < 1)
  (S : DirichletHeatSpectrum n Ω)

/-- A fixed-time supremum estimate for essentially bounded pivot data follows from
spectral smoothing and the finite measure of the domain. -/
theorem norm_classicalPower_le_of_ae_bound (f : DerivLp n 2 Ω) {M t : ℝ}
    (hM : 0 ≤ M) (hf : ∀ᵐ y ∂domainMeasure n Ω, ‖f y‖ ≤ M) (ht : 0 < t)
    {x : ℝ^n} (hx : x ∈ closure Ω) :
    ‖S.classicalPower hopen hbounded hgraph hγ 0 f t x‖ ≤
      (‖dirichletHolderLiftCLM hopen hbounded hgraph hγ 2‖ *
        ((2 + n + 1).factorial : ℝ) / t ^ (2 + n + 1) *
        (measureUnivNNReal (domainMeasure n Ω) : ℝ) ^ (2 : ℝ)⁻¹) * M := by
  let : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_restrict.mpr hbounded.measure_lt_top.ne
  have h := Lp.norm_le_of_ae_bound hM hf
  calc
    _ ≤ _ := S.norm_classicalPower_le hopen hbounded hgraph hγ f ht hx
    _ ≤ _ := by
      have h' := mul_le_mul_of_nonneg_left h
        (show 0 ≤ ‖dirichletHolderLiftCLM hopen hbounded hgraph hγ 2‖ *
          ((2 + n + 1).factorial : ℝ) / t ^ (2 + n + 1) by positivity)
      simpa only [ENNReal.toReal_ofNat, mul_assoc] using h'

/-- Continuous zero-boundary data obey the maximum-principle supremum bound under
the spectral evolution. No uniform estimate or Fourier reconstruction is assumed. -/
theorem norm_classicalPower_le_of_continuousOn (f : DerivLp n 2 Ω) {g : ℝ^n → ℝ}
    (hg : ContinuousOn g (closure Ω)) (hzero : ∀ y ∈ frontier Ω, g y = 0)
    (hf : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g) {M t : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ y ∈ closure Ω, ‖g y‖ ≤ M) (ht : 0 < t)
    {x : ℝ^n} (hx : x ∈ closure Ω) :
    ‖S.classicalPower hopen hbounded hgraph hγ 0 f t x‖ ≤ M := by
  let K : ℝ := ‖dirichletHolderLiftCLM hopen hbounded hgraph hγ 2‖ *
    ((2 + n + 1).factorial : ℝ) / t ^ (2 + n + 1) *
      (measureUnivNNReal (domainMeasure n Ω) : ℝ) ^ (2 : ℝ)⁻¹
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (K + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨φ, hnear⟩ := exists_testFunction_uniform_approximation hopen hbounded hg hzero hδ
  let q := baseCoordCLM (testFunctionToH10 φ)
  have hqbound (y : ℝ^n) (hy : y ∈ closure Ω) : ‖φ.1.toFun y‖ ≤ M + δ := by
    have h := norm_le_norm_add_norm_sub' (φ.1.toFun y) (g y)
    have hn := hnear y hy
    rw [← Real.norm_eq_abs] at hn
    linarith [hbound y hy]
  have hdiff : ∀ᵐ y ∂domainMeasure n Ω, ‖(f - q) y‖ ≤ δ := by
    filter_upwards [Lp.coeFn_sub f q, hf, baseCoordCLM_testFunction_apply_ae φ,
      ae_restrict_mem hopen.measurableSet] with y hsub hfy hqy hy
    rw [hsub, Pi.sub_apply, hfy, show q y = φ.1.toFun y from hqy,
      norm_sub_rev, Real.norm_eq_abs]
    exact (hnear y (subset_closure hy)).le
  have herr := S.norm_classicalPower_le_of_ae_bound hopen hbounded hgraph hγ
    (f - q) hδ.le hdiff ht hx
  rw [S.classicalPower_sub hopen hbounded hgraph hγ f q ht hx] at herr
  have htest := S.norm_classicalPower_test_le hopen hbounded hgraph hγ φ
    (add_nonneg hM hδ.le) hqbound ht hx
  have he : K * δ + (M + δ) = M + ε := by
    have hd : δ * (K + 1) = ε := div_mul_cancel₀ ε (by linarith : K + 1 ≠ 0)
    nlinarith [hd]
  calc
    _ ≤ ‖S.classicalPower hopen hbounded hgraph hγ 0 f t x -
        S.classicalPower hopen hbounded hgraph hγ 0 q t x‖ +
        ‖S.classicalPower hopen hbounded hgraph hγ 0 q t x‖ :=
      (norm_le_norm_add_norm_sub' _ _).trans_eq (add_comm _ _)
    _ ≤ M + ε := (add_le_add herr htest).trans_eq he

/-- The spectral heat evolution contracts the uniform distance between continuous
zero-boundary data, with the same pivot construction on both sides. -/
theorem norm_classicalPower_sub_le (f h : DerivLp n 2 Ω) {g k : ℝ^n → ℝ}
    (hg : ContinuousOn g (closure Ω)) (hk : ContinuousOn k (closure Ω))
    (hgzero : ∀ y ∈ frontier Ω, g y = 0) (hkzero : ∀ y ∈ frontier Ω, k y = 0)
    (hf : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g)
    (hh : (h : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] k) {M t : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ y ∈ closure Ω, ‖g y - k y‖ ≤ M) (ht : 0 < t)
    {x : ℝ^n} (hx : x ∈ closure Ω) :
    ‖S.classicalPower hopen hbounded hgraph hγ 0 f t x -
      S.classicalPower hopen hbounded hgraph hγ 0 h t x‖ ≤ M := by
  rw [← S.classicalPower_sub hopen hbounded hgraph hγ f h ht hx]
  apply S.norm_classicalPower_le_of_continuousOn hopen hbounded hgraph hγ (f - h)
    (hg.sub hk) (fun y hy ↦ by rw [Pi.sub_apply, hgzero y hy, hkzero y hy, sub_self])
    ?_ hM hbound ht hx
  filter_upwards [Lp.coeFn_sub f h, hf, hh] with y hsub hfy hhy
  rw [hsub, Pi.sub_apply, Pi.sub_apply, hfy, hhy]

end HeatEquation.DirichletHeatSpectrum
