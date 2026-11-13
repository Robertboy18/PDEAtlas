/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.VariableCoefficient.Energy.Weighted
public import PDE.Hyperbolic.Classical.VariableCoefficient.Energy.Initial
public import PDE.Analysis.Calculus.CompactEnergy.Inequality

/-!
# Vanishing compact weighted wave energy

The energy estimates combine here: the coefficient bounds, the wave equation, and zero
classical initial data force the weighted energy to vanish. Compactness is a geometric
hypothesis on a strict inner sublevel, independent of the solution.
-/

@[expose] public noncomputable section

namespace WaveEquation.VariableCoefficient

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Topology

variable {n : ℕ}

/-- Zero classical data force the compact weighted energy to vanish. -/
theorem weighted_energy_eq_zero {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (ha : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j)) (hsymm : ∀ x i j, a x i j = a x j i) {θ : ℝ}
    (hθ : 0 < θ) (hell : ∀ x (v : ℝ^n), θ * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * v i * v j) {q : ℝ^n → ℝ}
    (hq : Continuous q) (hqd : ∀ x, q x ≠ 0 → ContDiffAt ℝ 1 q x)
    (heik : ∀ x, q x ≠ 0 → ∑ i, ∑ j, a x i j * (∂[i] q) x * (∂[j] q) x = 1) {T r ε : ℝ} (hr : r < T)
    (hε : 0 < ε) (hK : IsCompact {x | q x ≤ r}) {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0})
    (hpde : ∀ t : ℝ, 0 < t → ∀ x, q x < T - t → waveOperator a u (timeSpaceCons t x) = 0)
    (hpos : ∀ x, q x < T → u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x, q x < T → derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0) {t : ℝ}
    (ht : t ∈ Ioo 0 (r - ε)) :
    (∫ x, sublevelCutoff q r ε (timeSpaceCons t x) *
      energyDensity a u (timeSpaceCons t x)) = 0 := by
  let φ := sublevelCutoff q r ε
  let e : ℝ^(n + 1) → ℝ := fun p ↦ φ p * energyDensity a u p
  let g : Fin n → ℝ^(n + 1) → ℝ := fun j p ↦ φ p * energyFlux a u j p
  let I := Ioo 0 (r - ε)
  let K := {x | q x ≤ r}
  obtain ⟨D, _, hD⟩ := exists_coefficientDivergence_bound ha hK
  let C := 1 + D ^ 2 / θ
  have hup (s : ℝ) (hs : 0 < s) (x : ℝ^n) : ContDiffAt ℝ 2 u (timeSpaceCons s x) :=
    hu.contDiffAt ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds
      (by simpa using hs))
  have hφc (s : ℝ) (hs : s ∈ I) (x : ℝ^n) : ContDiffAt ℝ 1 φ (timeSpaceCons s x) :=
    contDiffAt_sublevelCutoff hq hqd hε (by simpa using hs.2)
  have hec (s : ℝ) (hs : s ∈ I) (x : ℝ^n) : ContDiffAt ℝ 1 e (timeSpaceCons s x) :=
    (hφc s hs x).mul (contDiffAt_energyDensity (fun i j ↦ (ha i j).contDiffAt) (hup s hs.1 x))
  have hgc (j : Fin n) (s : ℝ) (hs : s ∈ I) (x : ℝ^n) : ContDiffAt ℝ 1 (g j) (timeSpaceCons s x) :=
    (hφc s hs x).mul (contDiffAt_energyFlux (fun i j ↦ (ha i j).contDiffAt) (hup s hs.1 x) j)
  have hφs (s : ℝ) (hs : 0 < s) (x : ℝ^n) (hx : x ∉ K) :
      φ (timeSpaceCons s x) = 0 := by
    apply sublevelCutoff_eq_zero hε
    exact (sub_le_self r hs.le).trans (le_of_lt (lt_of_not_ge hx))
  have hes (s : ℝ) (hs : s ∈ I) (x : ℝ^n) (hx : x ∉ K) :
      e (timeSpaceCons s x) = 0 := by
    simp only [e, hφs s hs.1 x hx, zero_mul]
  have hgs (j : Fin n) (s : ℝ) (hs : s ∈ I) (x : ℝ^n) (hx : x ∉ K) :
      g j (timeSpaceCons s x) = 0 := by
    simp only [g, hφs s hs.1 x hx, zero_mul]
  have hlocal (s : ℝ) (hs : s ∈ I) (x : ℝ^n) : (∂[0] e) (timeSpaceCons s x) -
        ∑ j, (∂[j.succ] (g j)) (timeSpaceCons s x) ≤ C * e (timeSpaceCons s x) :=
    weighted_energy_local_inequality ha hsymm hθ hell hq hqd heik hε hs.1 hs.2 x (hup s hs.1 x)
      (fun hx ↦ hpde s hs.1 x (hx.trans (sub_lt_sub_right hr s))) hD
  have hderiv (s : ℝ) (hs : s ∈ I) : HasDerivAt (fun z ↦ ∫ x, e (timeSpaceCons z x))
        (∫ x, (∂[0] e) (timeSpaceCons s x)) s :=
    hasDerivAt_integral_compact_support isOpen_Ioo hK hec hes hs
  have hle (s : ℝ) (hs : s ∈ I) :
      (∫ x, (∂[0] e) (timeSpaceCons s x)) ≤ C * ∫ x, e (timeSpaceCons s x) :=
    integral_time_partial_le isOpen_Ioo hK hec hgc hes hgs hlocal hs
  have hzero : Tendsto (fun s ↦ ∫ x, e (timeSpaceCons s x)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_weighted_energy_zero (fun i j ↦ (ha i j).continuous) hu₀
      (continuous_sublevelCutoff hq r ε) hK (isOpen_lt hq continuous_const)
      (fun _ hx ↦ hx.trans_lt hr) hpos hvel hφs
  exact eq_zero_of_hasDerivAt_le_of_tendsto_zero hderiv hle hzero
    (fun s _ ↦ integral_nonneg fun x ↦ mul_nonneg (sublevelCutoff_nonneg q r ε _)
      (energyDensity_nonneg (quadratic_nonneg_of_elliptic hθ hell) u _)) ht

/-- Nonnegative compact weighted energy vanishing in integral forces pointwise energy zero. -/
theorem energyDensity_eq_zero_of_weighted_energy_eq_zero {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (ha : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (hpos : ∀ x (v : ℝ^n), 0 ≤ ∑ i, ∑ j, a x i j * v i * v j) {q : ℝ^n → ℝ} (hq : Continuous q)
    {r ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) (hK : IsCompact {x | q x ≤ r}) {u : ℝ^(n + 1) → ℝ}
    (hu : ∀ x, ContDiffAt ℝ 2 u (timeSpaceCons t x))
    (hz :
      (∫ x, sublevelCutoff q r ε (timeSpaceCons t x) * energyDensity a u (timeSpaceCons t x)) = 0)
    {x : ℝ^n} (hx : q x < r - t) :
    energyDensity a u (timeSpaceCons t x) = 0 := by
  let f : ℝ^n → ℝ := fun y ↦ sublevelCutoff q r ε (timeSpaceCons t y) *
    energyDensity a u (timeSpaceCons t y)
  have hc : Continuous f := ((continuous_sublevelCutoff hq r ε).comp
      (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous).mul (contDiff_spatial_slice fun y ↦
        contDiffAt_energyDensity (fun i j ↦ (ha i j).contDiffAt) (hu y)).continuous
  have hs : HasCompactSupport f := HasCompactSupport.intro hK fun y hy ↦ by
    have hh := sublevelCutoff_eq_zero (q := q) hε
      ((sub_le_self r ht.le).trans (le_of_lt (lt_of_not_ge hy)))
    simp only [f, hh, zero_mul]
  have hnonneg : 0 ≤ f := fun y ↦ mul_nonneg (sublevelCutoff_nonneg q r ε _)
    (energyDensity_nonneg hpos u _)
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg (hc.integrable_of_hasCompactSupport hs)).mp hz
  have heq := Measure.eq_of_ae_eq hae hc continuous_const
  have hfx : f x = 0 := congrFun heq x
  exact (mul_eq_zero.mp hfx).resolve_left (sublevelCutoff_pos hε hx).ne'

end WaveEquation.VariableCoefficient
