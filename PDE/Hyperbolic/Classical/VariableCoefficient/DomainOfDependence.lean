/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.VariableCoefficient.FinitePropagation

/-!
# Domain of dependence for variable nondivergence waves

Two classical solutions with equal displacement and right velocity on
the open initial base agree throughout the eikonal cone and at its vertex.
Compact inner sublevels may be assumed directly or derived from an
at-most-quadratic upper bound on the principal matrix.
-/

@[expose] public noncomputable section

namespace WaveEquation.VariableCoefficient

open Set PDE.Common PDE.Analysis

variable {n : ℕ}

/-- Equal Cauchy data on an eikonal base determine the full cone and terminal value. -/
theorem eq_on_eikonal_cone_of_initial_eq {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (ha : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j)) (hsymm : ∀ x i j, a x i j = a x j i) {θ : ℝ}
    (hθ : 0 < θ) (hell : ∀ x (v : ℝ^n), θ * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * v i * v j) {q : ℝ^n → ℝ}
    {c : ℝ^n} (hq : Continuous q) (hqc : q c = 0) (hqpos : ∀ x, x ≠ c → 0 < q x)
    (hqd : ∀ x, x ≠ c → ContDiffAt ℝ 1 q x)
    (heik : ∀ x, x ≠ c → ∑ i, ∑ j, a x i j * (∂[i] q) x * (∂[j] q) x = 1) {T : ℝ} (hT : 0 < T)
    (hK : ∀ r ∈ Ioo 0 T, IsCompact {x | q x ≤ r}) {u v : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hv : ContDiffOn ℝ 2 v {p | 0 < p 0})
    (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) (hv₀ : ContDiffOn ℝ 1 v {p | 0 ≤ p 0})
    (hpdeu : ∀ t : ℝ, 0 < t → ∀ x, q x < T - t → waveOperator a u (timeSpaceCons t x) = 0)
    (hpdev : ∀ t : ℝ, 0 < t → ∀ x, q x < T - t → waveOperator a v (timeSpaceCons t x) = 0)
    (hpos : ∀ x, q x < T → u (timeSpaceCons 0 x) = v (timeSpaceCons 0 x))
    (hvel : ∀ x, q x < T → derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 =
      derivWithin (fun t ↦ v (timeSpaceCons t x)) (Ici 0) 0) :
    (∀ t ∈ Ico 0 T, ∀ x, q x < T - t → u (timeSpaceCons t x) = v (timeSpaceCons t x)) ∧
      u (timeSpaceCons T c) = v (timeSpaceCons T c) := by
  have hpde : ∀ t : ℝ, 0 < t → ∀ x, q x < T - t →
      waveOperator a (u - v) (timeSpaceCons t x) = 0 := by
    intro t ht x hx
    have hmem : {p : ℝ^(n + 1) | 0 < p 0} ∈ nhds (timeSpaceCons t x) :=
      (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds
        (by simpa using ht)
    rw [waveOperator_sub a (hu.contDiffAt hmem) (hv.contDiffAt hmem),
      hpdeu t ht x hx, hpdev t ht x hx, sub_self]
  have hpos' : ∀ x, q x < T → (u - v) (timeSpaceCons 0 x) = 0 :=
    fun x hx ↦ sub_eq_zero.mpr (hpos x hx)
  have hvel' : ∀ x, q x < T →
      derivWithin (fun t ↦ (u - v) (timeSpaceCons t x)) (Ici 0) 0 = 0 := by
    intro x hx
    change derivWithin (fun t ↦ u (timeSpaceCons t x) - v (timeSpaceCons t x)) (Ici 0) 0 = 0
    rw [derivWithin_fun_sub (differentiableWithinAt_initial_time hu₀ x)
      (differentiableWithinAt_initial_time hv₀ x), hvel x hx, sub_self]
  obtain ⟨hcone, hvertex⟩ := finite_propagation_eikonal_cone ha hsymm hθ hell
    hq hqc hqpos hqd heik hT hK (hu.sub hv) (hu₀.sub hv₀) hpde hpos' hvel'
  exact ⟨fun t ht x hx ↦ sub_eq_zero.mp (hcone t ht x hx), sub_eq_zero.mp hvertex⟩

/-- Equal Cauchy data determine the cone and its terminal value under quadratic matrix
growth. The eikonal sublevel compactness is proved, independently of both solutions. -/
theorem eq_on_eikonal_cone_of_initial_eq_of_quadratic_growth {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (ha : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j)) (hsymm : ∀ x i j, a x i j = a x j i) {θ : ℝ}
    (hθ : 0 < θ) (hell : ∀ x (v : ℝ^n), θ * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * v i * v j) {C : ℝ}
    (hC : 0 < C) {c : ℝ^n}
    (hupper : ∀ x (v : ℝ^n), (∑ i, ∑ j, a x i j * v i * v j) ≤ C ^ 2 * (1 + ‖x - c‖ ^ 2) * ‖v‖ ^ 2)
    {q : ℝ^n → ℝ} (hq : Continuous q) (hqc : q c = 0) (hqpos : ∀ x, x ≠ c → 0 < q x)
    (hqd : ∀ x, x ≠ c → ContDiffAt ℝ 1 q x)
    (heik : ∀ x, x ≠ c → ∑ i, ∑ j, a x i j * (∂[i] q) x * (∂[j] q) x = 1) {T : ℝ} (hT : 0 < T)
    {u v : ℝ^(n + 1) → ℝ} (hu : ContDiffOn ℝ 2 u {p | 0 < p 0})
    (hv : ContDiffOn ℝ 2 v {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0})
    (hv₀ : ContDiffOn ℝ 1 v {p | 0 ≤ p 0})
    (hpdeu : ∀ t : ℝ, 0 < t → ∀ x, q x < T - t → waveOperator a u (timeSpaceCons t x) = 0)
    (hpdev : ∀ t : ℝ, 0 < t → ∀ x, q x < T - t → waveOperator a v (timeSpaceCons t x) = 0)
    (hpos : ∀ x, q x < T → u (timeSpaceCons 0 x) = v (timeSpaceCons 0 x))
    (hvel : ∀ x, q x < T → derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 =
      derivWithin (fun t ↦ v (timeSpaceCons t x)) (Ici 0) 0) :
    (∀ t ∈ Ico 0 T, ∀ x, q x < T - t → u (timeSpaceCons t x) = v (timeSpaceCons t x)) ∧
      u (timeSpaceCons T c) = v (timeSpaceCons T c) :=
  eq_on_eikonal_cone_of_initial_eq ha hsymm hθ hell hq hqc hqpos hqd heik hT
    (fun r _ ↦ Eikonal.isCompact_sublevel_of_matrix_eikonal hC hupper hq hqc hqpos
      (fun x hx ↦ (hqd x hx).differentiableAt_one) heik r) hu hv hu₀ hv₀ hpdeu hpdev hpos hvel

end WaveEquation.VariableCoefficient
