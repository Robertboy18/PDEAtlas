/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm

/-!
# Ellipticity of continuous coefficient representatives

An almost-everywhere ellipticity bound holds everywhere on an open domain once
the coefficients have continuous representatives. For each fixed vector, continuity
extends the scalar quadratic inequality across the exceptional null set. The same
ellipticity constant works for every vector.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Continuous representatives inherit the almost-everywhere quadratic ellipticity
bound at every interior point. Symmetry is not needed. -/
theorem AEUniformlyElliptic.le_of_continuousOn
    {A : Fin n → Fin n → DerivLp n ∞ Ω} {alpha : ℝ}
    (hA : AEUniformlyElliptic A alpha) (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (hrep : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    (ha : ∀ i j, ContinuousOn (a i j) Ω) :
    ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      alpha * ∑ i : Fin n, ξ i * ξ i ≤
        ∑ i : Fin n, ∑ j : Fin n, a i j x * ξ j * ξ i := by
  have hrepAll : ∀ᵐ x ∂domainMeasure n Ω, ∀ i j, A i j x = a i j x :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ hrep i j
  intro x hx ξ
  let q : ℝ^n → ℝ := fun y ↦ ∑ i : Fin n, ∑ j : Fin n, a i j y * ξ j * ξ i
  let c : ℝ := alpha * ∑ i : Fin n, ξ i * ξ i
  have hq : ContinuousOn q Ω := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact ((ha i j).mul_const (ξ j)).mul_const (ξ i)
  have heq : q =ᵐ[domainMeasure n Ω] fun y ↦ max c (q y) := by
    filter_upwards [hA.2, hrepAll] with y hy hr
    have hle : c ≤ q y := by
      simpa only [c, q, hr] using hy ξ
    exact (max_eq_right hle).symm
  have hpoint := Measure.eqOn_open_of_ae_eq (μ := volume) heq hΩ hq
    (continuousOn_const.sup hq)
  exact (le_max_left c (q x)).trans_eq (hpoint hx).symm

end SobolevSpace.GraphSpace
