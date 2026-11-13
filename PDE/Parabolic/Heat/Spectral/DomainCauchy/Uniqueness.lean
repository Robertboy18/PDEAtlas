/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DomainCauchy.ClosedTime
import PDE.Parabolic.ComparisonPrinciple

/-!
# Uniqueness against independent classical Dirichlet heat solutions

The competing function is continuous on the closed cylinder, twice differentiable
in space and differentiable in time only in its interior, with the heat PDE
and prescribed parabolic boundary values. Applying the general maximum and minimum
principles to its difference from the constructed series proves uniqueness. No
spectral representation, pivot derivative, or terminal-time derivative is required.
-/

@[expose] public noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace MeasureTheory HolderSpace Set ParabolicMaximum
open scoped Sobolev ContDiff

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {γ : Exponent}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hγ : (γ : ℝ) < 1)
  (S : DirichletHeatSpectrum n Ω)

/-- The continuous spectral solution is unique against a separately supplied classical
solution on a closed cylinder. Differential hypotheses are imposed only for `0 < t < T`. -/
theorem eq_continuousDirichletHeat_of_classical (f : DerivLp n 2 Ω) {g : ℝ^n → ℝ}
    (hg : ContinuousOn g (closure Ω)) (hzero : ∀ x ∈ frontier Ω, g x = 0)
    (hf : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g) {T : ℝ} (hT : 0 < T)
    (z : ℝ^n → ℝ → ℝ)
    (hz : ContinuousOn (fun p : ℝ^n × ℝ ↦ z p.1 p.2) (closedCylinder Ω T))
    (hzspace : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ z y t) x)
    (hzheat : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
      HasDerivAt (z x) (PDE.laplacian (fun y ↦ z y t) x) t)
    (hzinitial : ∀ x ∈ closure Ω, z x 0 = g x)
    (hzboundary : ∀ x ∈ frontier Ω, ∀ t ∈ Icc 0 T, z x t = 0) :
    ∀ p ∈ closedCylinder Ω T,
      z p.1 p.2 = S.continuousDirichletHeat hopen hbounded hgraph hγ f g p.2 p.1 := by
  intro p hp
  have hne : Ω.Nonempty := closure_nonempty_iff.mp ⟨p.1, hp.1⟩
  let u (x : ℝ^n) (t : ℝ) := S.continuousDirichletHeat hopen hbounded hgraph hγ f g t x
  let w (x : ℝ^n) (t : ℝ) := z x t - u x t
  have hu := S.continuousOn_continuousDirichletHeat hopen hbounded hgraph hγ f hg hzero hf T
  have huspace (x : ℝ^n) (hx : x ∈ Ω) (t : ℝ) (ht : t ∈ Ioo 0 T) :
      ContDiffAt ℝ 2 (fun y ↦ u y t) x := by
    change ContDiffAt ℝ 2 (S.continuousDirichletHeat hopen hbounded hgraph hγ f g t) x
    rw [S.continuousDirichletHeat_of_pos hopen hbounded hgraph hγ f g ht.1]
    exact ((S.contDiffOn_classicalPower hopen hbounded hgraph hγ 0 f ht.1).of_le
      (by simp : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffAt (hopen.mem_nhds hx)
  have huheat (x : ℝ^n) (hx : x ∈ Ω) (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt (u x) (PDE.laplacian (fun y ↦ u y t) x) t :=
    S.hasDerivAt_continuousDirichletHeat_laplacian hopen hbounded hgraph hγ f g ht.1 hx
  have hwspace (x : ℝ^n) (hx : x ∈ Ω) (t : ℝ) (ht : t ∈ Ioo 0 T) :=
    (hzspace x hx t ht).sub (huspace x hx t ht)
  have hwtime (x : ℝ^n) (hx : x ∈ Ω) (t : ℝ) (ht : t ∈ Ioo 0 T) :=
    ((hzheat x hx t ht).sub (huheat x hx t ht)).differentiableAt
  have hwop (x : ℝ^n) (hx : x ∈ Ω) (t : ℝ) (ht : t ∈ Ioo 0 T) :
      heatParabolicOperator w x t = 0 := by
    rw [show w = (fun y s ↦ z y s - u y s) from rfl,
      heatParabolicOperator_sub z u x t (hzspace x hx t ht) (huspace x hx t ht)
        (hzheat x hx t ht).differentiableAt (huheat x hx t ht).differentiableAt,
      heatParabolicOperator, heatParabolicOperator, (hzheat x hx t ht).deriv,
      (huheat x hx t ht).deriv, sub_self, sub_self, sub_self]
  have hwboundary (q : ℝ^n × ℝ) (hq : q ∈ parabolicBoundary Ω T) : w q.1 q.2 = 0 := by
    rcases hq with hq | hq
    · change z q.1 q.2 - S.continuousDirichletHeat hopen hbounded hgraph hγ f g q.2 q.1 = 0
      rw [hzboundary q.1 hq.1 q.2 hq.2,
        S.continuousDirichletHeat_zero_on_frontier hopen hbounded hgraph hγ f hzero q.2 hq.1,
        sub_self]
    · have ht : q.2 = 0 := hq.2
      change z q.1 q.2 - S.continuousDirichletHeat hopen hbounded hgraph hγ f g q.2 q.1 = 0
      rw [ht, hzinitial q.1 hq.1,
        S.continuousDirichletHeat_zero hopen hbounded hgraph hγ, sub_self]
  have hup := heat_subsolution_le_of_boundary_le hopen hne hbounded.isCompact_closure hT w
    (hz.sub hu) hwspace hwtime (fun x hx t ht ↦ (hwop x hx t ht).le)
    (fun q hq ↦ (hwboundary q hq).le) p hp
  have hlo := boundary_le_heat_supersolution hopen hne hbounded.isCompact_closure hT w
    (hz.sub hu) hwspace hwtime (fun x hx t ht ↦ (hwop x hx t ht).ge)
    (fun q hq ↦ (hwboundary q hq).ge) p hp
  exact sub_eq_zero.mp (le_antisymm hup hlo)

end HeatEquation.DirichletHeatSpectrum
