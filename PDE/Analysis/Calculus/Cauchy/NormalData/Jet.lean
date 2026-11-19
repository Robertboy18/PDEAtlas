/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.Cauchy.NormalData.Analytic
public import PDE.Analysis.Calculus.Cauchy.NormalData.LowerJet

/-!
# The lower jet determined by analytic normal data

Equal ordinary normal data on a regular analytic level determine all lower
ordinary derivatives there. Thus the lower jet of an analytic extension of
the data is independent of that extension. Coefficient germs in a Cauchy
problem can be specified at this data-determined jet.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace PDE.Analysis.Cauchy

open MultiIndex Hypersurface

variable {d k : ℕ}

/-- Equality of normal-data germs determines the whole lower coordinate jet
along a regular analytic level, independently of any differential equation. -/
theorem eventually_coordinateJetLT_eq_of_normal_data
    {φ u v : ℝ^(d + 1) → ℝ} {p : ℝ^(d + 1)}
    (hφ : AnalyticAt ℝ φ p) (hreg : fderiv ℝ φ p ≠ 0)
    (hu : AnalyticAt ℝ u p) (hv : AnalyticAt ℝ v p)
    (hdata : ∀ᶠ x in 𝓝 p, φ x = 0 → ∀ j : Fin k,
      normalData (j : ℕ) u (levelNormal φ x) x =
        normalData (j : ℕ) v (levelNormal φ x) x) :
    ∀ᶠ x in 𝓝 p, φ x = 0 → coordinateJetLT k u x = coordinateJetLT k v x := by
  have hnear := hφ.eventually_analyticAt.and
    ((hφ.fderiv.continuousAt.eventually_ne hreg).and
      (hu.eventually_analyticAt.and (hv.eventually_analyticAt.and hdata)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hΓ := hasConormalParametrizations_levelNormal Metric.isOpen_ball
    (fun x hx ↦ (hball hx).1) (fun x hx ↦ (hball hx).2.1)
  have hν (x : ℝ^(d + 1)) (hx : x ∈ Metric.ball p r ∩ {y | φ y = 0}) :
      levelNormal φ x ≠ 0 := by
    have hnorm := norm_levelNormal (hball hx.1).2.1
    intro hz
    rw [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have huB : ContDiffOn ℝ ∞ u (Metric.ball p r) :=
    fun x hx ↦ (hball hx).2.2.1.contDiffAt.contDiffWithinAt
  have hvB : ContDiffOn ℝ ∞ v (Metric.ball p r) :=
    fun x hx ↦ (hball hx).2.2.2.1.contDiffAt.contDiffWithinAt
  have hj := iteratedFDeriv_eq_on_lt_of_normal_data Metric.isOpen_ball
    inter_subset_left (levelNormal φ) hν hΓ huB hvB
    (fun j hj x hx ↦ (hball hx.1).2.2.2.2 hx.2 ⟨j, hj⟩)
  filter_upwards [Metric.ball_mem_nhds p hr] with x hx
  intro hφx
  funext j α
  exact congrArg (fun D ↦ D (directions α)) (hj j j.isLt ⟨hx, hφx⟩)

/-- The lower jet of an analytic extension carrying the given normal-data
germs. The realization and independence theorems below characterize this
choice intrinsically at a point of the regular analytic level. -/
def normalDataJet (φ : ℝ^(d + 1) → ℝ) (g : Fin k → ℝ^(d + 1) → ℝ)
    (p : ℝ^(d + 1)) :
    ∀ j : Fin k, Sym (Fin (d + 1)) (j : ℕ) → ℝ :=
  Classical.epsilon fun q ↦ ∃ G : ℝ^(d + 1) → ℝ,
    AnalyticAt ℝ G p ∧
      (∀ᶠ x in 𝓝 p, φ x = 0 → ∀ j : Fin k,
        normalData (j : ℕ) G (levelNormal φ x) x = g j x) ∧
      coordinateJetLT k G p = q

/-- The data jet is realized by an analytic extension constructed from the
individual analytic normal data. No compatibility tuple is supplied. -/
theorem exists_analytic_normalData_with_jet
    {φ : ℝ^(d + 1) → ℝ} {p : ℝ^(d + 1)}
    (hφ : AnalyticAt ℝ φ p) (hreg : fderiv ℝ φ p ≠ 0)
    (g : Fin k → ℝ^(d + 1) → ℝ) (hg : ∀ j, AnalyticAt ℝ (g j) p) :
    ∃ G : ℝ^(d + 1) → ℝ, AnalyticAt ℝ G p ∧
      (∀ᶠ x in 𝓝 p, φ x = 0 → ∀ j : Fin k,
        normalData (j : ℕ) G (levelNormal φ x) x = g j x) ∧
      coordinateJetLT k G p = normalDataJet φ g p := by
  obtain ⟨G, hG, hdata⟩ := exists_analytic_normalData hφ hreg k g hg
  have hex : ∃ q, ∃ F : ℝ^(d + 1) → ℝ, AnalyticAt ℝ F p ∧
      (∀ᶠ x in 𝓝 p, φ x = 0 → ∀ j : Fin k,
        normalData (j : ℕ) F (levelNormal φ x) x = g j x) ∧
      coordinateJetLT k F p = q :=
    ⟨coordinateJetLT k G p, G, hG, hdata, rfl⟩
  exact Classical.epsilon_spec hex

/-- Every analytic extension of the same normal data has the data-determined
lower jet at a point of the regular level. -/
theorem coordinateJetLT_eq_normalDataJet
    {φ G : ℝ^(d + 1) → ℝ} {p : ℝ^(d + 1)}
    (hφ : AnalyticAt ℝ φ p) (hp : φ p = 0) (hreg : fderiv ℝ φ p ≠ 0)
    (g : Fin k → ℝ^(d + 1) → ℝ) (hg : ∀ j, AnalyticAt ℝ (g j) p)
    (hG : AnalyticAt ℝ G p)
    (hdata : ∀ᶠ x in 𝓝 p, φ x = 0 → ∀ j : Fin k,
      normalData (j : ℕ) G (levelNormal φ x) x = g j x) :
    coordinateJetLT k G p = normalDataJet φ g p := by
  obtain ⟨F, hF, hFdata, hFjet⟩ := exists_analytic_normalData_with_jet hφ hreg g hg
  have heq : ∀ᶠ x in 𝓝 p, φ x = 0 → ∀ j : Fin k,
      normalData (j : ℕ) G (levelNormal φ x) x =
        normalData (j : ℕ) F (levelNormal φ x) x := by
    filter_upwards [hdata, hFdata] with x hx hFx
    exact fun hx0 j ↦ (hx hx0 j).trans (hFx hx0 j).symm
  exact ((eventually_coordinateJetLT_eq_of_normal_data hφ hreg hG hF heq).self_of_nhds
    hp).trans hFjet

end PDE.Analysis.Cauchy
