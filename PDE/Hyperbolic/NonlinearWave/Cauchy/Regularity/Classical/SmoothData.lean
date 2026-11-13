/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Existence
public import PDE.Spaces.Sobolev.GraphSpace.Topology.SmoothData

/-!
# Smooth compact data give classical nonlinear waves

In every positive dimension, arbitrary smooth compactly supported displacement
and velocity yield a positive whole-space time strip for the reaction
`s / (1 + s²)`. The solution is jointly C² in the open strip, attains both
initial data, and satisfies the classical PDE using the second time
derivative and Mathlib's classical Laplacian.

The proof takes the already constructed global energy evolution and applies
the local classical correspondence.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Laplacian Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ}

/-- The canonical representative of smooth compact data is the original
function at every point, not just almost everywhere. -/
theorem classicalRepresentative_mkWkpSpaceOnOfContDiff (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    {g : ℝ^n → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    (classicalRepresentativeCLM hk
      (mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) g hg hc) : ℝ^n → ℝ) = g := by
  symm
  apply eq_classicalRepresentativeCLM_of_ae_eq hk _ hg.continuous
  simpa only [baseRepresentative, wkpBaseCoordinateCLM_apply,
    domainMeasure, Measure.restrict_univ] using
    (wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae (k := k) (Ω := univ) hg hc).symm

/-- Continuous derivative fields on a closed strip identify the
iterated time derivative at interior times. -/
theorem deriv_deriv_eq_of_wave_derivatives {b : ℝ} {q v a : ℝ → ℝ}
    (h : ∀ t ∈ Icc 0 b, HasDerivWithinAt q (v t) (Icc 0 b) t ∧ HasDerivWithinAt v (a t) (Icc 0 b) t)
    {t : ℝ} (ht : t ∈ Ioo 0 b) :
    deriv (deriv q) t = a t := by
  have heq : deriv q =ᶠ[𝓝 t] v := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact ((h r ⟨hr.1.le, hr.2.le⟩).1.hasDerivAt (Icc_mem_nhds hr.1 hr.2)).deriv
  rw [heq.deriv_eq]
  exact ((h t ⟨ht.1.le, ht.2.le⟩).2.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv

variable [NeZero n]

/-- In every positive dimension, smooth compact data yield a local
classical whole-space wave for the globally Lipschitz saturating reaction.
No bound, composition hypothesis, embedding hypothesis, or regularity of the
unknown solution is an input. -/
theorem exists_classical_saturatingReaction_of_smoothCompact
    (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ b : ℝ, 0 < b ∧ ∃ q : C(ℝ × ℝ^n, ℝ),
      ContDiffOn ℝ 2 q (Ioo 0 b ×ˢ univ) ∧
      (∀ x, q (0, x) = g x ∧
        HasDerivWithinAt (fun t ↦ q (t, x)) (h x) (Icc 0 b) 0) ∧
      ∀ t ∈ Ioo 0 b, ∀ x,
        deriv (fun s ↦ deriv (fun r ↦ q (r, x)) s) t -
          Δ (fun y ↦ q (t, y)) x + saturatingReaction (q (t, x)) = 0 := by
  let k := n + 2
  have hk : (n : ℝ) < 2 * ((k : ℝ) - 1) := by
    dsimp [k]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1) := by push_cast; linarith
  have hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1) := by push_cast; linarith
  let G := mkWkpSpaceOnOfContDiff (k := k + 2) (p := 2) (Ω := univ) g hg hgc
  let H := mkWkpSpaceOnOfContDiff (k := k + 1) (p := 2) (Ω := univ) h hh hhc
  obtain ⟨u, hu⟩ := exists_energySolution lipschitzWith_saturatingReaction saturatingReaction_zero
    (lowerOrderCLM (by omega : 1 ≤ k + 2) G, wkpBaseCoordinateCLM H)
  obtain ⟨b, hb, q, v, a, hq₂, hzero, hfield⟩ :=
    hu.exists_local_pointwise_saturatingReaction (k := k) hk hq hv (G, H)
  refine ⟨b, hb, q, hq₂, ?_, ?_⟩
  · intro x
    have hq₀ := (hzero x).1
    have hv₀ := (hzero x).2
    have hg' := congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hq hg hgc) x
    have hh' := congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hv hh hhc) x
    refine ⟨hq₀.trans hg', ?_⟩
    rw [← hv₀.trans hh']
    exact ((hfield 0 ⟨le_rfl, hb.le⟩).2.2.2 x).1
  · intro t ht x
    have hdd := deriv_deriv_eq_of_wave_derivatives
      (fun s hs ↦ ⟨((hfield s hs).2.2.2 x).1, ((hfield s hs).2.2.2 x).2.1⟩) ht
    rw [hdd]
    exact ((hfield t ⟨ht.1.le, ht.2.le⟩).2.2.2 x).2.2

end PDE.Hyperbolic.NonlinearWave.Cauchy
