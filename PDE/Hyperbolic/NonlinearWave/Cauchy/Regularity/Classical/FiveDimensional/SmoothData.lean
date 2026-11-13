/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import
  PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiveDimensional.GlobalClassical

/-!
# Global classical waves from smooth compact data in dimension five

For a smooth globally Lipschitz scalar reaction fixing zero with bounded
second derivative, smooth compact initial displacement and velocity give a classical
wave for every positive time. Global higher persistence and correspondence
with the energy evolution are proved in the imported modules.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {f : ℝ → ℝ} {K : ℝ≥0}

/-- In dimension five, smooth compact data give a global jointly C² whole-space
wave for a smooth globally Lipschitz reaction vanishing at zero with bounded
second derivative. Every composition, amplitude, and persistence bound is derived. -/
theorem exists_global_classical_smoothReaction_five_of_smoothCompact (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : LipschitzWith K f) (hf0 : f 0 = 0) {D : ℝ} (hD : 0 ≤ D)
    (hsecond : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ D) (g h : ℝ^5 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ q : C(ℝ × ℝ^5, ℝ),
      ContDiffOn ℝ 2 q (Ioi 0 ×ˢ univ) ∧
      (∀ x, q (0, x) = g x ∧
        HasDerivWithinAt (fun t ↦ q (t, x)) (h x) (Ici 0) 0) ∧
      ∀ t : ℝ, 0 < t → ∀ x,
        deriv (fun s ↦ deriv (fun r ↦ q (r, x)) s) t -
          Δ (fun y ↦ q (t, y)) x + f (q (t, x)) = 0 := by
  have hk : (5 : ℝ) < 2 * ((4 : ℝ) - 1) := by norm_num
  have hq : (5 : ℝ) < 2 * ((6 : ℝ) - 1) := by norm_num
  have hv : (5 : ℝ) < 2 * ((5 : ℝ) - 1) := by norm_num
  let G := mkWkpSpaceOnOfContDiff (k := 6) (p := 2) (Ω := univ) g hg hgc
  let H := mkWkpSpaceOnOfContDiff (k := 5) (p := 2) (Ω := univ) h hh hhc
  obtain ⟨e, he⟩ := exists_energySolution hf hf0
    (lowerOrderCLM (by decide : 1 ≤ 6) G, wkpBaseCoordinateCLM H)
  obtain ⟨q, v, a, hq₂, hzero, hfield⟩ :=
    he.exists_global_pointwise_smoothReaction_five (k := 4) hk hs hf hf0 hD hsecond hq hv (G, H)
  refine ⟨q, hq₂, ?_, ?_⟩
  · intro x
    have hg' := congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hq hg hgc) x
    have hh' := congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hv hh hhc) x
    refine ⟨(hzero x).1.trans hg', ?_⟩
    rw [← (hzero x).2.trans hh']
    exact ((hfield 0 le_rfl).2.2.2 x).1
  · intro t ht x
    have hdd := deriv_deriv_eq_of_wave_derivatives (b := t + 1)
      (fun s hst ↦ ⟨((hfield s hst.1).2.2.2 x).1.mono Icc_subset_Ici_self,
        ((hfield s hst.1).2.2.2 x).2.1.mono Icc_subset_Ici_self⟩) ⟨ht, by linarith⟩
    rw [hdd]
    exact ((hfield t ht.le).2.2.2 x).2.2

end PDE.Hyperbolic.NonlinearWave.Cauchy
