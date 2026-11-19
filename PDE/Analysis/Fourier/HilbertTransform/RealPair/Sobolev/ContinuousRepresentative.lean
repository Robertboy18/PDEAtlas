/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.Weak

/-!
# Continuous representatives of Hilbert transforms of weak H¹ data

The spectral Hilbert transform commutes with weak differentiation. Its weak
derivative therefore gives an explicit interval primitive representing the
transform almost everywhere. This constructs a continuous representative
without any continuity assumption on the initial choice of representative.

The weak Sobolev estimate then gives an almost-everywhere uniform bound for
every representative of the spectral transform.
-/

@[expose] public section

noncomputable section

open MeasureTheory PDE.Analysis.Evolution

namespace PDE.Analysis

/-- Changing either real function on a null set preserves the concrete
spectral Hilbert relation. -/
theorem IsHilbertPair.congr_ae {omega omega' v v' : ℝ → ℝ}
    (h : IsHilbertPair omega v) (homega : omega =ᵐ[volume] omega')
    (hv : v =ᵐ[volume] v') : IsHilbertPair omega' v' := by
  obtain ⟨F, hF, hHF⟩ := h
  refine ⟨F, ?_, ?_⟩
  · filter_upwards [homega, hF] with x hx hFx
    exact (congrArg (fun r : ℝ ↦ (r : ℂ)) hx).symm.trans hFx
  · filter_upwards [hv, hHF] with x hx hHFx
    exact (congrArg (fun r : ℝ ↦ (r : ℂ)) hx).symm.trans hHFx

/-- A real Hilbert transform of weak H¹ data has a continuous representative.
The representative is the mean-normalized primitive of its weak derivative,
whose existence follows from spectral commutation. -/
theorem IsHilbertPair.exists_continuous_ae_eq {omega eta v : ℝ → ℝ}
    (h : IsHilbertPair omega v) (heta : MemLp eta 2 volume)
    (hweak : HasWeakTimeDerivativeOn Set.univ omega eta) :
    ∃ V : ℝ → ℝ, Continuous V ∧ v =ᵐ[volume] V ∧ IsHilbertPair omega V := by
  obtain ⟨w, _hw, hderiv⟩ := h.exists_hasWeakTimeDerivativeOn heta hweak
  obtain ⟨V, hcont, hV, _hVderiv⟩ := hderiv.exists_continuous_ae_eq
  exact ⟨V, hcont, hV, h.congr_ae Filter.EventuallyEq.rfl hV⟩

/-- Every real representative of the spectral Hilbert transform of weak H¹
data satisfies the uniform Sobolev bound almost everywhere. Continuity of
the chosen representative is not a hypothesis. -/
theorem IsHilbertPair.ae_norm_le_eLpNorm_add_weakDerivative
    {omega eta v : ℝ → ℝ} (h : IsHilbertPair omega v)
    (heta : MemLp eta 2 volume)
    (hweak : HasWeakTimeDerivativeOn Set.univ omega eta) :
    ∀ᵐ x ∂volume,
      ‖v x‖ ≤ (eLpNorm omega 2 volume).toReal + (eLpNorm eta 2 volume).toReal := by
  obtain ⟨V, hcont, hV, hpair⟩ := h.exists_continuous_ae_eq heta hweak
  filter_upwards [hV] with x hx
  rw [hx]
  exact hpair.norm_le_eLpNorm_add_weakDerivative hcont heta hweak x

end PDE.Analysis
