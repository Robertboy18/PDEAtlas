/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing

/-!
# Bounded Fourier multipliers on L²

An L∞ scalar symbol acts on Hilbert-valued L² by Fourier transform,
pointwise multiplication, and inverse Fourier transform. Mathlib's Hölder
bilinear map supplies the multiplication operator; Plancherel gives its bound.

The construction accepts measurable symbols through their L∞ classes. A symbol that is real
almost everywhere gives a self-adjoint operator: Plancherel moves the pairing to the frequency
side, where multiplication by a real function is symmetric.
Identification with a multiplier on arbitrary tempered distributions requires
the representative symbol to have temperate growth.
-/

@[expose] public section

noncomputable section

open FourierTransform MeasureTheory
open scoped ENNReal SchwartzMap InnerProductSpace ComplexConjugate

open MeasureTheory.Lp

namespace PDE.Analysis.Fourier

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The L² operator with an essentially bounded Fourier symbol. The symbol is
an L∞ class, so changing it on a null set leaves the operator unchanged. -/
def fourierMultiplierL2 (m : Lp ℂ ∞ (volume : Measure E)) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  fourierInvCLM ℂ (Lp F 2 (volume : Measure E)) ∘L
    ((ContinuousLinearMap.lsmul ℂ ℂ (E := F)).holderL volume ∞ 2 2 m) ∘L
      fourierCLM ℂ (Lp F 2 (volume : Measure E))

/-- The operator acts by multiplying the Fourier transform in L². -/
theorem fourierMultiplierL2_apply (m : Lp ℂ ∞ (volume : Measure E))
    (f : Lp F 2 (volume : Measure E)) :
    fourierMultiplierL2 m f = 𝓕⁻ (m • 𝓕 f : Lp F 2 (volume : Measure E)) := by
  change 𝓕⁻ ((ContinuousLinearMap.lsmul ℂ ℂ (E := F)).holder 2 m (𝓕 f)) = _
  apply congrArg (fun z : Lp F 2 (volume : Measure E) ↦ 𝓕⁻ z)
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.lsmul ℂ ℂ (E := F)).coeFn_holder (r := 2) m (𝓕 f),
    Lp.coeFn_lpSMul (r := 2) m (𝓕 f)] with x hholder hsmul
  exact hholder.trans hsmul.symm

/-- Plancherel and Hölder bound each output by the L∞ symbol norm times the
input L² norm. -/
theorem norm_fourierMultiplierL2_apply_le (m : Lp ℂ ∞ (volume : Measure E))
    (f : Lp F 2 (volume : Measure E)) :
    ‖fourierMultiplierL2 m f‖ ≤ ‖m‖ * ‖f‖ := by
  rw [fourierMultiplierL2_apply]
  calc
    ‖𝓕⁻ (m • 𝓕 f : Lp F 2 (volume : Measure E))‖ =
        ‖(m • 𝓕 f : Lp F 2 (volume : Measure E))‖ :=
      (Lp.fourierTransformₗᵢ E F).symm.norm_map _
    _ ≤ ‖m‖ * ‖𝓕 f‖ := Lp.norm_smul_le m (𝓕 f)
    _ = ‖m‖ * ‖f‖ := by rw [Lp.norm_fourier_eq]

/-- The operator norm is at most the essential supremum of the Fourier symbol. -/
theorem norm_fourierMultiplierL2_le (m : Lp ℂ ∞ (volume : Measure E)) :
    ‖fourierMultiplierL2 (F := F) m‖ ≤ ‖m‖ :=
  (fourierMultiplierL2 (F := F) m).opNorm_le_bound (norm_nonneg m)
    (norm_fourierMultiplierL2_apply_le m)

/-- For a symbol of temperate growth, the L² construction agrees with Mathlib's
Fourier multiplier on tempered distributions. -/
theorem fourierMultiplierL2_toTemperedDistribution {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (hmem : MemLp g ∞ (volume : Measure E))
    (f : Lp F 2 (volume : Measure E)) :
    (fourierMultiplierL2 (hmem.toLp g) f : 𝓢'(E, F)) =
      TemperedDistribution.fourierMultiplierCLM F g (f : 𝓢'(E, F)) := by
  rw [fourierMultiplierL2_apply, ← Lp.fourierInv_toTemperedDistribution_eq,
    Lp.toTemperedDistribution_smul_eq hg hmem,
    ← Lp.fourier_toTemperedDistribution_eq,
    TemperedDistribution.fourierMultiplierCLM_apply]

/-- An L² Fourier multiplier whose symbol is real almost everywhere is self-adjoint. -/
theorem isSelfAdjoint_fourierMultiplierL2 {m : Lp ℂ ∞ (volume : Measure E)}
    (hm : ∀ᵐ ξ ∂volume, conj (m ξ) = m ξ) :
    IsSelfAdjoint (fourierMultiplierL2 (F := F) m) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change ⟪fourierMultiplierL2 m f, g⟫_ℂ = ⟪f, fourierMultiplierL2 m g⟫_ℂ
  rw [fourierMultiplierL2_apply, fourierMultiplierL2_apply,
    ← Lp.inner_fourier_eq (𝓕⁻ _) g, FourierInvPair.fourier_fourierInv_eq,
    Lp.inner_lpSMul_left_of_real hm, ← Lp.inner_fourier_eq f (𝓕⁻ _),
    FourierInvPair.fourier_fourierInv_eq]

end PDE.Analysis.Fourier
