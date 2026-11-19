/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm

/-!
# Restriction of elliptic coefficients

Restriction preserves the same almost-everywhere ellipticity constant.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace

/-- An almost-everywhere elliptic matrix remains elliptic on a smaller domain. -/
theorem AEUniformlyElliptic.restrict {n : ℕ} {Ω V : Set (ℝ^n)}
    {a : Fin n → Fin n → DerivLp n ∞ Ω} {alpha : ℝ}
    (ha : AEUniformlyElliptic a alpha) (hVΩ : V ⊆ Ω) :
    AEUniformlyElliptic (fun i j ↦ restrictDerivLp hVΩ (a i j)) alpha := by
  refine ⟨ha.1, ?_⟩
  filter_upwards [ae_mono (domainMeasure_le hVΩ) ha.2,
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦
      restrictDerivLp_apply_ae hVΩ (a i j)] with x hx hrep
  simpa only [hrep] using hx

end SobolevSpace.GraphSpace
