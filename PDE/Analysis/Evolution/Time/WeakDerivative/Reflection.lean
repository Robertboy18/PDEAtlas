/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.Reflection
public import PDE.Analysis.Evolution.Time.WeakDerivative.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Reflection of weak time derivatives

Time reflection transports a local weak evolution to the reflected domain.
The derivative changes sign by the chain rule. This is the analytic
extension step used to recover endpoint regularity on finite intervals.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace HasWeakTimeDerivativeOn

/-- Weak time derivatives are equivariant under reflection.  The derivative
acquires the expected minus sign because `d(2c-t)/dt = -1`.  This theorem is
the analytic core of the finite-interval endpoint extension used in the
Lions–Magenes argument. -/
theorem reflect
    {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → X}
    (h : HasWeakTimeDerivativeOn U f g) (c : ℝ) :
    HasWeakTimeDerivativeOn ((reflectTime c) ⁻¹' U)
      (f ∘ reflectTime c) (fun t ↦ -g (reflectTime c t)) where
  locallyIntegrable_f := LocallyIntegrableOn.comp_reflectTime hU h.locallyIntegrable_f c
  locallyIntegrable_g := (LocallyIntegrableOn.comp_reflectTime hU h.locallyIntegrable_g c).neg
  integral_eq ell φ hφ hφcompact hsupp := by
    have hderiv (t : ℝ) : deriv (φ ∘ reflectTime c) t = -deriv φ (reflectTime c t) := by
      rw [deriv_comp t (hφ.differentiable (by simp) _)
        ((contDiff_reflectTime c).differentiable (by simp) t), deriv_reflectTime, mul_neg_one]
    have hbase := h.integral_eq ell (φ ∘ reflectTime c)
      (hφ.comp (contDiff_reflectTime c)) (hφcompact.comp_homeomorph (reflectTimeHomeomorph c))
      ((tsupport_comp_eq_preimage φ (reflectTimeHomeomorph c)).subset.trans fun t ht ↦ by
        simpa using hsupp ht)
    have hR : ∀ F : ℝ → ℝ, ∫ t, F (reflectTime c t) = ∫ t, F t :=
      (measurePreserving_reflectTime c).integral_comp
        (reflectTimeHomeomorph c).toMeasurableEquiv.measurableEmbedding
    have h₁ := hR fun t ↦ ell (-g (reflectTime c t)) * φ t
    have h₂ := hR fun t ↦ ell (f (reflectTime c t)) * deriv φ t
    simp only [comp_apply, hderiv, reflectTime_involutive, map_neg, neg_mul, mul_neg, integral_neg,
      neg_neg, neg_inj] at h₁ h₂ hbase ⊢
    rw [← h₁, ← h₂, hbase]

end HasWeakTimeDerivativeOn

end PDE.Analysis.Evolution
