/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Solution.Basic
public import PDE.Analysis.Evolution.Time.WeakDerivative.Regularity.Integral
public import PDE.Analysis.MeasureTheory.Measure.Restriction.HalfLine

/-!
# Absolute continuity in the weak gradient-flow class

The distributional velocity determines the continuous trajectory, including its
initial trace. Thus every member of the weak class is absolutely continuous on finite
intervals and has the prescribed strong derivative almost everywhere.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis.Evolution.IsSubgradientFlow

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {I : H → EReal} {u g : ℝ → H}

/-- The globally bounded velocity is Bochner integrable on each finite interval. -/
theorem integrableOn_velocity (h : IsSubgradientFlow I u g) (T : ℝ) :
    IntegrableOn g (Ioo 0 T) :=
  (h.velocity_memLp.mono_measure
    (volume.restrict_mono_set Ioo_subset_Ioi_self)).integrable le_top

variable [CompleteSpace H]

/-- Weak differentiation gives absolute continuity of the curve on each closed
finite interval, and identifies its strong derivative almost everywhere. -/
theorem regularity_Icc (h : IsSubgradientFlow I u g) {T : ℝ} (hT : 0 < T) :
    AbsolutelyContinuousOnInterval u 0 T ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 T), HasDerivAt u (g t) t :=
  (h.weakDerivative.mono Ioo_subset_Ioi_self).absolutelyContinuousOnInterval_and_ae_hasDerivAt hT
      (h.continuousOn.mono Icc_subset_Ici_self) (h.integrableOn_velocity T)

/-- The velocity of any weak flow is its strong derivative almost everywhere. -/
theorem ae_hasDerivAt (h : IsSubgradientFlow I u g) :
    ∀ᵐ t ∂volume.restrict (Ioi 0), HasDerivAt u (g t) t :=
  ae_restrict_Ioi_of_forall_Ioo fun _ hT ↦ (h.regularity_Icc hT).2

end PDE.Analysis.Evolution.IsSubgradientFlow
