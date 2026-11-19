/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.IntegralIdentity
public import PDE.Analysis.Evolution.Time.WeakDerivative.InitialPrimitive

/-!
# Absolute continuity of the prescribed weakly differentiable curve

An integral identity at every time identifies the curve with its Bochner primitive.
Consequently the curve is absolutely continuous and has the prescribed strong derivative
almost everywhere. Combining this with the weak fundamental theorem rules out singular
continuous curves in weak evolution uniqueness statements.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A prescribed primitive is absolutely continuous, has its integrand as
strong derivative almost everywhere, and satisfies the distributional identity. -/
theorem regularity_of_eq_initial_add_integral {a b : ℝ} (hab : a ≤ b)
    {u g : ℝ → X} (hg : IntegrableOn g (Ioc a b)) {q : X}
    (hFTC : ∀ t ∈ Icc a b, u t = q + ∫ r in a..t, g r) :
    AbsolutelyContinuousOnInterval u a b ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt u (g t) t) ∧
      HasWeakTimeDerivativeOn (Ioo a b) u g := by
  obtain ⟨Q, _, _, hQFTC, hQAC, hQderiv, hQweak⟩ :=
    exists_initial_primitive_of_integrableOn hg q
  have heq : EqOn u Q (Icc a b) := fun t ht ↦ (hFTC t ht).trans (hQFTC t ht).symm
  refine ⟨hQAC.congr (by simpa only [uIcc_of_le hab] using heq.symm), ?_, ?_⟩
  · have hd := hQderiv.filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))
    filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with t ht htab
    apply ht.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds htab] with r hr
    exact heq (Ioo_subset_Icc_self hr)
  · apply hQweak.congr_ae_restrict measurableSet_Ioo _ EventuallyEq.rfl
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (heq (Ioo_subset_Icc_self ht)).symm

/-- A continuous curve with an integrable distributional derivative is absolutely
continuous on the closed interval and has that strong derivative almost everywhere. -/
theorem HasWeakTimeDerivativeOn.absolutelyContinuousOnInterval_and_ae_hasDerivAt
    {a b : ℝ} (hab : a < b) {u g : ℝ → X}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) u g)
    (hu : ContinuousOn u (Icc a b)) (hg : IntegrableOn g (Ioo a b)) :
    AbsolutelyContinuousOnInterval u a b ∧
      ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt u (g t) t := by
  have hFTC (t : ℝ) (ht : t ∈ Icc a b) :
      u t = u a + ∫ r in a..t, g r := by
    rw [hweak.integral_eq_sub_of_continuousOn hab hu hg ⟨le_rfl, hab.le⟩ ht]
    abel
  have h := regularity_of_eq_initial_add_integral hab.le
    ((integrableOn_congr_set_ae Ioo_ae_eq_Ioc).1 hg) hFTC
  exact ⟨h.1, h.2.1⟩

end PDE.Analysis.Evolution
