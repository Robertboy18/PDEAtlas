/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
import CAS.ExactTactic

/-!
# Joining two closed time slabs

The second slab is translated to start at the first slab's terminal time.
Constant time extensions outside the two slabs make continuity statements
global. Matching one-sided derivatives give an ordinary derivative at the join.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace DeGregorio.Iteration

/-- Concatenate two fields, extending constantly before the first initial time
and after the second terminal time. -/
def joinTimeSlabs {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (w z : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  if t ≤ T then w x (projIcc 0 T hT t) else z x (projIcc 0 S hS (t - T))

/-- The joined field agrees with the first field on its closed slab. -/
theorem joinTimeSlabs_eq_left {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (w z : ℝ → ℝ → ℝ) (x : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    joinTimeSlabs hT hS w z x t = w x t := by
  simp only [joinTimeSlabs, ite_eq_left ht.2, projIcc_of_mem hT ht]

/-- Matching endpoint values identify the whole second closed slab. -/
theorem joinTimeSlabs_eq_right {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    {w z : ℝ → ℝ → ℝ} (hmatch : ∀ x, w x T = z x 0)
    (x : ℝ) {t : ℝ} (ht : t ∈ Icc T (T + S)) :
    joinTimeSlabs hT hS w z x t = z x (t - T) := by
  by_cases hleft : t ≤ T
  · have heq : t = T := le_antisymm hleft ht.1
    subst t
    rw [joinTimeSlabs_eq_left hT hS w z x ⟨hT, le_rfl⟩, sub_self, hmatch]
  · have hsub : t - T ∈ Icc 0 S := ⟨sub_nonneg.mpr ht.1, sub_le_iff_le_add.mpr
      (by simpa only [add_comm S T] using ht.2)⟩
    simp only [joinTimeSlabs, ite_eq_right hleft, projIcc_of_mem hS hsub]

/-- Closed-slab continuity and matching values give a continuous joined field. -/
theorem continuous_joinTimeSlabs {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    {w z : ℝ → ℝ → ℝ}
    (hw : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ w p.1 p.2))
    (hz : Continuous (fun p : ℝ × Icc (0 : ℝ) S ↦ z p.1 p.2))
    (hmatch : ∀ x, w x T = z x 0) :
    Continuous (Function.uncurry (joinTimeSlabs hT hS w z)) := by
  apply (hw.comp
    (continuous_fst.prodMk ((continuous_projIcc (h := hT)).comp continuous_snd))).if_le
    (hz.comp (continuous_fst.prodMk ((continuous_projIcc (h := hS)).comp
      (continuous_snd.sub continuous_const)))) continuous_snd continuous_const
  intro p hp
  change w p.1 (projIcc 0 T hT p.2) = z p.1 (projIcc 0 S hS (p.2 - T))
  rw [hp, sub_self, projIcc_of_mem hT ⟨hT, le_rfl⟩,
    projIcc_of_mem hS ⟨le_rfl, hS⟩, hmatch]

/-- Inside the first slab the joined time section agrees locally with the original. -/
theorem joinTimeSlabs_eventuallyEq_left {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (w z : ℝ → ℝ → ℝ) (x : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    joinTimeSlabs hT hS w z x =ᶠ[𝓝 t] w x := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact joinTimeSlabs_eq_left hT hS w z x (Ioo_subset_Icc_self hs)

/-- Inside the second slab the joined time section is locally a time translate. -/
theorem joinTimeSlabs_eventuallyEq_right {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    {w z : ℝ → ℝ → ℝ} (hmatch : ∀ x, w x T = z x 0)
    (x : ℝ) {t : ℝ} (ht : t ∈ Ioo T (T + S)) :
    joinTimeSlabs hT hS w z x =ᶠ[𝓝 t] fun s ↦ z x (s - T) := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact joinTimeSlabs_eq_right hT hS hmatch x (Ioo_subset_Icc_self hs)

/-- Equal one-sided derivatives become an ordinary time derivative at the join. -/
theorem hasDerivAt_joinTimeSlabs_join {T S : ℝ} (hT : 0 < T) (hS : 0 < S)
    {w z : ℝ → ℝ → ℝ} (hmatch : ∀ x, w x T = z x 0)
    (x q : ℝ) (hw : HasDerivWithinAt (w x) q (Iic T) T)
    (hz : HasDerivWithinAt (z x) q (Ici 0) 0) :
    HasDerivAt (joinTimeSlabs hT.le hS.le w z x) q T := by
  have hleft : HasDerivWithinAt (joinTimeSlabs hT.le hS.le w z x) q (Iic T) T := by
    apply hw.congr_of_eventuallyEq_of_mem _ (show T ∈ Iic T from le_rfl)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hT),
      self_mem_nhdsWithin] with t ht htT
    exact joinTimeSlabs_eq_left hT.le hS.le w z x ⟨ht.le, htT⟩
  have hshift : HasDerivWithinAt (fun t ↦ z x (t - T)) q (Ici T) T := by
    have hsub : HasDerivWithinAt (fun t : ℝ ↦ t - T) 1 (Ici T) T := by
      cas
    have hd := hz.comp_of_eq T hsub
      (fun t ht ↦ sub_nonneg.mpr ht) (sub_self T).symm
    simpa only [Function.comp_def, mul_one] using hd
  have hright : HasDerivWithinAt (joinTimeSlabs hT.le hS.le w z x) q (Ici T) T := by
    apply hshift.congr_of_eventuallyEq_of_mem _ (show T ∈ Ici T from le_rfl)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Iio_mem_nhds (lt_add_of_pos_right T hS)), self_mem_nhdsWithin] with t ht htT
    exact joinTimeSlabs_eq_right hT.le hS.le hmatch x ⟨htT, ht.le⟩
  rw [← hasDerivWithinAt_univ, ← Iic_union_Ici]
  exact hleft.union hright

end DeGregorio.Iteration
