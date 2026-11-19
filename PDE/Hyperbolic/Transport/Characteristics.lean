/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Representations.Similarity.Dynamic
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Recovering a classical transport equation from characteristics

The inverse flow turns a classical characteristic amplitude into a classical
Eulerian field. Differentiating that field along a trajectory then recovers
`w_t + b w_x = c w`. Only interior time regularity is needed; the characteristic
identities may hold on a closed interval.
-/

@[expose] public section

noncomputable section

open Set
open scoped Topology

namespace TransportEquation

/-- A classical inverse flow and amplitude recover the Eulerian transport
equation. The characteristic derivative is the only evolution hypothesis. -/
theorem contDiffOn_transport_of_characteristics {T : ℝ} {b c X Y w : ℝ → ℝ → ℝ} {V : ℝ × ℝ → ℝ}
    (hY : ContDiffOn ℝ 1 (Function.uncurry Y) (univ ×ˢ Ioo (0 : ℝ) T))
    (hV : ContDiffOn ℝ 1 V (univ ×ˢ Ioo (0 : ℝ) T))
    (hXY : ∀ x t, t ∈ Icc (0 : ℝ) T → X (Y x t) t = x)
    (hformula : ∀ x t, t ∈ Icc (0 : ℝ) T → w (X x t) t = V (x, t))
    (hX : ∀ x t, t ∈ Icc (0 : ℝ) T → HasDerivAt (X x) (b (X x t) t) t)
    (hchar : ∀ x t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (fun s ↦ w (X x s) s) (c (X x t) t * w (X x t) t) (Icc (0 : ℝ) T) t) :
    ContDiffOn ℝ 1 (Function.uncurry w) (univ ×ˢ Ioo (0 : ℝ) T) ∧
      ∀ x t, t ∈ Ioo (0 : ℝ) T → deriv (w x) t + b x t * deriv (fun y ↦ w y t) x =
        c x t * w x t := by
  have hw : ContDiffOn ℝ 1 (Function.uncurry w) (univ ×ˢ Ioo (0 : ℝ) T) := by
    have hcomp := hV.comp (hY.prodMk contDiffOn_snd) (fun p hp ↦ ⟨mem_univ _, hp.2⟩)
    refine hcomp.congr fun p hp ↦ ?_
    change w p.1 p.2 = V (Y p.1 p.2, p.2)
    simpa only [hXY p.1 p.2 (Ioo_subset_Icc_self hp.2)] using
      hformula (Y p.1 p.2) p.2 (Ioo_subset_Icc_self hp.2)
  refine ⟨hw, fun x t ht ↦ ?_⟩
  let y : ℝ := Y x t
  have hxy : X y t = x := hXY x t (Ioo_subset_Icc_self ht)
  have hwAt : DifferentiableAt ℝ (Function.uncurry w) (x, t) := (hw.contDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ x, ht⟩)).differentiableAt (by simp)
  have hpath : HasDerivAt (fun s ↦ (X y s, s)) (b x t, 1) t := by
    simpa only [hxy, id_eq] using (hX y t (Ioo_subset_Icc_self ht)).prodMk (hasDerivAt_id t)
  have hwAtPath : HasFDerivAt (Function.uncurry w)
      (fderiv ℝ (Function.uncurry w) (x, t)) (X y t, t) := by
    rw [hxy]
    exact hwAt.hasFDerivAt
  have hcomp : HasDerivAt (fun s ↦ w (X y s) s)
      (fderiv ℝ (Function.uncurry w) (x, t) (b x t, 1)) t := by
    convert hwAtPath.comp_hasDerivAt (f := fun s ↦ (X y s, s)) t hpath using 1
    funext s
    rfl
  have hrate : HasDerivAt (fun s ↦ w (X y s) s) (c x t * w x t) t := by
    simpa only [hxy] using (hchar y t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have heq := hcomp.unique hrate
  rw [PDE.Representations.Similarity.fderiv_uncurry_apply_prod w x (b x t) t 1 hwAt] at heq
  simpa only [fderiv_eq_smul_deriv, smul_eq_mul, one_mul, add_comm] using heq

end TransportEquation
