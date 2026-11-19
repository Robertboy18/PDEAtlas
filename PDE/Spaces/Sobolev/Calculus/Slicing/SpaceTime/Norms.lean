/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.SpaceTime.FiniteProduct
import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert
import PDE.Analysis.MeasureTheory.Lp.Fubini

/-!
# Norms of spacetime Sobolev slices

The spatial H¹ and temporal L² contributions partition the joint spacetime H¹
graph norm. Measure preservation and Fubini recover this norm from the
almost-everywhere coordinate identities.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Slices

open Filter MeasureTheory Set PDE.Common GraphSpace
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {I : Set ℝ}

/-- The integrated squared norm of actual L² sections equals the original
spacetime L² norm. Fubini supplies the quantitative content of the row identity. -/
theorem integral_norm_sq_timeSlice_eq
    (u : Lp ℝ 2 (volume.restrict {y : ℝ^(n + 1) | y 0 ∈ I}))
    (v : ℝ → DerivLp n 2 univ)
    (hv : ∀ᵐ t ∂volume.restrict I, ∀ᵐ x ∂volume,
      v t x = u (timeSpaceCons t x)) :
    (∫ t, ‖v t‖ ^ 2 ∂volume.restrict I) = ‖u‖ ^ 2 := by
  let U := Lp.compMeasurePreserving (timeSpaceContinuousLinearEquiv n).symm
    (measurePreserving_timeSpaceCons_restrict I) u
  have hU : ∀ᵐ t ∂volume.restrict I, ∀ᵐ x ∂volume,
      U (t, x) = u (timeSpaceCons t x) := by
    simpa only [Function.comp_def, timeSpaceContinuousLinearEquiv_symm_apply] using
      Measure.ae_ae_of_ae_prod (Lp.coeFn_compMeasurePreserving u
        (measurePreserving_timeSpaceCons_restrict I))
  calc
    _ = ∫ t, ∫ x, ‖U (t, x)‖ ^ 2 ∂volume ∂volume.restrict I := by
      apply integral_congr_ae
      filter_upwards [hv, hU] with t ht hUt
      rw [Lp.norm_sq_eq_integral_norm_sq]
      simp only [domainMeasure, Measure.restrict_univ]
      apply integral_congr_ae
      filter_upwards [ht, hUt] with x hx hUx
      rw [hx, hUx]
    _ = ‖U‖ ^ 2 := by
      rw [Lp.norm_sq_eq_integral_norm_sq,
        integral_prod_real _ ((Lp.memLp U).norm.integrable_sq)]
    _ = ‖u‖ ^ 2 := by rw [Lp.norm_compMeasurePreserving]

private theorem integral_norm_sq_h1_timeSlice_eq
    (f : W^{1,2}(({y | y 0 ∈ I} : Set (ℝ^(n + 1)))))
    (F : ℝ → W^{1,2}(ℝ^n)) (hF : MemLp F 2 (volume.restrict I))
    (hbase : ∀ᵐ t ∂volume.restrict I, ∀ᵐ x ∂volume,
      wkpBaseCoordinateCLM (F t) x = wkpBaseCoordinateCLM f (timeSpaceCons t x))
    (hfirst : ∀ᵐ t ∂volume.restrict I, ∀ᵐ x ∂volume, ∀ j,
      wkpCoordinateCLM (singleDerivIndex n j) (F t) x =
        wkpCoordinateCLM (singleDerivIndex (n + 1) j.succ) f (timeSpaceCons t x)) :
    (∫ t, ‖F t‖ ^ 2 ∂volume.restrict I) =
      ‖wkpBaseCoordinateCLM f‖ ^ 2 + ∑ j : Fin n,
        ‖wkpCoordinateCLM (singleDerivIndex (n + 1) j.succ) f‖ ^ 2 := by
  have hrow (α : DerivIndex n 1) :
      MemLp (fun t ↦ wkpCoordinateCLM α (F t)) 2 (volume.restrict I) :=
    (wkpCoordinateCLM α : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ).comp_memLp' hF
  calc
    _ = ∫ t, ‖wkpBaseCoordinateCLM (F t)‖ ^ 2 +
        ∑ j : Fin n, ‖wkpCoordinateCLM (singleDerivIndex n j) (F t)‖ ^ 2
          ∂volume.restrict I := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t ↦
        ambient_norm_sq_eq_base_sq_add_sum_deriv_sq (F t).val
    _ = (∫ t, ‖wkpBaseCoordinateCLM (F t)‖ ^ 2 ∂volume.restrict I) +
        ∑ j : Fin n, ∫ t, ‖wkpCoordinateCLM (singleDerivIndex n j) (F t)‖ ^ 2
          ∂volume.restrict I := by
      simp only [wkpBaseCoordinateCLM]
      rw [integral_add ((hrow (baseIndex n 1)).norm.integrable_sq)
        (integrable_finsetSum Finset.univ fun j _ ↦
          (hrow (singleDerivIndex n j)).norm.integrable_sq)]
      rw [integral_finsetSum Finset.univ fun j _ ↦
        (hrow (singleDerivIndex n j)).norm.integrable_sq]
    _ = _ := by
      congr 1
      · exact integral_norm_sq_timeSlice_eq _ _ hbase
      · apply Finset.sum_congr rfl
        intro j _
        apply integral_norm_sq_timeSlice_eq
        filter_upwards [hfirst] with t ht
        filter_upwards [ht] with x hx
        exact hx j

/-- The spatial H¹ and temporal L² slice norms exactly partition the original
finite-vector spacetime H¹ norm. Only the actual three row identifications enter. -/
theorem norm_sq_vector_timeSlices_add_timeDerivative_eq
    (f : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(({y | y 0 ∈ I} : Set (ℝ^(n + 1))))))
    (F : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2 (volume.restrict I))
    (G : Lp (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)) 2 (volume.restrict I))
    (hbase : ∀ᵐ t ∂volume.restrict I, ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM (F t p) x = wkpBaseCoordinateCLM (f p) (timeSpaceCons t x))
    (hfirst : ∀ᵐ t ∂volume.restrict I, ∀ᵐ x ∂volume, ∀ p j,
      wkpCoordinateCLM (singleDerivIndex n j) (F t p) x =
        wkpCoordinateCLM (singleDerivIndex (n + 1) j.succ) (f p) (timeSpaceCons t x))
    (htime : ∀ᵐ t ∂volume.restrict I, ∀ᵐ x ∂volume, ∀ p,
      G t p x = wkpCoordinateCLM (singleDerivIndex (n + 1) 0) (f p)
        (timeSpaceCons t x)) :
    ‖F‖ ^ 2 + ‖G‖ ^ 2 = ‖f‖ ^ 2 := by
  classical
  have hFp (p : Fin m) : MemLp (fun t ↦ F t p) 2 (volume.restrict I) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) p).comp_memLp F
  have hGp (p : Fin m) : MemLp (fun t ↦ G t p) 2 (volume.restrict I) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ DerivLp n 2 univ) p).comp_memLp G
  have hFpnorm (p : Fin m) : (∫ t, ‖F t p‖ ^ 2 ∂volume.restrict I) =
      ‖wkpBaseCoordinateCLM (f p)‖ ^ 2 + ∑ j : Fin n,
        ‖wkpCoordinateCLM (singleDerivIndex (n + 1) j.succ) (f p)‖ ^ 2 := by
    apply integral_norm_sq_h1_timeSlice_eq (f p) (fun t ↦ F t p) (hFp p)
    · filter_upwards [hbase] with t ht
      filter_upwards [ht] with x hx
      exact hx p
    · filter_upwards [hfirst] with t ht
      filter_upwards [ht] with x hx
      exact hx p
  have hGpnorm (p : Fin m) : (∫ t, ‖G t p‖ ^ 2 ∂volume.restrict I) =
      ‖wkpCoordinateCLM (singleDerivIndex (n + 1) 0) (f p)‖ ^ 2 := by
    apply integral_norm_sq_timeSlice_eq
    filter_upwards [htime] with t ht
    filter_upwards [ht] with x hx
    exact hx p
  rw [Lp.norm_sq_eq_integral_norm_sq F, Lp.norm_sq_eq_integral_norm_sq G]
  simp_rw [PiLp.norm_sq_eq_of_L2]
  rw [integral_finsetSum _ fun p _ ↦ (hFp p).norm.integrable_sq,
    integral_finsetSum _ fun p _ ↦ (hGp p).norm.integrable_sq,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [hFpnorm, hGpnorm]
  have hnorm := ambient_norm_sq_eq_base_sq_add_sum_deriv_sq (f p).val
  rw [Fin.sum_univ_succ] at hnorm
  change _ = ‖(f p).val‖ ^ 2
  rw [hnorm]
  simp only [wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply]
  ring

/-- A fixed numerical factor absorbs both actual slice norms into the original
joint spacetime H¹ norm, independently of the datum and time interval. -/
theorem norm_vector_timeSlices_add_timeDerivative_le
    (f : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(({y | y 0 ∈ I} : Set (ℝ^(n + 1))))))
    (F : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2 (volume.restrict I))
    (G : Lp (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)) 2 (volume.restrict I))
    (hbase : ∀ᵐ t ∂volume.restrict I, ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM (F t p) x = wkpBaseCoordinateCLM (f p) (timeSpaceCons t x))
    (hfirst : ∀ᵐ t ∂volume.restrict I, ∀ᵐ x ∂volume, ∀ p j,
      wkpCoordinateCLM (singleDerivIndex n j) (F t p) x =
        wkpCoordinateCLM (singleDerivIndex (n + 1) j.succ) (f p) (timeSpaceCons t x))
    (htime : ∀ᵐ t ∂volume.restrict I, ∀ᵐ x ∂volume, ∀ p,
      G t p x = wkpCoordinateCLM (singleDerivIndex (n + 1) 0) (f p)
        (timeSpaceCons t x)) :
    ‖F‖ + ‖G‖ ≤ 2 * ‖f‖ := by
  have hnorm := norm_sq_vector_timeSlices_add_timeDerivative_eq f F G hbase hfirst htime
  have hF : ‖F‖ ≤ ‖f‖ := by nlinarith [sq_nonneg ‖G‖, norm_nonneg F, norm_nonneg f]
  have hG : ‖G‖ ≤ ‖f‖ := by nlinarith [sq_nonneg ‖F‖, norm_nonneg G, norm_nonneg f]
  linarith

end SobolevSpace.Slices
