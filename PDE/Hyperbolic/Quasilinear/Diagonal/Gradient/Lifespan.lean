/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Quasilinear.Diagonal.Gradient.Transport
public import PDE.Hyperbolic.Quasilinear.Diagonal.Gradient.Bounds
public import PDE.Analysis.Calculus.Transport.Characteristics
public import PDE.Solution.Singularity.FiniteTime.Comparison.QuadraticGrowth
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# A lifespan bound from a compressive initial slope

For two genuinely nonlinear diagonal equations, a bounded initial range fixes
positive constants before the candidate and the time interval. The PDE
preserves that range, gives finite characteristics, and evolves a weighted slope
by a Riccati equation. The initial slope is derived from the closure jet.
-/

@[expose] public noncomputable section

open Set
open PDE.Analysis PDE.Analysis.Transport
open PDE.Solution.Singularity.FiniteTime.QuadraticGrowth

namespace PDE.Hyperbolic.Quasilinear.Diagonal

variable {B : Fin 2 → (Fin 2 → ℝ) → ℝ}

/-- A compressive slope bounds the length of every closed classical time slab.
The constants depend only on the speeds and the initial range bound. The
candidate supplies its original diagonal PDE and values, not trajectories,
range estimates, or a differentiated equation. -/
theorem exists_uniform_lifespan_constants (hB : ∀ i, ContDiff ℝ 1 (B i))
    (hgap : ∀ i z, B i z ≠ B i.rev z) (hpos : ∀ i z, 0 < fderiv ℝ (B i) z (Pi.single i 1)) (R : ℝ) :
    ∃ κ : Fin 2 → ℝ, (∀ i, 0 < κ i) ∧
      ∀ (g : ℝ → Fin 2 → ℝ),
        (∀ x i, -R ≤ g x i ∧ g x i ≤ R) →
      ∀ (T : ℝ), 0 < T →
      ∀ (v : ℝ × ℝ → Fin 2 → ℝ)
        (_ : ContinuousSecondJetOn v (Ioo (0 : ℝ) T ×ˢ univ)),
        (∀ x, v (0, x) = g x) →
        (∀ p : ℝ × ℝ, p.1 ∈ Ioo 0 T → ∀ i,
          fderiv ℝ v p (1, B i (v p)) i = 0) →
      ∀ (i : Fin 2) (x₀ : ℝ), deriv (fun x ↦ g x i) x₀ < 0 →
        T < (κ i * (-deriv (fun x ↦ g x i) x₀))⁻¹ := by
  classical
  choose κ hκ hκbound using fun i ↦ exists_pos_le_weighted_coefficient hB hgap hpos R i
  refine ⟨κ, hκ, fun g hg T hT v hv hinit hpde i x₀ hneg ↦ ?_⟩
  have hinitbound : ∀ x j, -R ≤ v (0, x) j ∧ v (0, x) j ≤ R := fun x j ↦ hinit x ▸ hg x j
  obtain ⟨α, hα₀, hαcont, hαwithin⟩ := exists_characteristic_on_timeSlab hT hB hv hinitbound hpde i
      ⟨0, le_rfl, hT.le⟩ x₀
  have hα : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt α (B i (v (t, α t))) t :=
    fun t ht ↦ (hαwithin t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  let z := g x₀
  have hconst : ∀ t ∈ Icc (0 : ℝ) T, z i = v (t, α t) i := fun t ht ↦ by
    simpa only [hα₀, hinit, z] using
      (value_eq_initial_along_characteristic hT hv hpde hαcont i hα ht).symm
  have hclosure : closure (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) = Icc (0 : ℝ) T ×ˢ univ := by
    rw [closure_prod_eq, closure_Ioo hT.ne, closure_univ]
  have hcont : ContinuousOn v (Icc (0 : ℝ) T ×ˢ univ) := hclosure ▸ hv.continuousOn
  have hrange := rectangle_on_timeSlab hT (fun j ↦ (hB j).continuous)
    (fun j ↦ (continuous_apply j).comp_continuousOn hcont) hinitbound (by
      intro p hp j
      refine ⟨(ContinuousLinearMap.proj j).comp (hv.first p),
        (hasFDerivAt_pi'.mp (hv.hasFDerivAt (isOpen_Ioo.prod isOpen_univ) ⟨hp, mem_univ _⟩)) j, ?_⟩
      change hv.first p (1, B j (v p)) j = 0
      rw [hv.first_eq ⟨hp, mem_univ _⟩]
      exact hpde p hp j)
  have hz : z ∈ Icc (fun _ ↦ -R) (fun _ ↦ R) := ⟨fun j ↦ (hg x₀ j).1, fun j ↦ (hg x₀ j).2⟩
  have hvcurve : ∀ t ∈ Icc (0 : ℝ) T, v (t, α t) ∈ Icc (fun _ ↦ -R) (fun _ ↦ R) :=
    fun t ht ↦ ⟨fun j ↦ (hrange (t, α t) ht j).1, fun j ↦ (hrange (t, α t) ht j).2⟩
  have hpath : ContinuousOn (fun t ↦ (t, α t)) (Icc (0 : ℝ) T) := continuousOn_id.prodMk hαcont
  have hmaps : MapsTo (fun t ↦ (t, α t)) (Icc (0 : ℝ) T)
      (Icc (0 : ℝ) T ×ˢ univ) := fun _ ht ↦ ⟨ht, mem_univ _⟩
  have hycont : ContinuousOn (weightedSlope B hv i z α) (Icc (0 : ℝ) T) :=
    (((continuous_spatialWeight hB hgap i z).comp_continuousOn
      ((continuous_apply i.rev).comp_continuousOn (hcont.comp hpath hmaps))).mul
      ((continuous_apply i).comp_continuousOn
        (((hclosure ▸ hv.continuousOn_first).comp hpath hmaps).clm_apply continuousOn_const))).neg
  have hyd : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt (weightedSlope B hv i z α)
        ((fderiv ℝ (B i) (v (t, α t)) (Pi.single i 1) / spatialWeight B i z (v (t, α t) i.rev)) *
          weightedSlope B hv i z α t ^ 2) t := fun t ht ↦
    hasDerivAt_weightedSlope hB hgap hv (isOpen_Ioo.prod isOpen_univ)
      (fun p hp j ↦ hpde p hp.1 j) i z ⟨ht, mem_univ _⟩
      (hconst t (Ioo_subset_Icc_self ht)) (hα t ht)
  have htrace := (hasDerivAt_pi.mp (hv.hasDerivAt_initial_data hT hinit x₀) i).deriv
  have hy₀ : weightedSlope B hv i z α 0 = -deriv (fun x ↦ g x i) x₀ := by
    simp only [weightedSlope, hα₀, hinit]
    rw [show g x₀ = z from rfl, spatialWeight_initial, one_mul]
    exact congrArg Neg.neg htrace.symm
  have hbound := right_endpoint_lt_riccati_horizon
      (hκ i) (by rw [hy₀]; exact neg_pos.mpr hneg)
      hycont (fun t ht ↦ (hyd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ by
        rw [(hyd t ht).deriv]
        exact mul_le_mul_of_nonneg_right
          (hκbound i z hz (v (t, α t)) (hvcurve t (Ioo_subset_Icc_self ht))) (sq_nonneg _))
  simpa only [hy₀, zero_add] using hbound

end PDE.Hyperbolic.Quasilinear.Diagonal
