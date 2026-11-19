/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Linear

/-!
# Quadratic energy of the constructed whole-space evolution

The generator's two weak equations make it skew on the energy diagonal.
Differentiating its regular orbits and using density proves conservation for
every energy datum. Product coordinates then make the potential
chain rule available.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev InnerProductSpace SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ}

/-- Coordinates of the constructed Hilbert energy space. -/
def coordinates (n : ℕ) : EnergyState n ≃L[ℝ] H¹(ℝ^n) × DerivLp n 2 univ :=
  WaveEnergySpace.coordinates (massForm n) (massForm_coercive n) massForm_symmetric

/-- The whole-space wave generator is skew on its energy diagonal. -/
theorem inner_generator_eq_zero {x y : EnergyState n}
    (h : (linearSemigroup n).HasGeneratorAt x y) : ⟪x, y⟫_ℝ = 0 := by
  obtain ⟨hq, hp⟩ := linearSemigroup_generator h
  change (energyTriple n).inclusion (coordinates n y).1 = (coordinates n x).2 at hq
  have hpair := DFunLike.congr_fun hp (coordinates n y).1
  change massForm n (coordinates n x).1 (coordinates n y).1 =
    -⟪(coordinates n y).2, (energyTriple n).inclusion (coordinates n y).1⟫_ℝ at hpair
  rw [hq] at hpair
  rw [WaveEnergySpace.inner_eq]
  change massForm n (coordinates n x).1 (coordinates n y).1 +
    ⟪(coordinates n x).2, (coordinates n y).2⟫_ℝ = 0
  rw [hpair, real_inner_comm (coordinates n x).2, neg_add_cancel]

/-- Linear energy conservation first on the dense generator domain. -/
theorem norm_sq_linearSemigroup_of_mem_domain (t : NNReal)
    (x : (linearSemigroup n).generatorPMap.domain) :
    ‖linearSemigroup n t x‖ ^ 2 = ‖(x : EnergyState n)‖ ^ 2 := by
  have hd (s : ℝ) (hs : s ∈ Ico 0 (t : ℝ)) :
      HasDerivWithinAt (fun r ↦ ‖(linearSemigroup n).realOrbit x r‖ ^ 2)
        0 (Ici s) s := by
    have h := ((linearSemigroup n).hasGeneratorAt_generatorPMap x).hasDerivWithinAt_realOrbit
      ⟨s, hs.1⟩
    have hz := inner_generator_eq_zero
      (((linearSemigroup n).hasGeneratorAt_generatorPMap x).map ⟨s, hs.1⟩)
    have htime : s.toNNReal = ⟨s, hs.1⟩ := by
      ext
      exact Real.coe_toNNReal s hs.1
    have hh := h.norm_sq
    change HasDerivWithinAt (fun r ↦ ‖(linearSemigroup n).realOrbit x r‖ ^ 2)
      (2 * ⟪linearSemigroup n s.toNNReal x,
        linearSemigroup n ⟨s, hs.1⟩ ((linearSemigroup n).generatorPMap x)⟫_ℝ) (Ici s) s at hh
    rwa [htime, hz, mul_zero] at hh
  have he := constant_of_has_deriv_right_zero
    (((linearSemigroup n).continuous_realOrbit x).norm.pow 2).continuousOn hd
    (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  simpa only [Pi.pow_apply, StronglyContinuousSemigroup.realOrbit, Real.toNNReal_coe,
    Real.toNNReal_zero, StronglyContinuousSemigroup.map_zero_apply] using he

/-- Every energy datum has exactly conserved linear energy. -/
theorem norm_sq_linearSemigroup (t : NNReal) (x : EnergyState n) :
    ‖linearSemigroup n t x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hclosed : IsClosed {y : EnergyState n | ‖linearSemigroup n t y‖ ^ 2 = ‖y‖ ^ 2} :=
    isClosed_eq ((linearSemigroup n t).continuous.norm.pow 2) (continuous_norm.pow 2)
  apply closure_minimal (s := ((linearSemigroup n).generatorPMap.domain :
    Set (EnergyState n))) (fun y hy ↦ norm_sq_linearSemigroup_of_mem_domain t ⟨y, hy⟩) hclosed
  exact linearSemigroup_dense_domain n x

/-- The constructed whole-space massive wave semigroup in ordinary product coordinates. -/
def productSemigroup (n : ℕ) :
    StronglyContinuousSemigroup (H¹(ℝ^n) × DerivLp n 2 univ) where
  toMonoidHom :=
    { toFun := fun t ↦ (coordinates n).toContinuousLinearMap.comp
        ((linearSemigroup n t.toAdd).comp (coordinates n).symm.toContinuousLinearMap)
      map_one' := by
        refine ContinuousLinearMap.ext fun x ↦ ?_
        change coordinates n (linearSemigroup n 0 ((coordinates n).symm x)) = x
        rw [(linearSemigroup n).map_zero_apply, ContinuousLinearEquiv.apply_symm_apply]
      map_mul' := by
        intro s t
        refine ContinuousLinearMap.ext fun x ↦ ?_
        change coordinates n
          (linearSemigroup n (s.toAdd + t.toAdd) ((coordinates n).symm x)) =
            coordinates n (linearSemigroup n s.toAdd
              ((coordinates n).symm (coordinates n
                (linearSemigroup n t.toAdd ((coordinates n).symm x)))))
        rw [ContinuousLinearEquiv.symm_apply_apply, (linearSemigroup n).map_add_apply] }
  continuous_toPointwise := by
    refine PointwiseConvergenceCLM.continuous_of_continuous_eval fun x ↦ ?_
    exact (coordinates n).continuous.comp
      ((linearSemigroup n).continuous_orbit ((coordinates n).symm x))

/-- Product evolution has the same quadratic energy as the Hilbert evolution. -/
theorem productSemigroup_energy (t : NNReal) (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    autonomousWaveEnergy (massForm n) (productSemigroup n t x) =
      autonomousWaveEnergy (massForm n) x := by
  have h := norm_sq_linearSemigroup t ((coordinates n).symm x)
  rw [WaveEnergySpace.norm_sq_eq, WaveEnergySpace.norm_sq_eq] at h
  change massForm n (coordinates n (linearSemigroup n t ((coordinates n).symm x))).1
      (coordinates n (linearSemigroup n t ((coordinates n).symm x))).1 +
    ‖(coordinates n (linearSemigroup n t ((coordinates n).symm x))).2‖ ^ 2 =
      massForm n x.1 x.1 + ‖x.2‖ ^ 2
  simpa only [coordinates, ContinuousLinearEquiv.apply_symm_apply] using h

/-- Duhamel evolution commutes with the constructed product coordinates. -/
theorem productSemigroup_forced {f : ℝ → DerivLp n 2 univ} (hf : Continuous f)
    (x : H¹(ℝ^n) × DerivLp n 2 univ) (t : ℝ) :
    (productSemigroup n).realOrbit x t +
        (productSemigroup n).duhamel (fun s ↦ (0, f s)) t =
      coordinates n ((linearSemigroup n).realOrbit ((coordinates n).symm x) t +
        (linearSemigroup n).duhamel (fun s ↦ (coordinates n).symm (0, f s)) t) := by
  rw [map_add]
  congr 1
  have hcf : Continuous (fun s ↦ (coordinates n).symm (0, f s)) :=
    (coordinates n).symm.continuous.comp (continuous_const.prodMk hf)
  have hc := (linearSemigroup n).continuous_duhamelIntegrand hcf t
  exact (coordinates n).toContinuousLinearMap.intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := volume) 0 t)

/-- Both weak equations for forced product evolution, for arbitrary energy data. -/
theorem productSemigroup_forced_integral {f : ℝ → DerivLp n 2 univ} (hf : Continuous f)
    (x : H¹(ℝ^n) × DerivLp n 2 univ) {t : ℝ} (ht : 0 ≤ t) :
    let z := fun s ↦ (productSemigroup n).realOrbit x s +
      (productSemigroup n).duhamel (fun r ↦ (0, f r)) s
    (∫ s in (0 : ℝ)..t, (z s).2) =
        (energyTriple n).inclusion (z t).1 - (energyTriple n).inclusion x.1 ∧
      (∫ s in (0 : ℝ)..t,
        (energyTriple n).pivotToDual (f s) - massForm n (z s).1) =
        (energyTriple n).pivotToDual (z t).2 - (energyTriple n).pivotToDual x.2 := by
  simp only [productSemigroup_forced hf]
  simpa only [coordinates, ContinuousLinearEquiv.apply_symm_apply] using
    linear_forced_integral hf ((coordinates n).symm x) ht

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing
