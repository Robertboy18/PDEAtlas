/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.HeightAverage
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Operator
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.FirstOrder
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.HeightAverage.Smooth
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Density
import PDE.Spaces.Sobolev.Calculus.Differentiation.VectorValued.ClassicalToWeak

/-!
# Height averages recover the Banach-valued trace

Averaging over a strip of height `ε` approximates the physical trace. The error in
boundary `Lᵖ`, raised to the power `p`, is bounded by `ε ^ (p - 1)` times the
normal derivative energy. The estimate holds first for compact smooth representatives;
density transfers it to the Sobolev graph. Thus the strip averages converge
to the trace whenever `p > 1`, for arbitrary real Banach targets.
-/

public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open GraphSpace SobolevSpace.Trace.HalfSpace

variable (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [Fact (1 ≤ ENNReal.ofReal p)] [NormedSpace ℝ F] [CompleteSpace F] in
private theorem ofReal_norm_rpow_eq_lintegral (hp : 0 < p)
    (v : Lp F (ENNReal.ofReal p) (volume : Measure (ℝ^n))) :
    ENNReal.ofReal (‖v‖ ^ p) = ∫⁻ y : ℝ^n, ENNReal.ofReal (‖v y‖ ^ p) := by
  have hi : Integrable (fun y : ℝ^n ↦ ‖v y‖ ^ p) := by
    simpa only [ENNReal.toReal_ofReal hp.le] using
      (Lp.memLp v).integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp)
        ENNReal.ofReal_ne_top
  have hn : ‖v‖ ^ p = ∫ y : ℝ^n, ‖v y‖ ^ p := by
    simpa only [ENNReal.toReal_ofReal hp.le] using
      Lp.norm_rpow_eq_integral (ENNReal.ofReal_ne_zero_iff.mpr hp)
        ENNReal.ofReal_ne_top v
  rw [hn]
  exact ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun y ↦ Real.rpow_nonneg (norm_nonneg _) _)

private theorem norm_heightAverageLp_sub_traceLp_rpow_le_of_contDiff
    (hp : 1 ≤ p) (ε : ℝ) (hε : 0 < ε)
    (V : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F))
    {f : ℝ^(n + 1) → F} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hV : (V.val (baseIndex (n + 1) 1) : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] f) :
    ‖heightAverageLp n p hp ε hε (coordinateCLM (baseIndex (n + 1) 1) V) -
        traceLp n p hp V‖ ^ p ≤
      ε ^ (p - 1) * ‖∂[Fin.last n] V‖ ^ p := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  let A := heightAverageLp (F := F) n p hp ε hε
  have hA :
      (A (coordinateCLM (baseIndex (n + 1) 1) V) : ℝ^n → F) =ᵐ[volume] fun y ↦
        ε⁻¹ • ∫ t in Ioc (0 : ℝ) ε, normalSlice f y t := by
    simpa only [A, coordinateCLM_apply, normalSlice] using
      heightAverageLp_eq_integral_of_ae_eq n p hp ε hε _ hV
  have hb := traceLp_coeFn_ae hp V hf hfc hV
  let v : Lp F (ENNReal.ofReal p) (volume : Measure (ℝ^n)) :=
    A (coordinateCLM (baseIndex (n + 1) 1) V) - traceLp n p hp V
  have hrep : (v : ℝ^n → F) =ᵐ[volume] fun y ↦
      ε⁻¹ • (∫ t in Ioc (0 : ℝ) ε, normalSlice f y t) - normalSlice f y 0 :=
    (Lp.coeFn_sub _ _).trans (hA.sub hb)
  have hnormal : ‖∂[Fin.last n] V‖ ^ p =
      ∫ z in ℝ^(n + 1)₊, ‖(∂[Fin.last n] f) z‖ ^ p := by
    rw [norm_partialDeriv_eq_coordinate]
    have henergy := Lp.norm_rpow_eq_integral (ENNReal.ofReal_ne_zero_iff.mpr hp₀)
      ENNReal.ofReal_ne_top (V.val (singleDerivIndex (n + 1) (Fin.last n)))
    rw [ENNReal.toReal_ofReal hp₀.le] at henergy
    exact henergy.trans (integral_congr_ae
      ((coordinate_ae_partialDeriv_of_contDiffOn V hf.contDiffOn hV (Fin.last n)).fun_comp
        fun z : F ↦ ‖z‖ ^ p))
  apply (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.rpow_nonneg hε.le _)
      (Real.rpow_nonneg (norm_nonneg _) _))).mp
  calc
    _ = ∫⁻ y : ℝ^n, ENNReal.ofReal
        (‖ε⁻¹ • (∫ t in Ioc (0 : ℝ) ε, normalSlice f y t) -
          normalSlice f y 0‖ ^ p) := by
      rw [ofReal_norm_rpow_eq_lintegral n p hp₀]
      exact lintegral_congr_ae (hrep.fun_comp fun z : F ↦ ENNReal.ofReal (‖z‖ ^ p))
    _ ≤ ENNReal.ofReal (ε ^ (p - 1) *
        ∫ z in ℝ^(n + 1)₊, ‖(∂[Fin.last n] f) z‖ ^ p) :=
      lintegral_height_average_sub_le hf hfc hp hε
    _ = _ := by rw [hnormal]

/-- The normal derivative controls the boundary `p`-energy of the difference between
a strip average and the trace. At exponent one the same estimate remains valid. -/
theorem norm_heightAverageLp_sub_traceLp_rpow_le
    (hp : 1 ≤ p) (ε : ℝ) (hε : 0 < ε)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    ‖heightAverageLp n p hp ε hε (coordinateCLM (baseIndex (n + 1) 1) U) -
        traceLp n p hp U‖ ^ p ≤
      ε ^ (p - 1) * ‖∂[Fin.last n] U‖ ^ p := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  let A := heightAverageLp (F := F) n p hp ε hε
  refine le_on_closure (s := {V |
      ∃ f : ℝ^(n + 1) → F, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
        (V.val (baseIndex (n + 1) 1) : ℝ^(n + 1) → F)
          =ᵐ[volume.restrict ℝ^(n + 1)₊] f})
    (f := fun V :
        W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F) ↦
      ‖A (coordinateCLM (baseIndex (n + 1) 1) V) - traceLp n p hp V‖ ^ p)
    (g := fun V :
        W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F) ↦
      ε ^ (p - 1) * ‖∂[Fin.last n] V‖ ^ p) ?_ ?_ ?_
    (dense_compact_smooth ENNReal.ofReal_ne_top U)
  · rintro V ⟨f, hf, hfc, hV⟩
    exact norm_heightAverageLp_sub_traceLp_rpow_le_of_contDiff n p hp ε hε V
      (hf.of_le (by simp)) hfc hV
  · exact ((A.continuous.comp (coordinateCLM (baseIndex (n + 1) 1)).continuous).sub
      (traceLp n p hp).continuous).norm.rpow_const
        (fun _ ↦ Or.inr hp₀.le) |>.continuousOn
  · have hnormal : Continuous (fun V :
          W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
            SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F) ↦ ‖∂[Fin.last n] V‖) := by
      simpa only [norm_partialDeriv_eq_coordinate, coordinateCLM_apply] using
        (coordinateCLM (F := F) (p := ENNReal.ofReal p)
          (Ω := ⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩)
          (singleDerivIndex (n + 1) (Fin.last n))).continuous.norm
    exact ((hnormal.rpow_const (fun _ ↦ Or.inr hp₀.le)).const_mul _).continuousOn

/-- Every positive height scale tending to zero recovers the physical trace in
boundary `Lᵖ`. Only the Sobolev element, not a choice of representative, enters the limit. -/
theorem tendsto_heightAverageLp_of_tendsto
    (hp : 1 < p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F))
    {ι : Type*} {l : Filter ι} (ε : ι → ℝ)
    (hε : ∀ i, 0 < ε i) (hε₀ : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i ↦ heightAverageLp n p hp.le (ε i) (hε i)
      (coordinateCLM (baseIndex (n + 1) 1) U)) l (𝓝 (traceLp n p hp.le U)) := by
  have hp₀ : 0 < p := zero_lt_one.trans hp
  have hright : Tendsto
      (fun i ↦ ε i ^ (p - 1) * ‖∂[Fin.last n] U‖ ^ p) l (𝓝 0) := by
    simpa only [zero_mul] using
      (hε₀.rpow_const_nhds_zero (sub_pos.mpr hp)).mul_const _
  have hpower : Tendsto
      (fun i ↦ ‖heightAverageLp n p hp.le (ε i) (hε i)
        (coordinateCLM (baseIndex (n + 1) 1) U) - traceLp n p hp.le U‖ ^ p) l (𝓝 0) :=
    squeeze_zero (fun i ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (fun i ↦ norm_heightAverageLp_sub_traceLp_rpow_le n p hp.le (ε i) (hε i) U) hright
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.rpow_rpow_inv (norm_nonneg _) hp₀.ne'] using
    hpower.rpow_const_nhds_zero (inv_pos.mpr hp₀)

/-- The strip averages converge to the trace as height tends to zero from above,
including when the boundary is zero-dimensional. -/
theorem tendsto_heightAverageLp
    (hp : 1 < p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    Tendsto (fun ε : Ioi (0 : ℝ) ↦ heightAverageLp n p hp.le ε ε.2
      (coordinateCLM (baseIndex (n + 1) 1) U))
      (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 (traceLp n p hp.le U)) :=
  tendsto_heightAverageLp_of_tendsto n p hp U
    (fun ε : Ioi (0 : ℝ) ↦ (ε : ℝ)) (fun ε ↦ ε.2)
    (tendsto_comap.mono_right nhdsWithin_le_nhds)

end SobolevSpace.VectorValued.Trace.HalfSpace
