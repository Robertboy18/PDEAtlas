/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Output
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.TerminalClosure
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.VelocityIdentification

/-!
# A physical trajectory as a coupled H² output

`IsHkFrozenOutput` lists analytic properties of the fields and does not refer to how
they were constructed. A classical solution of the physical equation with `u(0, t) = 0`
and a continuous bounded supported H² base has these properties. The equation and
compact Sobolev continuity supply joint C¹ regularity.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis
open SobolevSpace SobolevSpace.GraphSpace
open scoped Topology Sobolev

namespace DeGregorio.Iteration

/-- A classical physical solution on `(0, T)` with `u(0, t) = 0`, jointly continuous
vorticity on `ℝ × [0, T]`, and a continuous bounded supported H² base is a coupled
frozen output on `[0, T]`. Theorems about `IsHkFrozenOutput` therefore apply to
continued solutions. -/
theorem exists_isHkFrozenOutput_of_classical
    {B : NNReal} {T R : ℝ} (hT : 0 ≤ T)
    (F : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B))
    {fields : Fields} (hsol : IsClassicalSolutionOn 1 fields (Ioo 0 T))
    (hw : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ fields.vorticity p.1 p.2))
    (hrep : ∀ t, (oneDimensionalPushforwardL2 (F t).val : ℝ → ℝ)
      =ᵐ[volume] fun x ↦ fields.vorticity x t)
    (hsupport : ∀ t ∈ Icc 0 T, tsupport (fun x ↦ fields.vorticity x t) ⊆ Icc (-R) R)
    (hzero : ∀ t ∈ Ioo 0 T, fields.velocity 0 t = 0) :
    ∃ (W₀ : W^{2,2}(ℝ^1)) (c : ℝ → ℝ → ℝ),
      IsHkFrozenOutput hT F F W₀ (fun x ↦ fields.vorticity x 0) c fields.vorticity := by
  have hbase : Continuous (fun t ↦ (F t).val) := continuous_subtype_val.comp F.continuous
  have hball (t : Icc (0 : ℝ) T) := (F t).property.1
  have hwc (t : Icc (0 : ℝ) T) : Continuous (fun x ↦ fields.vorticity x t) :=
    hw.comp (continuous_id.prodMk continuous_const)
  have hw1 (t : Icc (0 : ℝ) T) : ContDiff ℝ 1 (fun x ↦ fields.vorticity x t) := by
    obtain ⟨W, _, hW⟩ := hball t
    apply (contDiff_and_bounds_of_h2_representative W (hwc t) _).1
    rw [hW]
    exact hrep t
  have hwx := (continuous_representative_and_deriv_of_hkBaseBall
    hbase hball hwc hrep).2
  obtain ⟨c, hc, hpair, hvel, hbound, _⟩ := exists_hkCurve_hilbert_coefficient hT F
  have hu (t : ℝ) (ht : t ∈ Ioo 0 T) :
      (fun x ↦ fields.velocity x t) = fun x ↦ hkCurveHilbertVelocity hT F x t := by
    let τ : Icc (0 : ℝ) T := ⟨t, Ioo_subset_Icc_self ht⟩
    have hs : HasCompactSupport (fun x ↦ fields.vorticity x t) :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hsupport t τ.property)
    obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs (hw1 τ) one_ne_zero
    rw [(hsol.biotSavart ht).eq_hilbertPVVelocity_of_normalized
      (fun _ ↦ hsol.regularity.velocity_differentiableAt ht) hK hs (hzero t ht)]
    rw [hilbertPVVelocity_eq_l2Primitive_of_ae (hw1 τ) hs (hrep τ)]
    simp only [hkCurveHilbertVelocity, projIcc_of_mem hT τ.property, τ]
  have htransport (x t : ℝ) (ht : t ∈ Ioo 0 T) :
      deriv (fields.vorticity x) t +
        hkCurveHilbertVelocity hT F x t * deriv (fun y ↦ fields.vorticity y t) x =
          c x t * fields.vorticity x t := by
    have hp := hsol.transport (x := x) ht
    change deriv (fields.vorticity x) t + 1 * fields.velocity x t *
      deriv (fun y ↦ fields.vorticity y t) x =
        deriv (fun y ↦ fields.velocity y t) x * fields.vorticity x t at hp
    rw [hu t ht, (hvel x t).deriv, congrFun (hu t ht) x, one_mul] at hp
    exact hp
  let w : ℝ × ℝ → ℝ := fun p ↦ fields.vorticity p.1 (projIcc 0 T hT p.2)
  let d : ℝ × ℝ → ℝ := fun p ↦
    deriv (fun x ↦ fields.vorticity x (projIcc 0 T hT p.2)) p.1
  have hw' : Continuous w := hw.comp (continuous_fst.prodMk
    ((continuous_projIcc (h := hT)).comp continuous_snd))
  have hd : Continuous d := hwx.comp (continuous_fst.prodMk
    ((continuous_projIcc (h := hT)).comp continuous_snd))
  have hclass : ContDiffOn ℝ 1 (Function.uncurry fields.vorticity)
      (univ ×ˢ Ioo (0 : ℝ) T) := by
    apply contDiffOn_one_of_partial_derivatives (isOpen_univ.prod isOpen_Ioo)
      (((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hd).continuousOn)
      (((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp
        ((hc.mul hw').sub ((continuous_hkCurveHilbertVelocity hT F).mul hd))).continuousOn)
    · intro p hp
      simpa only [Function.comp_apply, Function.uncurry_apply_pair, d,
        ContinuousLinearMap.toSpanSingletonLIE_apply,
        projIcc_of_mem hT (Ioo_subset_Icc_self hp.2)] using
        ((hw1 ⟨p.2, Ioo_subset_Icc_self hp.2⟩).differentiable one_ne_zero
          p.1).hasDerivAt.hasFDerivAt
    · intro p hp
      have ht := (hsol.regularity.vorticity_time_differentiableAt
        (x := p.1) hp.2).hasDerivAt
      rw [eq_sub_iff_add_eq.mpr (htransport p.1 p.2 hp.2)] at ht
      simpa only [Function.comp_apply, Function.uncurry_def, Pi.sub_apply,
        Pi.mul_apply, ContinuousLinearMap.toSpanSingletonLIE_apply,
        w, d, projIcc_of_mem hT (Ioo_subset_Icc_self hp.2)] using ht.hasFDerivAt
  obtain ⟨W₀, _, hW₀⟩ := hball ⟨0, le_rfl, hT⟩
  refine ⟨W₀, c, hc, hpair, hvel, hbound, hw, hclass, fun _ ↦ rfl,
    htransport, ?_, hrep, hW₀.symm⟩
  intro x t ht hx
  apply image_eq_zero_of_notMem_tsupport (f := fun x ↦ fields.vorticity x t)
  intro hs
  have hi := hsupport t ht hs
  exact hx.not_ge (abs_le.mpr hi)

end DeGregorio.Iteration
