/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.EndpointDerivatives
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.Restart
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.Splice

/-!
# Classical continuation across a coupled H² trace

Two coupled slabs with the same endpoint L² trace concatenate to a classical
solution, including at the joining time. The spatial derivative and transport
right-hand side are continuous there; their partial derivatives give joint C¹
regularity. Applying local existence to the terminal H² graph then constructs
an extension whose velocity is the principal-value velocity of its own vorticity.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Common DeGregorio
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

variable {B D : NNReal} {T S R Q : ℝ} {hT : 0 ≤ T} {hS : 0 ≤ S}
  {F : C(Icc (0 : ℝ) T,
    supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
  {G : C(Icc (0 : ℝ) S,
    supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-Q) Q) D)}
  {W₀ V₀ : W^{2,2}((Set.univ : Set (ℝ^1)))} {w₀ z₀ : ℝ → ℝ}
  {c w d z : ℝ → ℝ → ℝ}

/-- Matching coupled L² endpoint traces give a classical solution on the
union, with an ordinary spacetime derivative at the joining time. -/
theorem IsHkFrozenOutput.isClassicalSolutionOn_join
    (hF : IsHkFrozenOutput hT F F W₀ w₀ c w)
    (hG : IsHkFrozenOutput hS G G V₀ z₀ d z)
    (hTpos : 0 < T) (hSpos : 0 < S)
    (hbase : (F ⟨T, hT, le_rfl⟩).val = (G ⟨0, le_rfl, hS⟩).val) :
    IsClassicalSolutionOn 1
      ⟨joinTimeSlabs hT hS w z,
        joinTimeSlabs hT hS (hkCurveHilbertVelocity hT F) (hkCurveHilbertVelocity hS G)⟩
      (Ioo 0 (T + S)) := by
  obtain ⟨hw, hderiv, hc, hu⟩ :=
    hF.spatial_fields_eq_of_base_eq hG ⟨T, hT, le_rfl⟩ ⟨0, le_rfl, hS⟩ hbase
  let J := joinTimeSlabs hT hS w z
  let U := joinTimeSlabs hT hS (hkCurveHilbertVelocity hT F) (hkCurveHilbertVelocity hS G)
  let C := joinTimeSlabs hT hS c d
  let A := joinTimeSlabs hT hS
    (fun x t ↦ deriv (fun y ↦ w y t) x) (fun x t ↦ deriv (fun y ↦ z y t) x)
  let q (x t : ℝ) :=
    c x t * w x t - hkCurveHilbertVelocity hT F x t * deriv (fun y ↦ w y t) x
  let r (x t : ℝ) :=
    d x t * z x t - hkCurveHilbertVelocity hS G x t * deriv (fun y ↦ z y t) x
  let K := joinTimeSlabs hT hS q r
  have hmatch (x : ℝ) : w x T = z x 0 := congrFun hw x
  have hqmatch (x : ℝ) : q x T = r x 0 := by
    dsimp only [q, r]
    rw [congrFun hc x, congrFun hw x, congrFun hu x, congrFun hderiv x]
  have hA : Continuous (Function.uncurry A) :=
    continuous_joinTimeSlabs hT hS hF.continuous_spatial_deriv hG.continuous_spatial_deriv
      (fun x ↦ congrFun hderiv x)
  have hK : Continuous (Function.uncurry K) :=
    continuous_joinTimeSlabs hT hS hF.continuous_transport_rhs hG.continuous_transport_rhs
      hqmatch
  have hspace (x t : ℝ) : HasDerivAt (fun y ↦ J y t) (A x t) x := by
    by_cases ht : t ≤ T
    · simpa only [J, A, joinTimeSlabs, ite_eq_left ht] using
        ((hF.contDiff_vorticity_on_Icc (projIcc 0 T hT t).property).differentiable
          (by simp) x).hasDerivAt
    · simpa only [J, A, joinTimeSlabs, ite_eq_right ht] using
        ((hG.contDiff_vorticity_on_Icc (projIcc 0 S hS (t - T)).property).differentiable
          (by simp) x).hasDerivAt
  have htime (x t : ℝ) (ht : t ∈ Ioo 0 (T + S)) : HasDerivAt (J x) (K x t) t := by
    rcases lt_trichotomy t T with hlt | heq | hgt
    · have hi : t ∈ Ioo 0 T := ⟨ht.1, hlt⟩
      have hd := (hF.isClassicalSolutionOn.regularity.vorticity_time_differentiableAt
        (x := x) hi).hasDerivAt
      rw [eq_sub_iff_add_eq.mpr (hF.transport x t hi)] at hd
      rw [show K x t = q x t from
        joinTimeSlabs_eq_left hT hS q r x (Ioo_subset_Icc_self hi)]
      exact hd.congr_of_eventuallyEq (joinTimeSlabs_eventuallyEq_left hT hS w z x hi)
    · subst t
      rw [show K x T = q x T from joinTimeSlabs_eq_left hT hS q r x ⟨hT, le_rfl⟩]
      apply hasDerivAt_joinTimeSlabs_join hTpos hSpos hmatch x (q x T)
        (hF.hasDerivWithinAt_time_terminal hTpos x)
      rw [hqmatch]
      exact hG.hasDerivWithinAt_time_initial hSpos x
    · have hi : t - T ∈ Ioo 0 S := ⟨sub_pos.mpr hgt, sub_lt_iff_lt_add.mpr
        (by simpa only [add_comm S T] using ht.2)⟩
      have hd := (hG.isClassicalSolutionOn.regularity.vorticity_time_differentiableAt
        (x := x) hi).hasDerivAt
      rw [eq_sub_iff_add_eq.mpr (hG.transport x (t - T) hi)] at hd
      rw [show K x t = r x (t - T) from
        joinTimeSlabs_eq_right hT hS hqmatch x ⟨hgt.le, ht.2.le⟩]
      exact (hd.comp_sub_const t T).congr_of_eventuallyEq
        (joinTimeSlabs_eventuallyEq_right hT hS hmatch x ⟨hgt, ht.2⟩)
  have hregular : ContDiffOn ℝ 1 (Function.uncurry J) (univ ×ˢ Ioo 0 (T + S)) :=
    contDiffOn_one_of_partial_derivatives (isOpen_univ.prod isOpen_Ioo)
      (((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hA).continuousOn)
      (((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hK).continuousOn)
      (fun p _ ↦ (hspace p.1 p.2).hasFDerivAt) fun p hp ↦ (htime p.1 p.2 hp.2).hasFDerivAt
  have hvelocity (x t : ℝ) : HasDerivAt (fun y ↦ U y t) (C x t) x := by
    by_cases ht : t ≤ T
    · simpa only [U, C, joinTimeSlabs, ite_eq_left ht] using
        hF.velocity_derivative x (projIcc 0 T hT t)
    · simpa only [U, C, joinTimeSlabs, ite_eq_right ht] using
        hG.velocity_derivative x (projIcc 0 S hS (t - T))
  have hpair (t : ℝ) : IsHilbertPair (fun x ↦ J x t) (fun x ↦ C x t) := by
    by_cases ht : t ≤ T
    · simpa only [J, C, joinTimeSlabs, ite_eq_left ht] using
        hF.hilbert_pair_self_on_Icc (projIcc 0 T hT t).property
    · simpa only [J, C, joinTimeSlabs, ite_eq_right ht] using
        hG.hilbert_pair_self_on_Icc (projIcc 0 S hS (t - T)).property
  have hKformula (x t : ℝ) : K x t = C x t * J x t - U x t * A x t := by
    by_cases ht : t ≤ T <;> simp only [K, C, J, U, A, joinTimeSlabs, ht, ↓reduceIte, q, r]
  refine ⟨⟨fun {x t} ht ↦ (hregular.contDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ x, ht⟩)).differentiableAt (by simp),
    fun {x t} _ ↦ (hvelocity x t).differentiableAt⟩, fun x t ht ↦ ?_,
    fun t _ ↦ (hpair t).congr_ae EventuallyEq.rfl (.of_forall fun x ↦ (hvelocity x t).deriv.symm)⟩
  change deriv (J x) t + 1 * U x t * deriv (fun y ↦ J y t) x = deriv (fun y ↦ U y t) x * J x t
  rw [(htime x t ht).deriv, (hspace x t).deriv, (hvelocity x t).deriv, one_mul, hKformula,
    sub_add_cancel]

/-- Every positive closed coupled slab extends beyond its terminal time.
The extension agrees with the entire original closed slab, uses its own
principal-value velocity, and retains compact support and a uniform H² bound. -/
theorem IsHkFrozenOutput.exists_classical_extension
    (hF : IsHkFrozenOutput hT F F W₀ w₀ c w) (hTpos : 0 < T) (hR : 0 ≤ R) :
    ∃ T' > T, ∃ (B' : NNReal) (v : ℝ → ℝ → ℝ),
      Continuous (Function.uncurry v) ∧
      (∀ x t, t ∈ Icc 0 T → v x t = w x t) ∧
      IsClassicalSolutionOn 1
        ⟨v, fun x t ↦ hilbertPVVelocity (fun y ↦ v y t) x⟩ (Ioo 0 T') ∧
      ∀ t : ℝ,
        tsupport (fun x ↦ v x t) ⊆
          Icc (-(max R (R * Real.exp 2))) (max R (R * Real.exp 2)) ∧
        ∃ V : W^{2,2}((Set.univ : Set (ℝ^1))), ‖V‖ ≤ B' ∧
          (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM V) : ℝ → ℝ)
            =ᵐ[volume] fun x ↦ v x t := by
  obtain ⟨V₀, S, hSpos, D, G, d, z, _, hVbase, hG, _, hmatch, _⟩ :=
    hF.exists_restart hR ⟨T, hT, le_rfl⟩
  let v := joinTimeSlabs hT hSpos.le w z
  let u := joinTimeSlabs hT hSpos.le
    (hkCurveHilbertVelocity hT F) (hkCurveHilbertVelocity hSpos.le G)
  have hbase : (F ⟨T, hT, le_rfl⟩).val = (G ⟨0, le_rfl, hSpos.le⟩).val :=
    hVbase.symm.trans hG.initial_base.symm
  have hsol := hF.isClassicalSolutionOn_join hG hTpos hSpos hbase
  have hu : u = fun x t ↦ hilbertPVVelocity (fun y ↦ v y t) x := by
    funext x t
    by_cases ht : t ≤ T
    · simpa only [u, v, joinTimeSlabs, ite_eq_left ht] using
        congrFun (hF.velocity_eq_hilbertPVVelocity_on_Icc (projIcc 0 T hT t).property) x
    · simpa only [u, v, joinTimeSlabs, ite_eq_right ht] using
        congrFun (hG.velocity_eq_hilbertPVVelocity_on_Icc
          (projIcc 0 S hSpos.le (t - T)).property) x
  change IsClassicalSolutionOn 1 ⟨v, u⟩ (Ioo 0 (T + S)) at hsol
  rw [hu] at hsol
  refine ⟨T + S, lt_add_of_pos_right T hSpos, max B D, v,
    continuous_joinTimeSlabs hT hSpos.le hF.continuous hG.continuous
      (fun x ↦ congrFun hmatch.1 x),
    fun x t ht ↦ joinTimeSlabs_eq_left hT hSpos.le w z x ht, hsol, ?_⟩
  intro t
  by_cases ht : t ≤ T
  · rw [show (fun x ↦ v x t) = fun x ↦ w x (projIcc 0 T hT t) by
      simp only [v, joinTimeSlabs, ite_eq_left ht]]
    obtain ⟨V, hV, hbase⟩ := (F (projIcc 0 T hT t)).property.1
    exact ⟨(hF.tsupport_on_Icc (projIcc 0 T hT t).property).trans
      (Icc_subset_Icc (neg_le_neg (le_max_left _ _)) (le_max_left _ _)), V,
      hV.trans (show (B : ℝ) ≤ (max B D : NNReal) from le_max_left _ _),
      hbase ▸ hF.representative (projIcc 0 T hT t)⟩
  · rw [show (fun x ↦ v x t) = fun x ↦ z x (projIcc 0 S hSpos.le (t - T)) by
      simp only [v, joinTimeSlabs, ite_eq_right ht]]
    obtain ⟨V, hV, hbase⟩ := (G (projIcc 0 S hSpos.le (t - T))).property.1
    exact ⟨(hG.tsupport_on_Icc (projIcc 0 S hSpos.le (t - T)).property).trans
      (Icc_subset_Icc (neg_le_neg (le_max_right _ _)) (le_max_right _ _)), V,
      hV.trans (show (D : ℝ) ≤ (max B D : NNReal) from le_max_right _ _),
      hbase ▸ hG.representative (projIcc 0 S hSpos.le (t - T))⟩

end DeGregorio.Iteration
