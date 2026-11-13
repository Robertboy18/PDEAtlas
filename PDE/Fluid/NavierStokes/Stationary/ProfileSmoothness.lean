/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.HigherRegularity
public import PDE.Fluid.NavierStokes.Stationary.PressureIdentification
public import PDE.Fluid.NavierStokes.Stationary.FarFieldDecay
public import PDE.Fluid.NavierStokes.RieszPressure.Smooth
public import PDE.Fluid.NavierStokes.Nonuniqueness.ClassicalProfile
public import PDE.Spaces.Sobolev.Calculus.Product.WholeSpaceMultiplier
public import PDE.Spaces.Sobolev.Calculus.Product.Algebra
import PDE.Fluid.Incompressible.DistributionalDivergence

/-!
# Smoothness of weak stationary profiles

Let `W` be a smooth divergence-free background field on `ℝ³` with bounded derivatives, `W ∈ L⁴`,
and all derivatives of its stationary operator in `L²`, and let `w ∈ H¹(ℝ³)³` be divergence free
with `W + w` a weak solution of the self-similar profile equation. Then `w ∈ H^m(ℝ³)³` for every
`m` (`exists_wkpSpace_of_weak_profile`): `w ∈ H²` by `memH2_of_weakProfileDensity`, and if
`w ∈ H^{m+2}`, then `w` solves the self-similar Stokes system with data
`-F_W - (w·∇)W - (W·∇)w - div(w ⊗ w) ∈ H^{m+1}`, because `H^{m+2}(ℝ³)` is an algebra and the
derivatives of `W` are bounded, so `w ∈ H^{m+3}` by `exists_wkpSpace_of_weak_selfsimilarStokes`.

The Morrey embedding then gives a smooth field `U = W + w` with `U - W` and all its derivatives
square integrable and bounded. When also `DᵏW ∈ L²` for `k ≥ 1`, its Riesz pressure is smooth
(`contDiff_rieszPressure`), and the pressure identification `profile_pressure_eq_riesz_of_memLp`,
after integration by parts on both sides, gives the profile equation
`stationaryVelocityOperator U + ∇P = 0` at every point (`contDiff_of_weak_profile`).

Hou, Wang and Yang prove this smoothness (their Proposition 3) by an induction on energy
estimates for mollified near fields (Appendix F). Our induction goes instead through the
regularity of the linear self-similar Stokes system, one Sobolev order at a time.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 2.1, Proposition 3, p. 9,
  and Appendix F, proof of Proposition 3, pp. 67-68.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert RealInnerProductSpace

namespace NavierStokes.Stationary

/-- The base representative of a weak partial derivative of an `H¹(ℝⁿ)` function is its
first-derivative coordinate. -/
theorem baseRepresentative_partialDerivCLM_H1 {n : ℕ} (u : H¹(ℝ^n)) (j : Fin n) :
    baseRepresentative (partialDerivCLM j u) =
      (wkpCoordinateCLM (singleDerivIndex n j) u : ℝ^n → ℝ) := by
  rw [baseRepresentative_partialDerivCLM]
  rfl

/-- If every component of `w` lies in `H^{m+1}(ℝ³)`, the forcing `-F_W - (w·∇)W - (W·∇)w` of the
linearized equation has components in `H^m(ℝ³)`. -/
theorem exists_wkpSpace_profileForcing {W : ℝ^3 → ℝ^3} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hWbd : ∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k W x‖ ≤ C)
    (hF : ∀ k, MemLp (iteratedFDeriv ℝ k (stationaryVelocityOperator W)) 2 volume) {m : ℕ}
    (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (hreg : ∀ i, ∃ V : W^{m + 1,2}(ℝ^3),
      baseRepresentative V =ᵐ[volume] baseRepresentative (w i)) (i : Fin 3) :
    ∃ G : W^{m,2}(ℝ^3), baseRepresentative G =ᵐ[volume] profileForcing W w i := by
  choose V hV using hreg
  have hWj (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ W x j) := contDiff_component hW j
  have hWtop (j : Fin 3) (l : ℕ) : MemLp (iteratedFDeriv ℝ l (fun x ↦ W x j)) ⊤ volume := by
    obtain ⟨C, hC⟩ := hWbd l
    exact PDE.memLp_top_iteratedFDeriv_of_bound (hWj j) l fun x ↦
      (PDE.norm_iteratedFDeriv_component_le hW j l x).trans (hC x)
  set A : Fin 3 → W^{m + 2,⊤}(ℝ^3) := fun j ↦
    wkpOfContDiff (fun x ↦ W x j) (hWj j) fun l _ ↦ hWtop j l with hA_def
  have hSc : ContDiff ℝ (⊤ : ℕ∞) (stationaryVelocityOperator W) :=
    contDiff_stationaryVelocityOperator hW
  have hS : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ stationaryVelocityOperator W x i) :=
    contDiff_component hSc i
  have hSmem (l : ℕ) : MemLp (iteratedFDeriv ℝ l (fun x ↦ stationaryVelocityOperator W x i)) 2
      volume :=
    (hF l).of_le ((hS.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ PDE.norm_iteratedFDeriv_component_le hSc i l x)
  set F : W^{m,2}(ℝ^3) := wkpOfContDiff (fun x ↦ stationaryVelocityOperator W x i) hS
    fun l _ ↦ hSmem l with hF_def
  set P : Fin 3 → W^{m,2}(ℝ^3) := fun j ↦ lowerOrderCLM (Nat.le_succ m)
    (wkMultiplication (m + 1) (partialDerivCLM j (A i)) (V j)) with hP_def
  set Q : Fin 3 → W^{m,2}(ℝ^3) := fun j ↦
    wkMultiplication m (lowerOrderCLM (by omega : m ≤ m + 2) (A j)) (partialDerivCLM j (V i))
    with hQ_def
  refine ⟨-F - ∑ j, P j - ∑ j, Q j, ?_⟩
  have hFae : baseRepresentative F =ᵐ[volume] fun x ↦ stationaryVelocityOperator W x i :=
    baseRepresentative_wkpOfContDiff _ _ _
  have hPae (j : Fin 3) : baseRepresentative (P j) =ᵐ[volume]
      fun x ↦ baseRepresentative (w j) x * ∂[j] (fun y ↦ W y i) x := by
    have h1 := wkMultiplication_base_ae (m + 1) (partialDerivCLM j (A i)) (V j)
    have h2 := baseRepresentative_partialDerivCLM_wkpOfContDiff (p := ⊤) (k := m + 1) j
      (fun x ↦ W x i) (hWj i) fun l _ ↦ hWtop i l
    filter_upwards [h1, h2, hV j] with x hx1 hx2 hx3
    simp only [hP_def, baseRepresentative_lowerOrderCLM]
    rw [hx1, hx2, hx3, mul_comm]
  have hQae (j : Fin 3) : baseRepresentative (Q j) =ᵐ[volume]
      fun x ↦ W x j * (wkpCoordinateCLM (singleDerivIndex 3 j) (w i) : ℝ^3 → ℝ) x := by
    have h1 := wkMultiplication_base_ae m (lowerOrderCLM (by omega : m ≤ m + 2) (A j))
      (partialDerivCLM j (V i))
    have h2 := baseRepresentative_wkpOfContDiff (p := ⊤) (k := m + 2) (fun x ↦ W x j) (hWj j)
      fun l _ ↦ hWtop j l
    have h3 := baseRepresentative_partialDerivCLM_ae_eq (hV i) j
    rw [baseRepresentative_partialDerivCLM_H1] at h3
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    simp only [hQ_def]
    rw [hx1, baseRepresentative_lowerOrderCLM, hx2, hx3]
  have hsub1 := baseRepresentative_sub_ae (-F - ∑ j, P j) (∑ j, Q j)
  have hsub2 := baseRepresentative_sub_ae (-F) (∑ j, P j)
  have hneg := baseRepresentative_neg_ae F
  have hsP := baseRepresentative_sum_ae P
  have hsQ := baseRepresentative_sum_ae Q
  simp only [domainMeasure, Measure.restrict_univ] at hsub1 hsub2 hneg hsP hsQ
  filter_upwards [hsub1, hsub2, hneg, hsP, hsQ, hFae, ae_all_iff.2 hPae, ae_all_iff.2 hQae]
    with x h1 h2 h3 h4 h5 h6 h7 h8
  rw [h1, h2, h3, h4, h5, h6]
  simp only [h7, h8, profileForcing]
  rfl

/-- **All-order Sobolev regularity of weak stationary profiles.** Let `W` be a smooth
divergence-free field on `ℝ³` with bounded derivatives of every order and all derivatives of its
stationary operator in `L²`, and let `w ∈ H¹(ℝ³)³` be divergence free with `W + w` a weak
solution of the self-similar profile equation. Then every component of `w` lies in `H^m(ℝ³)` for
every `m`. -/
theorem exists_wkpSpace_of_weak_profile {W : ℝ^3 → ℝ^3} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hWbd : ∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k W x‖ ≤ C)
    (hWdiv : ∀ x, PDE.divergence W x = 0)
    (hF : ∀ k, MemLp (iteratedFDeriv ℝ k (stationaryVelocityOperator W)) 2 volume)
    {w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))} (hw : divergenceCLM w = 0)
    (hweak : Nonuniqueness.WeakProfileEquation (W + representative w)) (m : ℕ) (i : Fin 3) :
    ∃ V : W^{m,2}(ℝ^3), baseRepresentative V =ᵐ[volume] baseRepresentative (w i) := by
  have hcoord := fun (φ : ℝ^3 → ℝ^3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
      (hdiv : ∀ x, PDE.divergence φ x = 0) ↦
    integral_coordinates_eq_zero_of_weakProfileEquation (W := W) w hweak hφ hc hdiv
  suffices h : ∀ m i, ∃ V : W^{m + 2,2}(ℝ^3),
      baseRepresentative V =ᵐ[volume] baseRepresentative (w i) by
    obtain ⟨V, hV⟩ := h m i
    exact ⟨lowerOrderCLM (by omega : m ≤ m + 2) V,
      by rw [baseRepresentative_lowerOrderCLM]; exact hV⟩
  intro m
  induction m with
  | zero =>
    intro i
    obtain ⟨V, hV⟩ := memH2_of_weakProfileDensity W hW hWbd hWdiv hF w hw hcoord i
    exact ⟨V, Filter.EventuallyEq.of_eq (by rw [← hV, baseRepresentative_lowerOrderCLM])⟩
  | succ m ih =>
    choose V hV using ih
    have hk : ((3 : ℕ) : ℝ) < 2 * ((m + 2 : ℕ) : ℝ) := by
      push_cast
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    choose G hG using exists_wkpSpace_profileForcing hW hWbd hF (m := m + 1) w
      fun i ↦ ⟨V i, hV i⟩
    set R : Fin 3 → Fin 3 → W^{m + 1,2}(ℝ^3) := fun j i ↦
      partialDerivCLM j (multiplication hk (V j) (V i)) with hR_def
    set g : Fin 3 → W^{m + 1,2}(ℝ^3) := fun i ↦ G i - ∑ j, R j i with hg_def
    refine exists_wkpSpace_of_weak_selfsimilarStokes (m + 1) w hw g fun φ hφ hc hdiv ↦ ?_
    have hφi (i : Fin 3) : ContDiff ℝ ∞ (fun y ↦ φ y i) := contDiff_component hφ i
    have hφic (i : Fin 3) : HasCompactSupport (fun y ↦ φ y i) := hasCompactSupport_component hc i
    have hE := sum_integral_eq_profileForcing_of_weakProfileDensity W hW hWdiv (hF 0) w hw hcoord
      hφ hc hdiv
    -- the convection in divergence form
    have hconv (i j : Fin 3) : ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
        (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x * PDE.partialDeriv j (fun y ↦ φ y i) x =
        -∫ x, baseRepresentative (R j i) x * φ x i := by
      rw [← integral_baseRepresentative_mul_partialDeriv (multiplication hk (V j) (V i)) j
        (hφi i) (hφic i)]
      refine integral_congr_ae ?_
      filter_upwards [multiplication_ae hk (V j) (V i), hV j, hV i] with x h1 h2 h3
      rw [h1, h2, h3]
      rfl
    -- the data
    have hdata (i : Fin 3) : ∫ x, baseRepresentative (g i) x * φ x i =
        (∫ x, profileForcing W w i x * φ x i) - ∑ j, ∫ x, baseRepresentative (R j i) x * φ x i := by
      have hsub := baseRepresentative_sub_ae (G i) (∑ j, R j i)
      have hsum := baseRepresentative_sum_ae (fun j ↦ R j i)
      simp only [domainMeasure, Measure.restrict_univ] at hsub hsum
      have hint (j : Fin 3) := integrable_baseRepresentative_mul (R j i) (hφi i).continuous
        (hφic i)
      have hGi : ∫ x, profileForcing W w i x * φ x i = ∫ x, baseRepresentative (G i) x * φ x i :=
        integral_congr_ae (by filter_upwards [hG i] with x hx; rw [hx])
      rw [hGi, ← integral_finsetSum _ fun j _ ↦ hint j, ← integral_sub
        (integrable_baseRepresentative_mul (G i) (hφi i).continuous (hφic i))
        (integrable_finsetSum _ fun j _ ↦ hint j)]
      refine integral_congr_ae ?_
      filter_upwards [hsub, hsum] with x h1 h2
      simp only [hg_def]
      rw [h1, h2, sub_mul, Finset.sum_mul]
    refine hE.trans ?_
    simp only [hconv, hdata, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring

/-- A field in `H¹(ℝ³)³` whose components lie in every `H^m(ℝ³)` has a smooth member `R` of its
class, with all derivatives square integrable and bounded, and `R ∈ L⁴`. -/
theorem exists_contDiff_ae_eq_representative (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (hreg : ∀ m i, ∃ V : W^{m,2}(ℝ^3),
      baseRepresentative V =ᵐ[volume] baseRepresentative (w i)) :
    ∃ R : ℝ^3 → ℝ^3, ContDiff ℝ (⊤ : ℕ∞) R ∧ R =ᵐ[volume] representative w ∧
      (∀ k, MemLp (iteratedFDeriv ℝ k R) 2 volume) ∧
      (∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k R x‖ ≤ C) ∧ MemLp R 4 volume := by
  have : Fact (0 < 3) := ⟨by norm_num⟩
  set f : Fin 3 → ℝ^3 → ℝ := fun i ↦ continuousRepresentative volume (baseRepresentative (w i))
    with hf_def
  have hf (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (f i) :=
    contDiff_continuousRepresentative_of_forall_wkpSpace fun m ↦ hreg m i
  have hfae (i : Fin 3) : f i =ᵐ[volume] baseRepresentative (w i) :=
    continuousRepresentative_ae_eq _ _
  set R : ℝ^3 → ℝ^3 := fun x ↦ WithLp.toLp 2 fun i ↦ f i x with hR_def
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := contDiff_euclidean.2 hf
  have hRk (k : ℕ) : ContDiff ℝ k R := hR.of_le (by exact_mod_cast le_top)
  have hR4 : MemLp (iteratedFDeriv ℝ 0 R) 4 volume := by
    refine PDE.memLp_iteratedFDeriv_of_component (hRk 0) fun i ↦ ?_
    obtain ⟨V, hV⟩ := hreg 3 i
    have h4 : MemLp (f i) 4 volume := by
      have h := memLp_four_baseRepresentative_three V
      simp only [domainMeasure, Measure.restrict_univ] at h
      exact h.ae_eq ((hfae i).trans hV.symm).symm
    exact h4.of_le (((hf i).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ by rw [norm_iteratedFDeriv_zero])
  refine ⟨R, hR, ?_, fun k ↦ ?_, fun k ↦ ?_, ?_⟩
  · filter_upwards [ae_all_iff.2 hfae] with x hx
    ext i
    simp only [hR_def, PiLp.toLp_apply, representative_apply, massCLM_apply]
    exact hx i
  · exact PDE.memLp_iteratedFDeriv_of_component (hRk k) fun i ↦
      memLp_iteratedFDeriv_continuousRepresentative_of_forall_wkpSpace (fun m ↦ hreg m i) k
  · refine PDE.exists_bound_iteratedFDeriv_of_component (hRk k) fun i ↦ ?_
    obtain ⟨V, hV⟩ := hreg (k + 3) i
    exact exists_bound_iteratedFDeriv_of_ae_eq_baseRepresentative V (hf i) ((hfae i).trans hV.symm)
  · exact hR4.of_le hR.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [norm_iteratedFDeriv_zero])

/-- A `C¹` member of the class of a divergence-free field in `H¹(ℝ³)³` is divergence free at every
point. -/
theorem divergence_eq_zero_of_ae_eq_representative {R : ℝ^3 → ℝ^3} (hR : ContDiff ℝ 1 R)
    {w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))} (hw : divergenceCLM w = 0)
    (hRw : R =ᵐ[volume] representative w) (x : ℝ^3) : PDE.divergence R x = 0 :=
  ((distributionallyDivergenceFree_representative hw).congr_ae
    hRw.symm).divergence_eq_zero_of_contDiffOn isOpen_univ hR.contDiffOn (mem_univ x)

/-- A smooth divergence-free field `U` and a smooth pressure `P` that satisfy the weak profile
equation with pressure, `∫ weakProfileDensity U φ = ∫ P div φ` for every smooth compactly
supported `φ`, satisfy `stationaryVelocityOperator U + ∇P = 0` at every point. -/
theorem stationaryVelocityOperator_add_gradient_eq_zero {U : ℝ^3 → ℝ^3} {P : ℝ^3 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U) (hdiv : ∀ x, PDE.divergence U x = 0)
    (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (h : ∀ φ : ℝ^3 → ℝ^3, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, Nonuniqueness.weakProfileDensity U φ x = ∫ x, P x * PDE.divergence φ x)
    (x : ℝ^3) : stationaryVelocityOperator U x + gradient P x = 0 := by
  have hSc : Continuous (stationaryVelocityOperator U) :=
    (contDiff_stationaryVelocityOperator hU).continuous
  have hUi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ U y i) := contDiff_component hU i
  have hcomp (i : Fin 3) : ∀ y, stationaryVelocityOperator U y i + ∂[i] P y = 0 := by
    set g : ℝ^3 → ℝ := fun y ↦ stationaryVelocityOperator U y i + ∂[i] P y with hg_def
    have hgc : Continuous g := ((EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).continuous.comp hSc).add
      ((hP.of_le (by simp)).continuous_partialDeriv i)
    have hint (χ : ℝ^3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
        ∫ y, χ y • g y = 0 := by
      set φ : ℝ^3 → ℝ^3 := fun y ↦ χ y • EuclideanSpace.single i (1 : ℝ) with hφ_def
      have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hχ.smul contDiff_const
      have hφc : HasCompactSupport φ := hc.smul_right
      have hdivφ (y : ℝ^3) : PDE.divergence φ y = ∂[i] χ y := by
        rw [PDE.divergence_eq_sum]
        have hj (j : Fin 3) : ∂[j] (fun z ↦ φ z j) y =
            (EuclideanSpace.single i (1 : ℝ) : ℝ^3) j * ∂[j] χ y := by
          have : (fun z ↦ φ z j) = fun z ↦ (EuclideanSpace.single i (1 : ℝ) : ℝ^3) j • χ z := by
            funext z
            simp [hφ_def, mul_comm]
          rw [this, PDE.partialDeriv_const_smul, smul_eq_mul]
        rw [Finset.sum_congr rfl fun j _ ↦ hj j]
        simp
      have hU2 : ∀ y : ℝ^3, y ≠ 0 → ContDiffAt ℝ 2 U y := fun y _ ↦
        (hU.of_le (by simp)).contDiffAt
      have hD (k j : Fin 3) : LocallyIntegrable (PDE.partialDeriv j (fun y ↦ U y k)) volume :=
        (((hUi k).of_le (by simp)).continuous_partialDeriv j).locallyIntegrable
      have hH (k j : Fin 3) : LocallyIntegrable
          (PDE.partialDeriv j (PDE.partialDeriv j (fun y ↦ U y k))) volume :=
        (((PDE.contDiff_top_partialDeriv (hUi k)).of_le (by simp)).continuous_partialDeriv
          j).locallyIntegrable
      have h1 :=
        Nonuniqueness.integral_weakProfileDensity_eq_integral_inner_stationaryVelocityOperator
          hU.continuous hU2 (fun y _ ↦ hdiv y) hD hH hφ hφc
      have hinner (y : ℝ^3) : ⟪stationaryVelocityOperator U y, φ y⟫ =
          χ y * stationaryVelocityOperator U y i := by
        simp [hφ_def, inner_smul_right, EuclideanSpace.inner_single_right]
      have h2 : ∫ y, P y * PDE.divergence φ y = -∫ y, χ y * ∂[i] P y := by
        rw [integral_mul_partialDeriv_eq_neg i (hχ.of_le (by simp)) (hP.of_le (by simp)) hc,
          neg_neg]
        exact integral_congr_ae (Eventually.of_forall fun y ↦ by
          simp only [hdivφ, mul_comm])
      have heq := h φ hφ hφc
      rw [h1, h2] at heq
      simp only [hinner] at heq
      have hi1 : Integrable (fun y ↦ χ y * stationaryVelocityOperator U y i) volume :=
        (hχ.continuous.mul ((EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).continuous.comp
          hSc)).integrable_of_hasCompactSupport hc.mul_right
      have hi2 : Integrable (fun y ↦ χ y * ∂[i] P y) volume :=
        (hχ.continuous.mul ((hP.of_le (by simp)).continuous_partialDeriv
          i)).integrable_of_hasCompactSupport
          hc.mul_right
      simp only [hg_def, smul_eq_mul, mul_add]
      rw [integral_add hi1 hi2, heq]
      ring
    have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hgc.locallyIntegrable hint
    have hzero : g = fun _ ↦ 0 :=
      (Continuous.ae_eq_iff_eq volume hgc continuous_const).mp (hae.mono fun y hy ↦ hy)
    exact fun y ↦ congrFun hzero y
  ext i
  simp only [PiLp.add_apply, PDE.gradient_apply_eq_partialDeriv, PiLp.zero_apply]
  exact hcomp i x

/-- **Smoothness of weak stationary profiles** (the regularity of Hou, Wang and Yang, Appendix F).
Let `W` be a smooth divergence-free field on `ℝ³` with bounded derivatives of every order,
`W ∈ L⁴`, `DᵏW ∈ L²` for `k ≥ 1`, and all derivatives of its stationary operator in `L²`. If
`w ∈ H¹(ℝ³)³` is divergence free and `W + w` is a weak solution of the self-similar profile
equation, then `W + w` has a smooth member `U` with every derivative of `U - W` square
integrable, the Riesz pressure of `U` is smooth, and `stationaryVelocityOperator U + ∇P = 0` at
every point, `P = rieszPressure U`. Smoothness is `C^∞`, written `ContDiff ℝ (⊤ : ℕ∞)`. -/
theorem contDiff_of_weak_profile (W : ℝ^3 → ℝ^3) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hWbd : ∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k W x‖ ≤ C)
    (hW4 : MemLp W 4 volume)
    (hDk : ∀ k, 1 ≤ k → MemLp (iteratedFDeriv ℝ k W) 2 volume)
    (hWdiv : ∀ x, PDE.divergence W x = 0)
    (hF : ∀ k, MemLp (iteratedFDeriv ℝ k (stationaryVelocityOperator W)) 2 volume)
    (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (hw : divergenceCLM w = 0)
    (hweak : Nonuniqueness.WeakProfileEquation (W + representative w)) :
    ∃ U : ℝ^3 → ℝ^3, ContDiff ℝ (⊤ : ℕ∞) U ∧ U =ᵐ[volume] W + representative w ∧
      (∀ k, MemLp (iteratedFDeriv ℝ k (U - W)) 2 volume) ∧
      ContDiff ℝ (⊤ : ℕ∞) (rieszPressure U) ∧
      ∀ x, stationaryVelocityOperator U x + gradient (rieszPressure U) x = 0 := by
  obtain ⟨R, hR, hRw, hR2, hRbd, hR4⟩ := exists_contDiff_ae_eq_representative w
    (exists_wkpSpace_of_weak_profile hW hWbd hWdiv hF hw hweak)
  have hU : ContDiff ℝ (⊤ : ℕ∞) (W + R) := hW.add hR
  have hUw : W + R =ᵐ[volume] W + representative w := hRw.mono fun x hx ↦ by
    simp only [Pi.add_apply, hx]
  have hUW : W + R - W = R := add_sub_cancel_left W R
  have hdiv (x : ℝ^3) : PDE.divergence (W + R) x = 0 := by
    rw [show W + R = fun y ↦ W y + R y from rfl, PDE.divergence_add_of_differentiableAt
      (hW.differentiable (by simp) x) (hR.differentiable (by simp) x), hWdiv,
      divergence_eq_zero_of_ae_eq_representative (hR.of_le (by simp)) hw hRw, add_zero]
  have hUbd (k : ℕ) : ∃ C, ∀ x, ‖iteratedFDeriv ℝ k (W + R) x‖ ≤ C := by
    obtain ⟨C₁, h₁⟩ := hWbd k
    obtain ⟨C₂, h₂⟩ := hRbd k
    refine ⟨C₁ + C₂, fun x ↦ ?_⟩
    rw [iteratedFDeriv_add_apply (hW.of_le (m := k) (by exact_mod_cast le_top)).contDiffAt
      (hR.of_le (m := k) (by exact_mod_cast le_top)).contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (h₁ x) (h₂ x))
  have hUd2 (k : ℕ) (hk : 1 ≤ k) : MemLp (iteratedFDeriv ℝ k (W + R)) 2 volume := by
    rw [iteratedFDeriv_add (hW.of_le (m := k) (by exact_mod_cast le_top))
      (hR.of_le (m := k) (by exact_mod_cast le_top))]
    exact (hDk k hk).add (hR2 k)
  have : Fact (0 < 3) := ⟨by norm_num⟩
  have hP := (contDiff_rieszPressure hU (hW4.add hR4) hUbd hUd2).1
  refine ⟨W + R, hU, hUw, by rw [hUW]; exact hR2, hP, ?_⟩
  have hFW : MemLp (stationaryVelocityOperator W) 2 volume :=
    (hF 0).of_le (contDiff_stationaryVelocityOperator hW).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [norm_iteratedFDeriv_zero])
  obtain ⟨C₀, hC₀⟩ := hWbd 0
  refine stationaryVelocityOperator_add_gradient_eq_zero hU hdiv hP fun φ hφ hc ↦ ?_
  have hid := (profile_pressure_eq_riesz_of_memLp hW hWdiv (C₀ := C₀)
    (fun x ↦ by simpa [norm_iteratedFDeriv_zero] using hC₀ x) hW4 hFW hw hweak hφ hc).2.2
  rw [rieszPressure_congr_ae hUw, ← hid]
  exact integral_congr_ae (Nonuniqueness.weakProfileDensity_congr_ae hUw φ)

end NavierStokes.Stationary
