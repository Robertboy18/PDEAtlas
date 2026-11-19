/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.DilationDrift
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.ThreeDimensionalProduct
public import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Uniqueness of weak solutions of the shifted linearized profile equation

Let `w` be a divergence-free field in `H¹(ℝ³)³` and `μ ≥ 0`. A divergence-free `d ∈ H¹(ℝ³)³`
satisfying `(μ + L₀) d + Π((w·∇) d) = 0` against all smooth compactly supported
divergence-free test fields vanishes. Here `L₀ = -1/2 - (1/2) x·∇ - Δ` and the equation is
tested in the form `∫ d · ((μ + 1) φ + (1/2) x·∇φ - Δφ) = ∫ wⱼ dᵢ ∂ⱼφᵢ`.

The weak equation identifies `⟨d, x·∇φ⟩` with a continuous linear functional of `φ` in `H¹`,
because products of `H¹(ℝ³)` functions lie in `L²`. The dilation identity then gives the
energy inequality `(2μ + 1/2) ‖d‖² + 2 ‖∇d‖² ≤ 0`, once the convection energy `∫ wⱼ dᵢ ∂ⱼdᵢ`
is shown to vanish by density of smooth compactly supported functions. No smallness of `w`
and no weight on `d` enter.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Stationary

theorem memLp_mul_H1 (W U : H¹(ℝ^3)) :
    MemLp (fun x ↦ baseRepresentative W x * baseRepresentative U x) 2 volume := by
  obtain ⟨C, _, hC⟩ := SobolevSpace.Inequalities.exists_eLpNorm_mul_le_H1
  exact lt_of_le_of_lt (hC W U) ENNReal.ofReal_lt_top

/-- Multiplication by a fixed three-dimensional `H¹` function, from `H¹` into `L²`. -/
def mulH1 (W : H¹(ℝ^3)) : H¹(ℝ^3) →L[ℝ] DerivLp 3 2 univ :=
  LinearMap.mkContinuous
    { toFun := fun U ↦ (show MemLp (fun x ↦ baseRepresentative W x * baseRepresentative U x) 2
          (domainMeasure 3 univ) by simpa [domainMeasure] using memLp_mul_H1 W U).toLp _
      map_add' := fun U V ↦ by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (μ := domainMeasure 3 univ)
            (f := fun x ↦ baseRepresentative W x * baseRepresentative (U + V) x)
            (by simpa [domainMeasure] using memLp_mul_H1 W (U + V)),
          MemLp.coeFn_toLp (μ := domainMeasure 3 univ)
            (f := fun x ↦ baseRepresentative W x * baseRepresentative U x)
            (by simpa [domainMeasure] using memLp_mul_H1 W U),
          MemLp.coeFn_toLp (μ := domainMeasure 3 univ)
            (f := fun x ↦ baseRepresentative W x * baseRepresentative V x)
            (by simpa [domainMeasure] using memLp_mul_H1 W V),
          Lp.coeFn_add (μ := domainMeasure 3 univ)
            ((show MemLp (fun x ↦ baseRepresentative W x * baseRepresentative U x) 2
              (domainMeasure 3 univ) by simpa [domainMeasure] using memLp_mul_H1 W U).toLp _)
            ((show MemLp (fun x ↦ baseRepresentative W x * baseRepresentative V x) 2
              (domainMeasure 3 univ) by simpa [domainMeasure] using memLp_mul_H1 W V).toLp _),
          baseRepresentative_add_ae U V] with x h1 h2 h3 h4 h5
        simp only [Pi.add_apply] at h4
        rw [h1, h4, h2, h3, h5]
        ring
      map_smul' := fun c U ↦ by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (μ := domainMeasure 3 univ)
            (f := fun x ↦ baseRepresentative W x * baseRepresentative (c • U) x)
            (by simpa [domainMeasure] using memLp_mul_H1 W (c • U)),
          MemLp.coeFn_toLp (μ := domainMeasure 3 univ)
            (f := fun x ↦ baseRepresentative W x * baseRepresentative U x)
            (by simpa [domainMeasure] using memLp_mul_H1 W U),
          Lp.coeFn_smul (μ := domainMeasure 3 univ) c
            ((show MemLp (fun x ↦ baseRepresentative W x * baseRepresentative U x) 2
              (domainMeasure 3 univ) by simpa [domainMeasure] using memLp_mul_H1 W U).toLp _),
          baseRepresentative_smul_ae c U] with x h1 h2 h3 h4
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at h3 h4 ⊢
        rw [h1, h3, h2, h4]
        ring }
    (SobolevSpace.Inequalities.exists_eLpNorm_mul_le_H1.choose * ‖W‖) (fun U ↦ by
      have hC := SobolevSpace.Inequalities.exists_eLpNorm_mul_le_H1.choose_spec
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp]
      have hb := hC.2 W U
      have hb' : eLpNorm (fun x ↦ baseRepresentative W x * baseRepresentative U x) 2
          (domainMeasure 3 univ) ≤ ENNReal.ofReal
            (SobolevSpace.Inequalities.exists_eLpNorm_mul_le_H1.choose * ‖W‖ * ‖U‖) := by
        simpa [domainMeasure] using hb
      exact ENNReal.toReal_le_of_le_ofReal (by positivity [hC.1]) hb')

theorem mulH1_ae (W U : H¹(ℝ^3)) :
    (mulH1 W U : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ baseRepresentative W x * baseRepresentative U x := by
  have h := MemLp.coeFn_toLp (μ := domainMeasure 3 univ)
    (f := fun x ↦ baseRepresentative W x * baseRepresentative U x)
    (by simpa [domainMeasure] using memLp_mul_H1 W U)
  simpa [mulH1, domainMeasure] using h

/-- The convection energy `∑ⱼ ∫ wⱼ a ∂ⱼa` vanishes for a divergence-free `H¹(ℝ³)` field `w`
and every scalar `a ∈ H¹(ℝ³)`. -/
theorem sum_inner_mulH1_partial_self_eq_zero (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (hw : divergenceCLM w = 0) (a : H¹(ℝ^3)) :
    ∑ j, inner ℝ (mulH1 (w j) a) (wkpCoordinateCLM (singleDerivIndex 3 j) a) = 0 := by
  set q : H¹(ℝ^3) → ℝ := fun a ↦
    ∑ j, inner ℝ (mulH1 (w j) a) (wkpCoordinateCLM (singleDerivIndex 3 j) a)
  have hq : Continuous q := continuous_finsetSum _ fun j _ ↦
    ((mulH1 (w j)).continuous).inner (wkpCoordinateCLM (singleDerivIndex 3 j)).continuous
  have hsmooth : ∀ (f : ℝ^3 → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f),
      q (mkWkpSpaceOnOfContDiff (n := 3) (k := 1) (p := 2) (Ω := univ) f hf hc) = 0 := by
    intro f hf hc
    set A := mkWkpSpaceOnOfContDiff (n := 3) (k := 1) (p := 2) (Ω := univ) f hf hc
    have hcoord : ∀ α : DerivIndex 3 1, ((A : WkpAmbientOn 3 1 2 univ) α : ℝ^3 → ℝ) =ᵐ[volume]
        fun x ↦ iteratedPartialDeriv α.toList f x := by
      intro α
      simpa [domainMeasure] using
        mkWkpSpaceOnOfContDiff_apply_ae (n := 3) (k := 1) (p := 2) (Ω := univ) f hf hc α
    have hψ : ContDiff ℝ ∞ (fun x ↦ f x ^ 2 / 2) := (hf.pow 2).div_const 2
    have hψc : HasCompactSupport (fun x ↦ f x ^ 2 / 2) :=
      HasCompactSupport.intro hc fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]
    rw [← sum_integral_base_mul_partialDeriv_eq_zero w hw hψ hψc]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [L2.inner_def]
    simp only [domainMeasure, Measure.restrict_univ]
    apply integral_congr_ae
    filter_upwards [mulH1_ae (w j) A, hcoord (baseIndex 3 1), hcoord (singleDerivIndex 3 j)]
      with x h1 h2 h3
    have hd : PDE.partialDeriv j (fun x ↦ f x ^ 2 / 2) x = f x * PDE.partialDeriv j f x := by
      have hfd := (hf.differentiable (by simp)).differentiableAt (x := x)
      have : HasFDerivAt (fun x ↦ f x ^ 2 / 2) ((1 / 2 : ℝ) • ((2 * f x) • fderiv ℝ f x)) x := by
        have h := (hfd.hasFDerivAt.pow 2).const_mul (1 / 2 : ℝ)
        convert h using 1
        · funext y; ring
        · ext v; simp
      rw [PDE.partialDeriv, this.fderiv, PDE.partialDeriv]
      simp only [one_div, smul_apply, smul_eq_mul]
      ring
    rw [real_inner_eq_re_inner, RCLike.re_to_real, h1, wkpCoordinateCLM_apply, h3, hd]
    simp only [baseRepresentative] at h2 ⊢
    rw [h2]
    simp only [baseIndex_toList, iteratedPartialDeriv, singleDerivIndex_toList, RCLike.inner_apply,
      conj_trivial, wkpBaseCoordinateCLM_apply]
    ring
  obtain ⟨f, hf, hc, hconv⟩ := globalApproximation_WkpSpace (n := 3) (p := 2)
    (Approximation.standardMollifier 3) (by norm_num) 1 a
  have htend : Tendsto (fun m ↦ mkWkpSpaceOnOfContDiff (n := 3) (k := 1) (p := 2) (Ω := univ)
      (f m) (hf m) (hc m)) atTop (𝓝 a) := tendsto_iff_norm_sub_tendsto_zero.mpr hconv
  exact tendsto_nhds_unique ((hq.tendsto a).comp htend)
    (tendsto_const_nhds.congr fun m ↦ (hsmooth (f m) (hf m) (hc m)).symm)


/-- Weak solutions in divergence-free `H¹(ℝ³)` of the shifted linearized self-similar
equation `(μ + L₀) d + Π((w·∇) d) = 0`, `μ ≥ 0`, vanish. The equation is tested against
smooth compactly supported divergence-free fields with all derivatives on the test field. -/
theorem eq_zero_of_weak_shifted_convection (d w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (hd : divergenceCLM d = 0) (hw : divergenceCLM w = 0) {μ : ℝ} (hμ : 0 ≤ μ)
    (heq : ∀ φ : ℝ^3 → ℝ^3, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, PDE.divergence φ x = 0) →
      ∑ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x *
        ((μ + 1) * φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun z ↦ φ z i) x) =
      ∑ i, ∑ j, ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
        (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x * PDE.partialDeriv j (fun z ↦ φ z i) x) :
    d = 0 := by
  -- the drift functional
  set P : Fin 3 → Fin 3 → DerivLp 3 2 univ := fun i j ↦ mulH1 (w j) (d i)
  set Ψ : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)) →L[ℝ] ℝ := (2 : ℝ) •
    (∑ i, ∑ j, (innerSL ℝ (P i j)).comp ((wkpCoordinateCLM (singleDerivIndex 3 j)).comp
        (PiLp.proj 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)) i)) -
      (μ + 1) • ∑ i, (innerSL ℝ (wkpBaseCoordinateCLM (d i))).comp
        (wkpBaseCoordinateCLM.comp (PiLp.proj 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)) i)) -
      ∑ i, ∑ j, (innerSL ℝ (wkpCoordinateCLM (singleDerivIndex 3 j) (d i))).comp
        ((wkpCoordinateCLM (singleDerivIndex 3 j)).comp
          (PiLp.proj 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)) i)))
  have hΨ : ∀ v, Ψ v = 2 * (∑ i, ∑ j, inner ℝ (P i j)
      (wkpCoordinateCLM (singleDerivIndex 3 j) (v i)) - (μ + 1) * massPairing d v -
      ∑ i, ∑ j, inner ℝ (wkpCoordinateCLM (singleDerivIndex 3 j) (d i))
        (wkpCoordinateCLM (singleDerivIndex 3 j) (v i))) := by
    intro v
    simp [Ψ, massPairing, innerSL_apply_apply, Finset.mul_sum]
  have hdm : ∀ i, MemLp (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) 2 volume := fun i ↦ by
    simpa [domainMeasure] using Lp.memLp (wkpBaseCoordinateCLM (d i))
  -- the weak equation in terms of the drift functional
  have hΛ : ∀ (φ : ℝ^3 → ℝ^3) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      (∀ x, PDE.divergence φ x = 0) →
      ∑ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x * fderiv ℝ φ x x i =
        Ψ (testFieldH1 φ hφ hc) := by
    intro φ hφ hc hdiv
    have h := heq φ hφ hc hdiv
    have hcomp : ∀ i, ContDiff ℝ ∞ (fun x ↦ φ x i) := contDiff_component hφ
    have hcompc : ∀ i, HasCompactSupport (fun x ↦ φ x i) := hasCompactSupport_component hc
    have hsplit : ∀ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x *
        ((μ + 1) * φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun z ↦ φ z i) x) =
        (μ + 1) * (∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x * φ x i) +
          (1 / 2) * (∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x * fderiv ℝ φ x x i) -
          ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x * PDE.laplacian (fun z ↦ φ z i) x :=
      fun i ↦ integral_mul_shiftedAdjoint _ _ hφ hc i
    -- the coordinates of the test field
    have hTcoord : ∀ i j, ((wkpCoordinateCLM (singleDerivIndex 3 j) (testFieldH1 φ hφ hc i) :
        DerivLp 3 2 univ) : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ PDE.partialDeriv j (fun z ↦ φ z i) x := by
      intro i j
      simpa [domainMeasure, iteratedPartialDeriv, wkpCoordinateCLM_apply, testFieldH1] using
        mkWkpSpaceOnOfContDiff_apply_ae (n := 3) (k := 1) (p := 2) (Ω := univ)
          (fun x ↦ φ x i) (hcomp i) (hcompc i) (singleDerivIndex 3 j)
    have hC : ∀ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x *
        PDE.laplacian (fun z ↦ φ z i) x =
        -∑ j, inner ℝ (wkpCoordinateCLM (singleDerivIndex 3 j) (d i))
          (wkpCoordinateCLM (singleDerivIndex 3 j) (testFieldH1 φ hφ hc i)) := by
      intro i
      have hint : ∀ j : Fin 3, Integrable (fun x ↦ (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x *
          PDE.partialDeriv j (fun z ↦ PDE.partialDeriv j (fun w ↦ φ w i) z) x) := fun j ↦
        integrable_base_mul (d i)
          ((PDE.contDiff_top_partialDeriv (i := j) (PDE.contDiff_top_partialDeriv (i := j)
            (hcomp i))).continuous) (((hcompc i).partialDeriv j).partialDeriv j)
      simp only [PDE.laplacian, Finset.mul_sum]
      rw [integral_finsetSum _ fun j _ ↦ hint j, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [integral_base_mul_partialDeriv (d i) j (PDE.contDiff_top_partialDeriv (i := j) (hcomp i))
        ((hcompc i).partialDeriv j), inner_eq_integral_mul_of_ae (by rfl) (hTcoord i j)]
    have hR : ∀ i j, ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
        (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x * PDE.partialDeriv j (fun z ↦ φ z i) x =
        inner ℝ (P i j) (wkpCoordinateCLM (singleDerivIndex 3 j) (testFieldH1 φ hφ hc i)) := by
      intro i j
      rw [inner_eq_integral_mul_of_ae (mulH1_ae (w j) (d i)) (hTcoord i j)]
      rfl
    simp only [hsplit, hC, hR, sub_neg_eq_add, Finset.sum_add_distrib, ← Finset.mul_sum] at h
    rw [hΨ, massPairing_testFieldH1]
    linarith
  -- the energy inequality
  have hdcl := mem_topologicalClosure_span_solenoidalTestFields (by norm_num) d hd
  have hlow := (drift_eq_neg_half_mul_massPairing _
    (fun _ hφ hdiv s _ ↦ divergence_comp_smul hφ hdiv s) d Ψ hΛ hdcl).ge
  rw [hΨ] at hlow
  have hconv : ∀ i, ∑ j, inner ℝ (P i j) (wkpCoordinateCLM (singleDerivIndex 3 j) (d i)) = 0 :=
    fun i ↦ sum_inner_mulH1_partial_self_eq_zero w hw (d i)
  simp only [hconv, Finset.sum_const_zero, zero_sub] at hlow
  have hG : 0 ≤ ∑ i, ∑ j, inner ℝ (wkpCoordinateCLM (singleDerivIndex 3 j) (d i))
      (wkpCoordinateCLM (singleDerivIndex 3 j) (d i)) :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ real_inner_self_nonneg
  have hM : 0 ≤ massPairing d d :=
    Finset.sum_nonneg fun i _ ↦ real_inner_self_nonneg
  have hM0 : massPairing d d = 0 := by
    push_cast at hlow
    nlinarith
  -- each base row vanishes
  ext i : 1
  apply wkpBaseCoordinateCLM_injective (n := 3) (p := 2) isOpen_univ
  rw [PiLp.zero_apply, map_zero]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ real_inner_self_nonneg)).mp hM0 i
    (Finset.mem_univ i)
  exact inner_self_eq_zero.mp hterm

end NavierStokes.Stationary
