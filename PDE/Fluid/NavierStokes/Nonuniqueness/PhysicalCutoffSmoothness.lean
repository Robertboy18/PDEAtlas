/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalTimeRegularity
public import PDE.Parabolic.Heat.WholeSpace.GaussianFlowDerivative
public import PDE.Parabolic.Heat.ConvolutionSpace.Equation
public import PDE.Parabolic.Heat.ConvolutionTime
public import PDE.Analysis.MeasureTheory.Lp.SymbolDecay
public import PDE.Parabolic.Heat.WholeSpace.GaussianFlowTrace

/-!
# The physical cutoff field is a smooth path

The localization remainder `w` agrees with the far field `‖x‖⁻¹ A(x)` outside a ball, so it has
symbol decay of order `-1`: all its derivatives are bounded, and its Laplacian has all
derivatives square integrable. The heat flow `e^{tΔ} w` then differs from `e^{t₀Δ} w` by
`∫_{t₀}^t e^{sΔ} Δw ds`, a smooth path in every `Hᴺ` (the heat semigroup is smooth on smooth
vectors), so the physical cutoff field `-e^{tΔ} w` is a smooth path on `(0, 1)` in every
`W^{k,∞}` and every `W^{k,4}` (`contDiffOn_physicalCutoffSobolev_top`,
`contDiffOn_physicalCutoffSobolev_four`).
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Analysis
open scoped NNReal ENNReal Sobolev ContDiff

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

namespace UnstableProfile

variable (D : UnstableProfile) {R : ℝ}

/-- The localization remainder has symbol decay of order `-1`. -/
theorem hasSymbolDecay_localizationRemainder (hR : 0 < R) :
    HasSymbolDecay (-1) (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) := by
  have hfar : HasSymbolDecay (-1) (fun x : ℝ^3 ↦ ‖x‖⁻¹ • D.A x) :=
    hasSymbolDecay_of_homogeneous (fun x hx ↦ (D.contDiffAt_farField hx).contDiffWithinAt)
      fun x c hc ↦ by rw [D.farField_smul x hc, zpow_neg_one]
  exact hfar.of_eqOn_far
    (contDiff_localizationRemainder hR fun x hx ↦ D.contDiffAt_farField hx).contDiffOn
    (R := 2 * R) fun x hx ↦ localizationRemainder_of_two_mul_lt hR hx

/-! ### The heat semigroup on smooth vectors -/

/-- Forgetting orders of a smooth field in vector Sobolev spaces. -/
theorem vectorLowerOrderCLM_toLp_vectorWkpOfContDiff {M N : ℕ} (h : N ≤ M) {X : ℝ^3 → ℝ^3}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hX2 : ∀ m : ℕ, MemLp (iteratedFDeriv ℝ m X) 2 volume) :
    vectorLowerOrderCLM h (WithLp.toLp 2 (vectorWkpOfContDiff (k := M) X hX fun m _ ↦ hX2 m)) =
      WithLp.toLp 2 (vectorWkpOfContDiff (k := N) X hX fun m _ ↦ hX2 m) := by
  refine PiLp.ext fun j ↦ WkpSpaceOn.ext_of_base_ae isOpen_univ _ _ ?_
  change baseRepresentative _ =ᵐ[domainMeasure 3 univ] baseRepresentative _
  rw [vectorLowerOrderCLM_apply, baseRepresentative_lowerOrderCLM]
  simp only [domainMeasure, Measure.restrict_univ]
  exact (baseRepresentative_toLp_vectorWkpOfContDiff_ae (N := M) hX (fun m _ ↦ hX2 m) j).trans
    (baseRepresentative_toLp_vectorWkpOfContDiff_ae (N := N) hX (fun m _ ↦ hX2 m) j).symm

/-- The Laplacian of a smooth field in vector Sobolev spaces. -/
theorem vectorLaplacian_toLp_vectorWkpOfContDiff {N : ℕ} {X : ℝ^3 → ℝ^3}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hX2 : ∀ m : ℕ, MemLp (iteratedFDeriv ℝ m X) 2 volume)
    (hL : ContDiff ℝ (⊤ : ℕ∞) (PDE.laplacian X))
    (hL2 : ∀ m : ℕ, MemLp (iteratedFDeriv ℝ m (PDE.laplacian X)) 2 volume) :
    vectorLaplacian 3 N (WithLp.toLp 2 (vectorWkpOfContDiff (k := N + 2) X hX fun m _ ↦ hX2 m)) =
      WithLp.toLp 2 (vectorWkpOfContDiff (k := N) (PDE.laplacian X) hL fun m _ ↦ hL2 m) := by
  set w : VectorH 3 (N + 2) := WithLp.toLp 2 (vectorWkpOfContDiff X hX fun m _ ↦ hX2 m)
  refine PiLp.ext fun j ↦ WkpSpaceOn.ext_of_base_ae isOpen_univ _ _ ?_
  change baseRepresentative _ =ᵐ[domainMeasure 3 univ] baseRepresentative _
  simp only [domainMeasure, Measure.restrict_univ]
  have hw0 := baseRepresentative_toLp_vectorWkpOfContDiff_ae (N := N + 2) hX
    (fun m _ ↦ hX2 m) j
  have hΔ : baseRepresentative (vectorLaplacian 3 N w j) =ᵐ[volume]
      fun x ↦ ∑ i : Fin 3, iteratedPartialDeriv [i, i] (fun y ↦ X y j) x := by
    rw [vectorLaplacian_apply, higherOrderLaplacianCLM, sum_apply]
    have hs := baseRepresentative_sum_ae (fun i : Fin 3 ↦
      (derivativeWordCLM [i, i] (by simp [Nat.add_comm]) (w j) : W^{N,2}(ℝ^3)))
    simp only [domainMeasure, Measure.restrict_univ] at hs
    have hi := fun i : Fin 3 ↦ baseRepresentative_derivativeWordCLM_ae (k := N) isOpen_univ (w j)
      (fun y ↦ X y j) [i, i] (by simp [Nat.add_comm])
      ((EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).contDiff.comp (hX.of_le (by exact_mod_cast le_top)))
      (by simpa only [domainMeasure, Measure.restrict_univ] using hw0)
    simp only [domainMeasure, Measure.restrict_univ] at hi
    filter_upwards [hs, ae_all_iff.mpr hi] with x hx hix
    rw [hx]
    exact Finset.sum_congr rfl fun i _ ↦ hix i
  filter_upwards [hΔ, baseRepresentative_toLp_vectorWkpOfContDiff_ae (N := N) hL
    (fun m _ ↦ hL2 m) j] with x h₁ h₂
  rw [h₁, h₂, laplacian_component hX x j]

/-- The heat evolution of a smooth field with square-integrable derivatives, in vector `Hᴺ`. -/
def heatPath (X : ℝ^3 → ℝ^3) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hX2 : ∀ m : ℕ, MemLp (iteratedFDeriv ℝ m X) 2 volume) (N : ℕ) (s : ℝ) : VectorH 3 N :=
  vectorHeat 3 N s.toNNReal (WithLp.toLp 2 (vectorWkpOfContDiff X hX fun m _ ↦ hX2 m))

/-- The Laplacian keeps a smooth field with square-integrable derivatives in the class. -/
theorem memLp_iteratedFDeriv_laplacian {X : ℝ^3 → ℝ^3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hX2 : ∀ m : ℕ, MemLp (iteratedFDeriv ℝ m X) 2 volume) (m : ℕ) :
    MemLp (iteratedFDeriv ℝ m (PDE.laplacian X)) 2 volume := by
  have hlap : ContDiff ℝ (⊤ : ℕ∞) (PDE.laplacian X) := by
    unfold PDE.laplacian
    exact ContDiff.sum fun i _ ↦ PDE.contDiff_top_partialDeriv (PDE.contDiff_top_partialDeriv hX)
  refine ((hX2 (m + 2)).norm.const_mul 3).of_le
    ((hlap.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs]
  exact (norm_iteratedFDeriv_laplacian_le hX m x).trans (le_abs_self _)

/-- The Laplacian of a smooth field is smooth. -/
theorem contDiff_laplacian_of_top {X : ℝ^3 → ℝ^3} (hX : ContDiff ℝ (⊤ : ℕ∞) X) :
    ContDiff ℝ (⊤ : ℕ∞) (PDE.laplacian X) := by
  unfold PDE.laplacian
  exact ContDiff.sum fun i _ ↦ PDE.contDiff_top_partialDeriv (PDE.contDiff_top_partialDeriv hX)

/-- The heat evolution of a smooth field is differentiable at positive times, with the heat
evolution of the Laplacian as derivative. -/
theorem hasDerivAt_heatPath {X : ℝ^3 → ℝ^3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hX2 : ∀ m : ℕ, MemLp (iteratedFDeriv ℝ m X) 2 volume) (N : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (heatPath X hX hX2 N)
      (heatPath (PDE.laplacian X) (contDiff_laplacian_of_top hX)
        (memLp_iteratedFDeriv_laplacian hX hX2) N s) s := by
  have hg := hasGeneratorAt_vectorHeatSemigroup (n := 3) (k := N)
    (WithLp.toLp 2 (vectorWkpOfContDiff (k := N + 2) X hX fun m _ ↦ hX2 m))
  rw [vectorLowerOrderCLM_toLp_vectorWkpOfContDiff, vectorLaplacian_toLp_vectorWkpOfContDiff hX hX2
    (contDiff_laplacian_of_top hX) (memLp_iteratedFDeriv_laplacian hX hX2)] at hg
  exact hg.hasDerivAt_realOrbit hs

/-- **The heat semigroup is smooth on smooth vectors**: the heat evolution of a smooth field
with square-integrable derivatives is smooth at positive times in every vector `Hᴺ`. -/
theorem contDiffOn_heatPath : ∀ (j : ℕ) {X : ℝ^3 → ℝ^3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hX2 : ∀ m : ℕ, MemLp (iteratedFDeriv ℝ m X) 2 volume) (N : ℕ),
    ContDiffOn ℝ j (heatPath X hX hX2 N) (Ioi 0) := by
  intro j
  induction j with
  | zero =>
    intro X hX hX2 N
    exact contDiffOn_zero.mpr fun s hs ↦
      (hasDerivAt_heatPath hX hX2 N hs).continuousAt.continuousWithinAt
  | succ j ih =>
    intro X hX hX2 N
    rw [show ((j + 1 : ℕ) : WithTop ℕ∞) = (j : WithTop ℕ∞) + 1 by norm_cast,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun s hs ↦ (hasDerivAt_heatPath hX hX2 N hs).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    exact (ih (contDiff_laplacian_of_top hX) (memLp_iteratedFDeriv_laplacian hX hX2) N).congr
      fun s hs ↦ (hasDerivAt_heatPath hX hX2 N hs).deriv

/-! ### The remainder and its heat flow -/

/-- The localization remainder is smooth. -/
theorem contDiff_remainder (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) :=
  contDiff_localizationRemainder hR fun _ hx ↦ D.contDiffAt_farField hx

/-- Every derivative of the localization remainder is bounded. -/
theorem exists_bound_iteratedFDeriv_remainder (hR : 0 < R) (m : ℕ) :
    ∃ M, ∀ x, ‖iteratedFDeriv ℝ m (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) x‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := (D.hasSymbolDecay_localizationRemainder hR).exists_bound_one_add_norm
    (D.contDiff_remainder hR) (k := m) (by omega)
  exact ⟨C, fun x ↦ (hC x).trans (div_le_self hC0 (one_le_pow₀ (by linarith [norm_nonneg x])))⟩

/-- Every derivative of the Laplacian of the localization remainder is square integrable. -/
theorem memLp_iteratedFDeriv_laplacian_remainder (hR : 0 < R) (m : ℕ) :
    MemLp (iteratedFDeriv ℝ m
      (PDE.laplacian (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R))) 2 volume :=
  (D.hasSymbolDecay_localizationRemainder hR).laplacian.memLp_iteratedFDeriv
    (contDiff_laplacian_of_top (D.contDiff_remainder hR)) m (by
      simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat, Int.cast_sub,
        Int.cast_neg, Int.cast_one, Int.cast_ofNat, ENNReal.toReal_ofNat]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)

/-- The physical cutoff field is minus the heat flow of the remainder. -/
theorem dilateField_cutoffFieldFn {t : ℝ} (ht : 0 < t) (x : ℝ^3) :
    dilateField (physicalFactor (Real.log t)) (cutoffFieldFn D R (Real.log t)) x =
      -gaussianFlow t (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) x := by
  have hc : cutoffFieldFn D R (Real.log t) = cutoffField D R (Real.log t) := by
    rw [cutoffField_eq_conv, cutoffFieldFn]
    have h := gaussianFlow_const_smul 1 (-1 : ℝ) (fun x ↦ Real.exp (Real.log t / 2) •
      localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R (Real.exp (Real.log t / 2) • x))
    rw [neg_one_smul] at h
    rw [← h]
    congr 1
    funext y
    simp
  rw [dilateField, hc, physicalFactor_log ht]
  exact inv_sqrt_smul_cutoffField D R ht x

/-- The Laplacian of the remainder is bounded. -/
theorem exists_bound_laplacian_remainder (hR : 0 < R) :
    ∃ M, ∀ x, ‖PDE.laplacian (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) x‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ :=
    (D.hasSymbolDecay_localizationRemainder hR).laplacian.exists_bound_one_add_norm
      (contDiff_laplacian_of_top (D.contDiff_remainder hR)) (k := 0) (by omega)
  refine ⟨C, fun x ↦ ?_⟩
  have := (hC x).trans (div_le_self hC0 (one_le_pow₀ (by linarith [norm_nonneg x])))
  simpa [norm_iteratedFDeriv_zero] using this

/-- The increment `∫_{1/2}^t e^{sΔ} Δw ds` of the heat flow of the remainder, in vector `Hᴺ`. -/
def cutoffIncrement (hR : 0 < R) (N : ℕ) (t : ℝ) : VectorH 3 N :=
  ∫ s in (1 / 2 : ℝ)..t, heatPath (PDE.laplacian (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R))
    (contDiff_laplacian_of_top (D.contDiff_remainder hR))
    (D.memLp_iteratedFDeriv_laplacian_remainder hR) N s

/-- The interval between `1/2` and `t > 0` is positive. -/
theorem uIcc_half_subset_Ioi {t : ℝ} (ht : 0 < t) : uIcc (1 / 2 : ℝ) t ⊆ Ioi 0 := fun _ hx ↦
  lt_of_lt_of_le (lt_min (by norm_num) ht) hx.1

/-- The increment is differentiable at positive times. -/
theorem hasDerivAt_cutoffIncrement (hR : 0 < R) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (D.cutoffIncrement hR N)
      (heatPath (PDE.laplacian (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R))
        (contDiff_laplacian_of_top (D.contDiff_remainder hR))
        (D.memLp_iteratedFDeriv_laplacian_remainder hR) N t) t := by
  have hc := (contDiffOn_heatPath 0 (contDiff_laplacian_of_top (D.contDiff_remainder hR))
    (D.memLp_iteratedFDeriv_laplacian_remainder hR) N).continuousOn
  have _ : SecondCountableTopologyEither ℝ (VectorH 3 N) :=
    secondCountableTopologyEither_of_left ℝ _
  exact intervalIntegral.integral_hasDerivAt_right
    ((hc.mono (uIcc_half_subset_Ioi ht)).intervalIntegrable)
    (hc.stronglyMeasurableAtFilter isOpen_Ioi t ht) (hc.continuousAt (Ioi_mem_nhds ht))

/-- The increment is smooth at positive times in every vector `Hᴺ`. -/
theorem contDiffOn_cutoffIncrement (hR : 0 < R) (N : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (D.cutoffIncrement hR N) (Ioi 0) := by
  refine contDiffOn_infty.mpr fun j ↦ ?_
  rcases j with _ | j
  · exact contDiffOn_zero.mpr fun t ht ↦
      (D.hasDerivAt_cutoffIncrement hR N ht).continuousAt.continuousWithinAt
  · rw [show ((j + 1 : ℕ) : WithTop ℕ∞) = (j : WithTop ℕ∞) + 1 by norm_cast,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun t ht ↦ (D.hasDerivAt_cutoffIncrement hR N ht).differentiableAt
      |>.differentiableWithinAt, by simp, ?_⟩
    exact (contDiffOn_heatPath j _ _ N).congr fun t ht ↦
      (D.hasDerivAt_cutoffIncrement hR N ht).deriv

/-- The time derivative of the heat flow of a component of the remainder is the heat flow of the
component of its Laplacian. -/
theorem hasDerivAt_initialValueSolution_remainder (hR : 0 < R) (j : Fin 3) (x : ℝ^3) {s : ℝ}
    (hs : 0 < s) :
    HasDerivAt (fun r ↦ HeatEquation.initialValueSolution
        (fun y ↦ localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R y j) x r)
      (HeatEquation.initialValueSolution
        (fun y ↦ PDE.laplacian (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) y j) x s) s := by
  set W := localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R
  have hW := D.contDiff_remainder hR
  have hWj : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ W y j) :=
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).contDiff.comp hW
  have hbj : ∀ m : ℕ, ∃ M, ∀ x, ‖iteratedFDeriv ℝ m (fun y ↦ W y j) x‖ ≤ M := fun m ↦ by
    obtain ⟨M, hM⟩ := D.exists_bound_iteratedFDeriv_remainder hR m
    exact ⟨M, fun x ↦ (PDE.norm_iteratedFDeriv_component_le hW j m x).trans (hM x)⟩
  obtain ⟨M₀, h₀⟩ := hbj 0
  have hbdd : ∃ M, ∀ y, |W y j| ≤ M :=
    ⟨M₀, fun y ↦ by simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h₀ y⟩
  have hd := HeatEquation.hasDerivAt_initialValueSolution_time (fun y ↦ W y j) x s hs
    hWj.continuous hbdd
  have hderiv := HeatEquation.deriv_initialValueSolution_time_eq_laplacian (fun y ↦ W y j) x s hs
    hWj.continuous hbdd
  have hlap : PDE.laplacian (fun x' ↦ HeatEquation.initialValueSolution (fun y ↦ W y j) x' s) x =
      HeatEquation.initialValueSolution (fun y ↦ PDE.laplacian W y j) x s := by
    have h₁ : (fun x' ↦ HeatEquation.initialValueSolution (fun y ↦ W y j) x' s) =
        gaussianFlow s (fun y ↦ W y j) :=
      funext fun x' ↦ initialValueSolution_eq_gaussianFlow _ x' s
    rw [h₁, laplacian_gaussianFlow hs hWj hbj, initialValueSolution_eq_gaussianFlow]
    congr 1
    funext y
    exact (laplacian_component hW y j).symm
  rw [← hlap, ← hderiv]
  exact hd.differentiableAt.hasDerivAt

/-- **The increment is the difference of heat flows**: `∫_{1/2}^t e^{sΔ} Δw ds` is
`e^{tΔ} w - e^{Δ/2} w`. -/
theorem baseRepresentative_cutoffIncrement_ae (hR : 0 < R) (N : ℕ) {t : ℝ} (ht : 0 < t)
    (j : Fin 3) :
    baseRepresentative (D.cutoffIncrement hR N t j) =ᵐ[volume] fun x ↦
      gaussianFlow t (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) x j -
        gaussianFlow (1 / 2) (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) x j := by
  set W := localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R with hWdef
  set L := PDE.laplacian W
  have hW := D.contDiff_remainder hR
  have hLc : ContDiff ℝ (⊤ : ℕ∞) L := contDiff_laplacian_of_top hW
  have hL2 := D.memLp_iteratedFDeriv_laplacian_remainder hR
  set T := baseComponentCLM N j
  set c : ℝ := min t (1 / 2)
  have hc0 : 0 < c := lt_min ht (by norm_num)
  obtain ⟨ML, hML⟩ := D.exists_bound_laplacian_remainder hR
  have hLj : Continuous (fun y ↦ L y j) :=
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous.comp hLc.continuous
  have hLb : ∃ M, ∀ y, |L y j| ≤ M :=
    ⟨ML, fun y ↦ (by rw [← Real.norm_eq_abs]; exact (PiLp.norm_apply_le _ j).trans (hML y))⟩
  set f : ℝ → ℝ^3 → ℝ := fun r x ↦ HeatEquation.initialValueSolution (fun y ↦ L y j) x (max r c)
    with hfdef
  have hf : Continuous (Function.uncurry f) := by
    have hcd := HeatEquation.contDiffOn_initialValueSolution_timeSpace (fun y ↦ L y j) hLj hLb
    exact hcd.continuousOn.comp_continuous
      ((continuous_fst.max continuous_const).prodMk continuous_snd)
      fun p ↦ lt_of_lt_of_le hc0 (le_max_right _ _)
  have hcp := (contDiffOn_heatPath 0 hLc hL2 N).continuousOn
  have key : ∀ a b : ℝ, c ≤ a → a ≤ b →
      ((∫ r in a..b, T (heatPath L hLc hL2 N r) : DerivLp 3 2 univ) : ℝ^3 → ℝ)
        =ᵐ[domainMeasure 3 univ] fun x ↦ ∫ r in a..b, f r x := fun a b hca hab ↦ by
    refine coeFn_intervalIntegral_ae (by simp [domainMeasure]) hab
      (T.continuous.comp_continuousOn (hcp.mono fun r hr ↦ lt_of_lt_of_le hc0
        (hca.trans hr.1))) hf fun r hr ↦ ?_
    have hr0 : 0 < r := lt_of_lt_of_le hc0 (hca.trans hr.1)
    rw [Function.comp_apply, coeFn_baseComponentCLM]
    have h₁ := baseRepresentative_heatSobolev (n := 3) (k := N) r.toNNReal
      ((WithLp.toLp 2 (vectorWkpOfContDiff L hLc fun m _ ↦ hL2 m) : VectorH 3 N) j)
    have h₂ := baseRepresentative_toLp_vectorWkpOfContDiff_ae (N := N) hLc (fun m _ ↦ hL2 m) j
    rw [Real.coe_toNNReal _ hr0.le, gaussianFlow_congr_ae hr0 h₂] at h₁
    simp only [domainMeasure, Measure.restrict_univ]
    filter_upwards [h₁] with x hx
    change baseRepresentative (vectorHeat 3 N r.toNNReal _ j) x = _
    rw [vectorHeat_apply, hx, hfdef]
    simp only [max_eq_left (hca.trans hr.1)]
    rw [initialValueSolution_eq_gaussianFlow]
  have hint : IntervalIntegrable (heatPath L hLc hL2 N) volume (1 / 2) t :=
    (hcp.mono (uIcc_half_subset_Ioi ht)).intervalIntegrable
  have hcomm : T (D.cutoffIncrement hR N t) = ∫ r in (1 / 2 : ℝ)..t, T (heatPath L hLc hL2 N r) :=
    (T.intervalIntegral_comp_comm hint).symm
  have hgoal : ((T (D.cutoffIncrement hR N t) : DerivLp 3 2 univ) : ℝ^3 → ℝ)
      =ᵐ[domainMeasure 3 univ] fun x ↦ ∫ r in (1 / 2 : ℝ)..t, f r x := by
    rw [hcomm]
    rcases le_or_gt (1 / 2) t with h1 | h1
    · exact key (1 / 2) t (min_le_right _ _) h1
    · rw [intervalIntegral.integral_symm]
      filter_upwards [Lp.coeFn_neg (∫ r in t..(1 / 2 : ℝ), T (heatPath L hLc hL2 N r)),
        key t (1 / 2) (min_le_left _ _) h1.le] with x hx₁ hx₂
      rw [hx₁, Pi.neg_apply, hx₂, intervalIntegral.integral_symm, neg_neg]
  rw [coeFn_baseComponentCLM] at hgoal
  simp only [domainMeasure, Measure.restrict_univ] at hgoal
  filter_upwards [hgoal] with x hx
  rw [hx]
  -- the pointwise integral
  have hFTC : ∀ r ∈ uIcc (1 / 2 : ℝ) t, HasDerivAt (fun r ↦ HeatEquation.initialValueSolution
      (fun y ↦ W y j) x r) (f r x) r := fun r hr ↦ by
    have hcr : c ≤ r := by
      rcases le_total (1 / 2 : ℝ) t with h | h
      · rw [uIcc_of_le h] at hr
        exact (min_le_right _ _).trans hr.1
      · rw [uIcc_of_ge h] at hr
        exact (min_le_left _ _).trans hr.1
    rw [hfdef]
    simp only [max_eq_left hcr]
    exact D.hasDerivAt_initialValueSolution_remainder hR j x (lt_of_lt_of_le hc0 hcr)
  have hfi : IntervalIntegrable (fun r ↦ f r x) volume (1 / 2) t :=
    (hf.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFTC hfi,
    initialValueSolution_eq_gaussianFlow, initialValueSolution_eq_gaussianFlow,
    ← gaussianFlow_component t (by norm_num : (1 : ℝ≥0∞) ≤ 4)
      (D.memLp_four_localizationRemainder R),
    ← gaussianFlow_component (1 / 2) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
      (D.memLp_four_localizationRemainder R)]

/-! ### The physical cutoff field -/

/-- The heat flow of the remainder at time `1/2` is smooth. -/
theorem contDiff_gaussianFlow_half_remainder :
    ContDiff ℝ (⊤ : ℕ∞) (gaussianFlow (1 / 2) (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R)) :=
  contDiff_gaussianFlow (by norm_num) (p := 4) (by norm_num) (D.memLp_four_localizationRemainder R)

/-- Every derivative of the heat flow of the remainder at time `1/2` lies in `Lʳ`, `r ≥ 4`. -/
theorem memLp_iteratedFDeriv_gaussianFlow_half_remainder {r : ℝ≥0∞} (hr : 4 ≤ r) (m : ℕ) :
    MemLp (iteratedFDeriv ℝ m
      (gaussianFlow (1 / 2) (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R))) r volume :=
  memLp_iteratedFDeriv_gaussianFlow (by norm_num) (by norm_num) hr
    (D.memLp_four_localizationRemainder R) m

/-- The physical cutoff field is `-(e^{Δ/2} w + ι Ψ(t))` with the smooth increment `Ψ`. -/
theorem physicalCutoffSobolev_eq (hR : 0 < R) {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 4 ≤ r)
    (hq : ∀ U : W^{3,2}(ℝ^3), MemLp (baseRepresentative U) r (domainMeasure 3 univ)) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    physicalCutoffSobolev D R k hr t =
      -(vectorWkpOfContDiff
          (gaussianFlow (1 / 2) (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R))
          D.contDiff_gaussianFlow_half_remainder
          (fun m _ ↦ D.memLp_iteratedFDeriv_gaussianFlow_half_remainder hr m) +
        vectorHilbertEmbeddingCLM k hq (D.cutoffIncrement hR (k + 3) t)) := by
  funext j
  refine WkpSpaceOn.ext_of_base_ae isOpen_univ _ _ ?_
  change baseRepresentative _ =ᵐ[domainMeasure 3 univ] baseRepresentative _
  simp only [Pi.neg_apply, Pi.add_apply]
  have h₁ := baseRepresentative_neg_ae (vectorWkpOfContDiff
    (gaussianFlow (1 / 2) (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R))
    D.contDiff_gaussianFlow_half_remainder
    (fun m (_ : m ≤ k) ↦ D.memLp_iteratedFDeriv_gaussianFlow_half_remainder hr m) j +
      vectorHilbertEmbeddingCLM k hq (D.cutoffIncrement hR (k + 3) t) j)
  have h₂ := baseRepresentative_add_ae (vectorWkpOfContDiff
    (gaussianFlow (1 / 2) (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R))
    D.contDiff_gaussianFlow_half_remainder
    (fun m (_ : m ≤ k) ↦ D.memLp_iteratedFDeriv_gaussianFlow_half_remainder hr m) j)
    (vectorHilbertEmbeddingCLM k hq (D.cutoffIncrement hR (k + 3) t) j)
  simp only [domainMeasure, Measure.restrict_univ] at h₁ h₂ ⊢
  have h₃ : baseRepresentative (vectorHilbertEmbeddingCLM k hq (D.cutoffIncrement hR (k + 3) t) j)
      = baseRepresentative (D.cutoffIncrement hR (k + 3) t j) := by
    simp only [vectorHilbertEmbeddingCLM, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.comp_apply, PiLp.proj_apply, baseRepresentative_hilbertEmbeddingCLM]
  filter_upwards [baseRepresentative_vectorWkpOfContDiff _ _
      (fun m (_ : m ≤ k) ↦ (memLp_iteratedFDeriv_dilateField (physicalFactor_pos _).ne'
        (contDiff_cutoffFieldFn D R _) (memLp_iteratedFDeriv_cutoffFieldFn D R hr _ m))) j,
    h₁, h₂, baseRepresentative_vectorWkpOfContDiff _ _
      (fun m (_ : m ≤ k) ↦ D.memLp_iteratedFDeriv_gaussianFlow_half_remainder hr m) j,
    D.baseRepresentative_cutoffIncrement_ae hR (k + 3) ht j] with x e₁ e₂ e₃ e₄ e₅
  change baseRepresentative (vectorWkpOfContDiff
    (dilateField (physicalFactor (Real.log t)) (cutoffFieldFn D R (Real.log t))) _ _ j) x = _
  rw [e₁, e₂, e₃, e₄, h₃, e₅, D.dilateField_cutoffFieldFn ht x, PiLp.neg_apply]
  ring

/-- **The physical cutoff field is a smooth path** on `(0, 1)` in `W^{k,r}`, for an exponent
`r ≥ 4` with `H³(ℝ³) ⊂ Lʳ`. -/
theorem contDiffOn_physicalCutoffSobolev (hR : 0 < R) {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 4 ≤ r)
    (hq : ∀ U : W^{3,2}(ℝ^3), MemLp (baseRepresentative U) r (domainMeasure 3 univ)) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffSobolev D R k hr) (Ioo 0 1) := by
  let _ : NormedSpace ℝ (Fin 3 → W^{k,r}(ℝ^3)) := Pi.normedSpace
  refine (contDiffOn_const.add ((vectorHilbertEmbeddingCLM k hq).contDiff.comp_contDiffOn
    ((D.contDiffOn_cutoffIncrement hR (k + 3)).mono Ioo_subset_Ioi_self))).neg.congr
    fun t ht ↦ D.physicalCutoffSobolev_eq hR hr hq k ht.1

/-- The physical cutoff field is a smooth path on `(0, 1)` in every `W^{k,∞}`. -/
theorem contDiffOn_physicalCutoffSobolev_top (hR : 0 < R) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffSobolev D R k le_top) (Ioo 0 1) :=
  D.contDiffOn_physicalCutoffSobolev hR le_top memLp_top_baseRepresentative_three k

/-- The physical cutoff field is a smooth path on `(0, 1)` in every `W^{k,4}`. -/
theorem contDiffOn_physicalCutoffSobolev_four (hR : 0 < R) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffSobolev D R k le_rfl) (Ioo 0 1) :=
  have : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
  D.contDiffOn_physicalCutoffSobolev hR le_rfl memLp_four_baseRepresentative_three k

end UnstableProfile

/-- **Time regularity of the constructed solutions.** Above the threshold radius and for
`s ∈ [0, 1]`, the physical correction `u_cor(t) = t^{-1/2} U_cor(log t, ·/√t)` is `C^j` on
`(0, 1)` with values in every vector `Hᵐ⁺¹`, for every `j`, and the physical velocity is smooth
at every point of `(0, 1) × ℝ³`. -/
theorem physical_time_regularity (D : UnstableProfile) (R s : ℝ) (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    (∀ (j m : ℕ) (hm : (3 : ℝ) < 2 * m),
        ContDiffOn ℝ j (physicalCorrection D R s m hm) (Ioo 0 1)) ∧
      ∀ z ∈ IncompressibleFlow.finiteTimeDomain 3 1,
        ContDiffAt ℝ (⊤ : ℕ∞) (physicalVelocity D R s) z := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (D.one_le_ancientThreshold.trans hR)
  exact physical_time_regularity_of_cutoff D R s hR hs
    (D.contDiffOn_physicalCutoffSobolev_top hR0) (D.contDiffOn_physicalCutoffSobolev_four hR0)

end NavierStokes.Nonuniqueness
