/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.VectorValued.Localization
import PDE.FDeriv.Calculus

/-!
# Banach-valued bilinear weak Leibniz rule

For a continuous bilinear map between arbitrary complete real Banach spaces, the weak
product rule holds at every Hölder triple of exponents in `[1, ∞]`.

At an infinity endpoint, first keep that input fixed and take a smooth representative
for the other input. Both functions and their derivatives are locally square-integrable,
so the finite-exponent theorem gives the identity locally. Smooth density in the finite
input then passes to the desired product. When both inputs are essentially bounded,
local square-integrability applies directly. The argument never uses density in the infinity norm.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {Ω : Opens ℝ^n} {F G H : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

private theorem top_coordinate_memLp_two (U : W^{1,∞}(Ω; F)) {O : Opens ℝ^n}
    (hc : IsCompact (closure (O : Set ℝ^n))) (ho : closure (O : Set ℝ^n) ⊆ Ω)
    (a : DerivIndex n 1) : MemLp (U.val a) 2 (domainMeasure n O) := by
  let : IsFiniteMeasure (domainMeasure n O) :=
    isFiniteMeasure_domainMeasure_of_isBounded (hc.isBounded.subset subset_closure)
  exact ((Lp.memLp (U.val a)).mono_measure
    (Measure.restrict_mono (subset_closure.trans ho) le_rfl)).mono_exponent le_top

omit [CompleteSpace F] [NormedSpace ℝ F] in
private theorem continuousOn_memLp_two {f : ℝ^n → F}
    (hf : ContinuousOn f Ω) {O : Opens ℝ^n}
    (hc : IsCompact (closure (O : Set ℝ^n))) (ho : closure (O : Set ℝ^n) ⊆ Ω) :
    MemLp f 2 (domainMeasure n O) := by
  let : IsFiniteMeasure (domainMeasure n O) :=
    isFiniteMeasure_domainMeasure_of_isBounded (hc.isBounded.subset subset_closure)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (hf.mono ho)
  have hint : IntegrableOn f (O : Set ℝ^n) volume :=
    ((hf.mono ho).integrableOn_compact hc).mono_set subset_closure
  apply MemLp.of_bound hint.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem O.isOpen.measurableSet] with x hx
  exact hC x (subset_closure hx)

private theorem smooth_coordinate_memLp_two {p : ℝ≥0∞} (U : W^{1,p}(Ω; F))
    {f : ℝ^n → F} (hf : ContDiffOn ℝ 1 f Ω)
    (hbase : (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[domainMeasure n Ω] f)
    {O : Opens ℝ^n} (hc : IsCompact (closure (O : Set ℝ^n)))
    (ho : closure (O : Set ℝ^n) ⊆ Ω) (a : DerivIndex n 1) :
    MemLp (U.val a) 2 (domainMeasure n O) := by
  have hμ : domainMeasure n O ≤ domainMeasure n Ω :=
    Measure.restrict_mono (subset_closure.trans ho) le_rfl
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · exact (memLp_congr_ae (hbase.filter_mono (ae_mono hμ))).mpr
      (continuousOn_memLp_two hf.continuousOn hc ho)
  · have hd : ContinuousOn (∂[i] f) Ω := fun x hx ↦
      (PDE.contDiffAt_partialDeriv 0
        (hf.contDiffAt (Ω.isOpen.mem_nhds hx)) i).continuousAt.continuousWithinAt
    exact (memLp_congr_ae
      ((coordinate_ae_partialDeriv_of_contDiffOn U hf hbase i).filter_mono
        (ae_mono hμ))).mpr (continuousOn_memLp_two hd hc ho)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem weak_bilinear_smooth_top
    (B : F →L[ℝ] G →L[ℝ] H) (U : W^{1,p}(Ω; F)) (V : W^{1,∞}(Ω; G))
    {f : ℝ^n → F} (hf : ContDiffOn ℝ 1 f Ω)
    (hbase : (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[domainMeasure n Ω] f)
    (i : Fin n) :
    HasWeakDerivativeOn Ω [i]
      (fun x ↦ B (U.val (baseIndex n 1) x) (V.val (baseIndex n 1) x))
      (fun x ↦ B (U.val (singleDerivIndex n i) x) (V.val (baseIndex n 1) x) +
        B (U.val (baseIndex n 1) x) (V.val (singleDerivIndex n i) x)) :=
  hasWeakDerivativeOn_bilinear_of_locally_memLp_two (r := p) B U V
    (fun _ hc ho ↦ smooth_coordinate_memLp_two U hf hbase hc ho)
    (fun _ hc ho ↦ top_coordinate_memLp_two V hc ho) i

/-- A `W^{1,∞}` input acts by any continuous bilinear map on `W^{1,p}` for every
`1 ≤ p ≤ ∞`. This includes the `L¹` endpoint without norm approximation at infinity. -/
theorem hasWeakDerivativeOn_bilinear_top_right
    (B : F →L[ℝ] G →L[ℝ] H) (U : W^{1,p}(Ω; F)) (V : W^{1,∞}(Ω; G))
    (i : Fin n) :
    HasWeakDerivativeOn Ω [i]
      (fun x ↦ B (U.val (baseIndex n 1) x) (V.val (baseIndex n 1) x))
      (fun x ↦ B (U.val (singleDerivIndex n i) x) (V.val (baseIndex n 1) x) +
        B (U.val (baseIndex n 1) x) (V.val (singleDerivIndex n i) x)) := by
  by_cases hp : p = ∞
  · subst p
    exact hasWeakDerivativeOn_bilinear_of_locally_memLp_two (r := ∞) B U V
      (fun _ hc ho ↦ top_coordinate_memLp_two U hc ho)
      (fun _ hc ho ↦ top_coordinate_memLp_two V hc ho) i
  · obtain ⟨Us, f, hf, hbase, hlim⟩ := meyers_serrin hp U
    have ht : Tendsto Us atTop (𝓝 U) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      simpa only [dist_eq_norm] using hlim
    exact hasWeakDerivativeOn_bilinear_of_tendsto (r := p) B ht tendsto_const_nhds i
      (fun j ↦ weak_bilinear_smooth_top B (Us j) V
        ((hf j).of_le (by simp)) (hbase j) i)

variable {q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)] [ENNReal.HolderTriple p q r]

include r in
/-- Weak Leibniz rule for a continuous bilinear map between complete real Banach spaces.
The exponents satisfy `1/r = 1/p + 1/q`, with all three in `[1, ∞]`. -/
theorem hasWeakDerivativeOn_bilinear
    (B : F →L[ℝ] G →L[ℝ] H) (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G))
    (i : Fin n) :
    HasWeakDerivativeOn Ω [i]
      (fun x ↦ B (U.val (baseIndex n 1) x) (V.val (baseIndex n 1) x))
      (fun x ↦ B (U.val (singleDerivIndex n i) x) (V.val (baseIndex n 1) x) +
        B (U.val (baseIndex n 1) x) (V.val (singleDerivIndex n i) x)) := by
  by_cases hq : q = ∞
  · subst q
    exact hasWeakDerivativeOn_bilinear_top_right B U V i
  by_cases hp : p = ∞
  · subst p
    simpa only [ContinuousLinearMap.flip_apply, add_comm] using
      hasWeakDerivativeOn_bilinear_top_right B.flip V U i
  exact hasWeakDerivativeOn_bilinear_finite (r := r) B hp hq U V i

end SobolevSpace.VectorValued
