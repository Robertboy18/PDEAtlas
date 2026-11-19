/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Derivative.FirstOrder
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.WeightedEnergy

/-!
# H¹ uniqueness for linear equations along the characteristics

A bounded H¹ family `q` with

  `q (X a t) t = ∫₀ᵗ S s (X a s) ds`,

where the source `S` is strongly measurable with `‖S s‖ ≤ K ‖q s‖`, vanishes
identically. In characteristic coordinates this is an integral equation in H¹ with a homogeneous
norm estimate, and Grönwall's inequality applies because composition with the forward and inverse
characteristics is bounded on H¹.

The linear part of the source of the `k`-th derivative equation of the De Gregorio model is
`ω H q + λ (H ω) q` for an H² vorticity `ω`; the forcing `F_k` is the rest.
`exists_h1_linearSource` constructs the linear part in H¹ with the bound
`(12 + 12 |λ|) ‖ω‖ ‖q‖`, together with its continuous representative.

## Main results

* `HkCharacteristics.eq_zero_of_h1_integral`: uniqueness for the homogeneous equation.
* `exists_h1_linearSource`: the linear part `ω H q + λ (H ω) q` of the source, in H¹.
* `stronglyMeasurable_h1_linearSource`: measurability of the sources of a measurable family.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Sobolev
open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- A bounded H¹ family whose values along the characteristics are the time integrals of a
strongly measurable source bounded by a multiple of the family vanishes. -/
theorem HkCharacteristics.eq_zero_of_h1_integral
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} {hT : 0 ≤ T}
    {f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)}
    {c X Y : ℝ → ℝ → ℝ} (hchar : HkCharacteristics hT f c X Y)
    {q S : Icc (0 : ℝ) T → W^{1,2}(ℝ^1)} (hS : StronglyMeasurable S)
    (hqbound : ∃ D ≥ 0, ∀ t, ‖q t‖ ≤ D) {K : ℝ} (hK : 0 ≤ K)
    (hSnorm : ∀ t, ‖S t‖ ≤ K * ‖q t‖)
    (heq : ∀ a (t : Icc (0 : ℝ) T),
      realLineRepresentative (q t) (X a t) =
        ∫ s in 0..(t : ℝ), realLineRepresentative (S (projIcc 0 T hT s)) (X a s)) :
    ∀ t, q t = 0 := by
  obtain ⟨P, Q, hP, hQ, C, hC, hnorm⟩ := hchar.exists_h1_pullbacks
  have hXm : Measurable (Function.uncurry (fun (t : Icc (0 : ℝ) T) x ↦ X x t)) := by
    convert (hchar.flow_continuous.comp continuous_swap).measurable using 1
    rfl
  let G (t : Icc (0 : ℝ) T) := P t (q t)
  let H (t : Icc (0 : ℝ) T) := P t (S t)
  have hHm : StronglyMeasurable H :=
    stronglyMeasurable_h1_pullback hXm (fun t ↦ hP t (S t)) hS
  have hHbound (t : Icc (0 : ℝ) T) : ‖H t‖ ≤ C * (K * ‖q t‖) :=
    (hnorm t (S t)).1.trans (mul_le_mul_of_nonneg_left (hSnorm t) hC)
  obtain ⟨D, hD, hqnorm⟩ := hqbound
  let Hext (s : ℝ) := H (projIcc 0 T hT s)
  have hHint : IntegrableOn Hext (Icc (0 : ℝ) T) volume := by
    apply (integrableOn_const (C := C * (K * D))
      (hs := measure_Icc_lt_top.ne)).mono'
      ((hHm.comp_measurable continuous_projIcc.measurable).aestronglyMeasurable.restrict)
    filter_upwards with s
    exact (hHbound _).trans (by gcongr; exact hqnorm _)
  have hInt (t : Icc (0 : ℝ) T) : IntervalIntegrable Hext volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le t.property.1).mpr
      (hHint.mono_set (Icc_subset_Icc_right t.property.2))
  have hGint (t : Icc (0 : ℝ) T) : G t = ∫ s in 0..(t : ℝ), Hext s := by
    apply realLineRepresentative_injective
    funext a
    change realLineRepresentative (P t (q t)) a = _
    rw [hP]
    change realLineRepresentative (q t) (X a t) = _
    rw [heq]
    have hEval := (realLineRepresentativeEvalCLM a).intervalIntegral_comp_comm (hInt t)
    change _ = realLineRepresentativeEvalCLM a (∫ s in 0..(t : ℝ), Hext s)
    rw [← hEval]
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) T := (uIcc_subset_Icc ⟨le_rfl, hT⟩ t.property) hs
    simp only [Hext, H, projIcc_of_mem hT hsI]
    change _ = realLineRepresentative (P ⟨s, hsI⟩ (S ⟨s, hsI⟩)) a
    rw [hP]
  have hqG (t : Icc (0 : ℝ) T) : ‖q t‖ ≤ C * ‖G t‖ := by
    have hid : Q t (G t) = q t := by
      apply realLineRepresentative_injective
      funext x
      rw [hQ]
      change realLineRepresentative (P t (q t)) (Y x t) = _
      rw [hP]
      change realLineRepresentative (q t) (X (Y x t) t) = _
      rw [hchar.flow_inverse x t t.property]
    rw [← hid]
    exact (hnorm t (G t)).2
  let K' := C * K * C
  have hHG (t : Icc (0 : ℝ) T) : ‖H t‖ ≤ K' * ‖G t‖ :=
    (hHbound t).trans (by
      calc
        _ ≤ C * (K * (C * ‖G t‖)) := by gcongr; exact hqG t
        _ = _ := by dsimp only [K']; ring)
  have hGzero : ∀ t, G t = 0 := by
    have hzero := eq_zero_on_of_eq_intervalIntegral_of_norm_le hT
      (hInt ⟨T, hT, le_rfl⟩)
      (u := fun s ↦ G (projIcc 0 T hT s))
      (K := K')
      (fun t ht ↦ by simpa only [projIcc_of_mem hT ht] using hGint ⟨t, ht⟩)
      (fun t ht ↦ by
        simpa only [Hext, projIcc_of_mem hT ht] using hHG ⟨t, ht⟩)
    intro t
    simpa only [projIcc_of_mem hT t.property] using hzero t t.property
  intro t
  apply norm_le_zero_iff.mp
  simpa only [hGzero t, norm_zero, mul_zero] using hqG t

/-- The linear part `ω H q + λ (H ω) q` of the source of the higher derivative equations, in
H¹, for an H² vorticity `W` and an H¹ unknown `Q`. Its continuous representative is the pointwise
expression and its norm is at most `(12 + 12 |λ|) ‖W‖ ‖Q‖`. -/
theorem exists_h1_linearSource (W : W^{2,2}(ℝ^1)) (Q : W^{1,2}(ℝ^1)) (lam : ℝ) :
    ∃ S : W^{1,2}(ℝ^1),
      realLineRepresentative S =
        (fun x ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W) x *
            realLineRepresentative (realHilbertH1 Q) x +
          lam * (realLineRepresentative
            (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) W)) x *
            realLineRepresentative Q x)) ∧
      ‖S‖ ≤ (12 + 12 * |lam|) * ‖W‖ * ‖Q‖ := by
  obtain ⟨S₁, hS₁, hS₁n⟩ := exists_h1_firstDerivativeSource W Q
  let m := realLineRepresentative (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) W))
  let m' := realLineRepresentative (realHilbertH1 (∂[0] W))
  have hm : Continuous m := continuous_realLineRepresentative _
  have hm' : Continuous m' := continuous_realLineRepresentative _
  have hpair : IsHilbertPair (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W)) m := by
    have h := isHilbertPair_realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) W)
    rwa [realLineCoordinateCLM_base_lowerOrder] at h
  have hderiv (x : ℝ) : HasDerivAt m (m' x) x :=
    hasDerivAt_hilbert_coefficient_of_h2 W hm hpair x
  have hmb (x : ℝ) : ‖m x‖ ≤ 4 * ‖W‖ := by
    apply (norm_realLineRepresentative_le _ x).trans
    have := (norm_realHilbertH1_le (lowerOrderCLM (by decide : 1 ≤ 2) W)).trans
      (mul_le_mul_of_nonneg_left (norm_lowerOrderCLM_apply_le _ W) (by norm_num))
    linarith
  have hm'b (x : ℝ) : ‖m' x‖ ≤ 4 * ‖W‖ := by
    apply (norm_realLineRepresentative_le _ x).trans
    have := (norm_realHilbertH1_le (∂[0] W)).trans
      (mul_le_mul_of_nonneg_left (norm_partialDeriv_le 0 W) (by norm_num))
    linarith
  obtain ⟨S₂, hS₂n, hS₂, -⟩ := exists_h1_mul_of_bounded_c1 Q hm hm' hderiv hmb hm'b
  refine ⟨S₁ + lam • S₂, ?_, ?_⟩
  · rw [realLineRepresentative_add, realLineRepresentative_smul, hS₁, hS₂]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, m]
    ring
  · have hb := norm_realLineCoordinateCLM_le (baseIndex 1 1) Q
    have hd := norm_realLineCoordinateCLM_le (singleDerivIndex 1 0) Q
    have hW := norm_nonneg W
    have hQ := norm_nonneg Q
    have hS₂' : ‖S₂‖ ≤ 12 * ‖W‖ * ‖Q‖ := by
      apply hS₂n.trans
      nlinarith
    calc
      ‖S₁ + lam • S₂‖ ≤ ‖S₁‖ + |lam| * ‖S₂‖ := by
        apply (norm_add_le _ _).trans
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 12 * ‖W‖ * ‖Q‖ + |lam| * (12 * ‖W‖ * ‖Q‖) := by
        gcongr
      _ = _ := by ring

/-- Sources chosen with the representatives of `exists_h1_linearSource` for measurable
families of vorticities and unknowns are strongly measurable. -/
theorem stronglyMeasurable_h1_linearSource
    {T : Type*} [MeasurableSpace T] {lam : ℝ}
    {W : T → W^{2,2}(ℝ^1)} {Q S : T → W^{1,2}(ℝ^1)}
    (hW : StronglyMeasurable W) (hQ : StronglyMeasurable Q)
    (hS : ∀ t, realLineRepresentative (S t) =
      fun x ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) x *
          realLineRepresentative (realHilbertH1 (Q t)) x +
        lam * (realLineRepresentative
          (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) (W t))) x *
          realLineRepresentative (Q t) x)) :
    StronglyMeasurable S := by
  have hm : StronglyMeasurable (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) (W t)) :=
    (lowerOrderCLM (by decide : 1 ≤ 2)).continuous.comp_stronglyMeasurable hW
  have hh : StronglyMeasurable (fun t ↦ realHilbertH1 (Q t)) :=
    continuous_realHilbertH1.comp_stronglyMeasurable hQ
  have hc : StronglyMeasurable (fun t ↦ realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) (W t))) :=
    continuous_realHilbertH1.comp_stronglyMeasurable hm
  have h2 := ((stronglyMeasurable_realLineRepresentative hc).mul
      (stronglyMeasurable_realLineRepresentative hQ)).const_mul lam
  have hrep := ((stronglyMeasurable_realLineRepresentative hm).mul
    (stronglyMeasurable_realLineRepresentative hh)).add h2
  apply stronglyMeasurable_hk_of_joint_representative S
    (v := fun t x ↦
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) x *
          realLineRepresentative (realHilbertH1 (Q t)) x +
        lam * (realLineRepresentative
          (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) (W t))) x *
          realLineRepresentative (Q t) x)) hrep
  intro t
  exact (realLineCoordinate_ae_representative (S t)).trans
    (Filter.EventuallyEq.of_eq (hS t))

end DeGregorio.Iteration
