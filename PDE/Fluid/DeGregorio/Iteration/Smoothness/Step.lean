/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Characteristics.Integral
public import PDE.Fluid.DeGregorio.Iteration.Smoothness.Evolution
public import PDE.Fluid.DeGregorio.Iteration.Smoothness.Source
public import PDE.Fluid.DeGregorio.Iteration.Smoothness.Uniqueness

/-!
# One step of the regularity bootstrap

Let `Φ` be a bounded family of H² graphs whose representatives satisfy a characteristic
identity with a bounded measurable H² integrand `V`. If the derivative of the representative of
`V` is `ω H Φ' + λ (H ω) Φ' + f + c Φ'`, with `Φ' = ∂ Φ`, `c = H ω` the stretching coefficient and
`f` a bounded measurable H² forcing, then `Φ'` satisfies the characteristic identity

  `Φ' (X a t) t = Φ' a 0 + ∫₀ᵗ (ω H Φ' + λ (H ω) Φ' + f) (X a s) s ds`

of an affine equation. If `Φ' 0` has an H² graph, that equation has a bounded measurable H²
solution with this initial value, and H¹ uniqueness identifies it with `Φ'`. Thus `Φ'` is itself
a bounded family of H² graphs, and one more spatial derivative of the representatives exists.

## Main results

* `HkCharacteristics.deriv_h2_integral`: the characteristic identity for `∂ Φ`.
* `HkCharacteristics.exists_h2_deriv`: `∂ Φ` is represented by a bounded measurable H² family
  satisfying the characteristic identity of the affine equation.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology Sobolev
open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.ODE (deriv_characteristic_integral)

namespace DeGregorio.Iteration

variable {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} {hT : 0 ≤ T}
  {f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)} {c X Y : ℝ → ℝ → ℝ}

/-- The characteristic identity of a bounded H² family differentiates into one for the first
weak derivatives, with the source `G' - c Φ'`. -/
theorem HkCharacteristics.deriv_h2_integral (hchar : HkCharacteristics hT f c X Y)
    {Φ V : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)} (hV : StronglyMeasurable V) {M : ℝ}
    (hVb : ∀ t, ‖V t‖ ≤ M) {Src : Icc (0 : ℝ) T → W^{1,2}(ℝ^1)}
    (hder : ∀ (t : Icc (0 : ℝ) T) x, realLineRepresentative (∂[0] (V t)) x =
      realLineRepresentative (Src t) x + c x t * realLineRepresentative (∂[0] (Φ t)) x)
    (heq : ∀ a (t : Icc (0 : ℝ) T),
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (Φ t)) (X a t) =
        realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (Φ ⟨0, le_rfl, hT⟩)) a +
          ∫ s in 0..(t : ℝ), realLineRepresentative
            (lowerOrderCLM (by decide : 1 ≤ 2) (V (projIcc 0 T hT s))) (X a s)) :
    ∀ a (t : Icc (0 : ℝ) T),
      realLineRepresentative (∂[0] (Φ t)) (X a t) =
        realLineRepresentative (∂[0] (Φ ⟨0, le_rfl, hT⟩)) a +
          ∫ s in 0..(t : ℝ), realLineRepresentative (Src (projIcc 0 T hT s)) (X a s) := by
  have hmeas (U : Icc (0 : ℝ) T → W^{1,2}(ℝ^1)) (hU : StronglyMeasurable U) :
      Measurable (fun z : ℝ × ℝ ↦ realLineRepresentative (U (projIcc 0 T hT z.2)) z.1) := by
    have h : Measurable (fun z : Icc (0 : ℝ) T × ℝ ↦ realLineRepresentative (U z.1) z.2) :=
      (stronglyMeasurable_realLineRepresentative hU).measurable
    have h2 := h.comp (((continuous_projIcc (h := hT)).measurable.comp measurable_snd).prodMk
      measurable_fst)
    exact h2
  have hbound (U : W^{1,2}(ℝ^1)) (x : ℝ) : |realLineRepresentative U x| ≤ 2 * ‖U‖ :=
    (Real.norm_eq_abs _).symm.trans_le (norm_realLineRepresentative_le U x)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hVb ⟨0, le_rfl, hT⟩)
  have hmain := deriv_characteristic_integral (T := T) (K := 2 * M) (C := 2 * (B : ℝ))
    (X := X) (c := c)
    (φ := fun x t ↦
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (Φ (projIcc 0 T hT t))) x)
    (φ' := fun x t ↦ realLineRepresentative (∂[0] (Φ (projIcc 0 T hT t))) x)
    (G := fun x s ↦
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (V (projIcc 0 T hT s))) x)
    (G' := fun x s ↦ realLineRepresentative (∂[0] (V (projIcc 0 T hT s))) x)
    (φ₀ := realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (Φ ⟨0, le_rfl, hT⟩)))
    (φ₀' := realLineRepresentative (∂[0] (Φ ⟨0, le_rfl, hT⟩)))
    hchar.flow_continuous
    (fun a s hs ↦ hasDerivAt_hkCurve_hilbert_flow_space hT f hchar.velocity_derivative
      hchar.flow_initial hchar.flow_derivative a s hs)
    hchar.coefficient_continuous
    (fun x s ↦ by rw [← Real.norm_eq_abs]; exact hchar.coefficient_bound x s)
    (fun t _ x ↦ hasDerivAt_realLineRepresentative_lowerOrder _ x)
    (fun x ↦ hasDerivAt_realLineRepresentative_lowerOrder _ x)
    (fun s _ x ↦ hasDerivAt_realLineRepresentative_lowerOrder _ x)
    (hmeas (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) (V t))
      ((lowerOrderCLM (by decide : 1 ≤ 2)).continuous.comp_stronglyMeasurable hV))
    (hmeas (fun t ↦ ∂[0] (V t)) ((partialDerivCLM 0).continuous.comp_stronglyMeasurable hV))
    (fun s _ x ↦ (hbound _ x).trans (by
      gcongr; exact (norm_lowerOrderCLM_apply_le _ _).trans (hVb _)))
    (fun s _ x ↦ (hbound _ x).trans (by gcongr; exact (norm_partialDeriv_le 0 _).trans (hVb _)))
    (fun a t ht ↦ by simpa only [projIcc_of_mem hT ht] using heq a ⟨t, ht⟩)
  intro a t
  have h := hmain a t t.property
  simp only [projIcc_of_mem hT t.property] at h
  rw [h]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [hder (projIcc 0 T hT s) (X a s),
    projIcc_of_mem hT ((uIcc_subset_Icc ⟨le_rfl, hT⟩ t.property) hs)]
  ring

/-- One step of the bootstrap. Let `Φ` be a bounded strongly measurable H² family satisfying a
characteristic identity with a bounded strongly measurable integrand `V`, and suppose the
derivative of `V` is `ω H Φ' + λ c Φ' + g + c Φ'`, where `Φ' = ∂ Φ`, `c = H ω` is the stretching
coefficient and `g` a bounded strongly measurable H² forcing. If the initial derivative `Φ' 0`
is represented by an H² graph `Q₀`, then `Φ'` is represented by a bounded strongly measurable H²
family `q`, which satisfies the characteristic identity with integrand
`B (ω, q) + λ B (q, ω) + g`. This is persistence of the initial H² regularity of `Φ'`. -/
theorem HkCharacteristics.exists_h2_deriv (hchar : HkCharacteristics hT f c X Y)
    {W : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)} (hW : StronglyMeasurable W) {K : ℝ} (hK : 0 ≤ K)
    (hWb : ∀ t, ‖W t‖ ≤ K)
    (hc : ∀ (t : Icc (0 : ℝ) T) x, c x t =
      realLineRepresentative (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) (W t))) x)
    {Φ V g : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)} (hΦ : StronglyMeasurable Φ)
    (hΦb : ∀ t, ‖Φ t‖ ≤ K) (hV : StronglyMeasurable V) (hVb : ∀ t, ‖V t‖ ≤ K)
    (hg : StronglyMeasurable g) (hgb : ∀ t, ‖g t‖ ≤ K) (lam : ℝ)
    (hder : ∀ (t : Icc (0 : ℝ) T) x, realLineRepresentative (∂[0] (V t)) x =
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) x *
          realLineRepresentative (realHilbertH1 (∂[0] (Φ t))) x +
        lam * (c x t * realLineRepresentative (∂[0] (Φ t)) x) +
        realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (g t)) x +
        c x t * realLineRepresentative (∂[0] (Φ t)) x)
    (heq : ∀ a (t : Icc (0 : ℝ) T),
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (Φ t)) (X a t) =
        realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (Φ ⟨0, le_rfl, hT⟩)) a +
          ∫ s in 0..(t : ℝ), realLineRepresentative
            (lowerOrderCLM (by decide : 1 ≤ 2) (V (projIcc 0 T hT s))) (X a s))
    (Q₀ : W^{2,2}(ℝ^1))
    (hQ₀ : realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) Q₀) =
      realLineRepresentative (∂[0] (Φ ⟨0, le_rfl, hT⟩))) :
    ∃ q : Icc (0 : ℝ) T → W^{2,2}(ℝ^1), StronglyMeasurable q ∧ (∃ C ≥ 0, ∀ t, ‖q t‖ ≤ C) ∧
      (∀ t, ∂[0] (Φ t) = lowerOrderCLM (by decide : 1 ≤ 2) (q t)) ∧
      ∀ a (t : Icc (0 : ℝ) T),
        realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (q t)) (X a t) =
          realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (q ⟨0, le_rfl, hT⟩)) a +
            ∫ s in 0..(t : ℝ), realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2)
              (firstDerivativeSourceH2CLM (W (projIcc 0 T hT s)) (q (projIcc 0 T hT s)) +
                lam • firstDerivativeSourceH2CLM (q (projIcc 0 T hT s))
                  (W (projIcc 0 T hT s)) + g (projIcc 0 T hT s))) (X a s) := by
  set S := firstDerivativeSourceH2CLM with hSdef
  -- The derivative identity.
  choose Sa hSa hSan using fun t ↦ exists_h1_linearSource (W t) (∂[0] (Φ t)) lam
  let Src (t : Icc (0 : ℝ) T) : W^{1,2}(ℝ^1) :=
    Sa t + lowerOrderCLM (by decide : 1 ≤ 2) (g t)
  have hder' (t : Icc (0 : ℝ) T) (x : ℝ) : realLineRepresentative (∂[0] (V t)) x =
      realLineRepresentative (Src t) x + c x t * realLineRepresentative (∂[0] (Φ t)) x := by
    simp only [Src, realLineRepresentative_add, Pi.add_apply, hSa, hder, ← hc]
  have hE := hchar.deriv_h2_integral hV hVb hder' heq
  -- The affine H² solution.
  let L (t : Icc (0 : ℝ) T) : W^{2,2}(ℝ^1) →L[ℝ] W^{2,2}(ℝ^1) := S (W t) + lam • S.flip (W t)
  have hLapply (t : Icc (0 : ℝ) T) (U : W^{2,2}(ℝ^1)) :
      L t U = S (W t) U + lam • S U (W t) := rfl
  set k := 36 * succOrderAssemblyNormBound 1 1 with hk
  have hk0 : 0 ≤ k := mul_nonneg (by norm_num) succOrderAssemblyNormBound_nonneg
  have hSn (U Q : W^{2,2}(ℝ^1)) : ‖S U Q‖ ≤ k * ‖U‖ * ‖Q‖ :=
    norm_firstDerivativeSourceH2CLM_apply_le U Q
  have hLm (U : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)) (hU : StronglyMeasurable U) :
      StronglyMeasurable (fun t ↦ L t (U t)) := by
    simp only [hLapply]
    exact (S.continuous₂.comp_stronglyMeasurable (hW.prodMk hU)).add
      ((S.continuous₂.comp_stronglyMeasurable (hU.prodMk hW)).const_smul lam)
  have hLn (t : Icc (0 : ℝ) T) (U : W^{2,2}(ℝ^1)) :
      ‖L t U‖ ≤ (k * K + |lam| * (k * K)) * ‖U‖ := by
    rw [hLapply]
    calc
      ‖S (W t) U + lam • S U (W t)‖ ≤ ‖S (W t) U‖ + |lam| * ‖S U (W t)‖ :=
        (norm_add_le _ _).trans_eq (by rw [norm_smul, Real.norm_eq_abs])
      _ ≤ k * K * ‖U‖ + |lam| * (k * ‖U‖ * K) := by
        gcongr
        · exact (hSn _ _).trans (by gcongr; exact hWb t)
        · exact (hSn _ _).trans (by gcongr; exact hWb t)
      _ = _ := by ring
  obtain ⟨q, hq, ⟨C, hC, hqb⟩, hqeq⟩ := hchar.exists_h2_affine_evolution L hLm
    (by positivity) hLn g hg hgb Q₀
  -- Uniqueness in H¹ identifies the derivative.
  let r (t : Icc (0 : ℝ) T) : W^{1,2}(ℝ^1) :=
    ∂[0] (Φ t) - lowerOrderCLM (by decide : 1 ≤ 2) (q t)
  have hrm : StronglyMeasurable r :=
    ((partialDerivCLM 0).continuous.comp_stronglyMeasurable hΦ).sub
      ((lowerOrderCLM (by decide : 1 ≤ 2)).continuous.comp_stronglyMeasurable hq)
  choose Sr hSr hSrn using fun t ↦ exists_h1_linearSource (W t) (r t) lam
  have hSrm : StronglyMeasurable Sr := stronglyMeasurable_h1_linearSource hW hrm hSr
  have hSam : StronglyMeasurable Sa := stronglyMeasurable_h1_linearSource hW
    ((partialDerivCLM 0).continuous.comp_stronglyMeasurable hΦ) hSa
  have hSrcm : StronglyMeasurable Src :=
    hSam.add ((lowerOrderCLM (by decide : 1 ≤ 2)).continuous.comp_stronglyMeasurable hg)
  have hSrcb (t : Icc (0 : ℝ) T) : ‖Src t‖ ≤ (12 + 12 * |lam|) * K * K + K := by
    apply (norm_add_le _ _).trans
    gcongr
    · apply (hSan t).trans
      gcongr
      · exact hWb t
      · exact (norm_partialDeriv_le 0 _).trans (hΦb t)
    · exact (norm_lowerOrderCLM_apply_le _ _).trans (hgb t)
  let Lq (t : Icc (0 : ℝ) T) : W^{1,2}(ℝ^1) :=
    lowerOrderCLM (by decide : 1 ≤ 2) (L t (q t) + g t)
  have hLqm : StronglyMeasurable Lq :=
    (lowerOrderCLM (by decide : 1 ≤ 2)).continuous.comp_stronglyMeasurable ((hLm q hq).add hg)
  have hLqb (t : Icc (0 : ℝ) T) : ‖Lq t‖ ≤ (k * K + |lam| * (k * K)) * C + K := by
    apply (norm_lowerOrderCLM_apply_le _ _).trans
    apply (norm_add_le _ _).trans
    gcongr
    · exact (hLn t _).trans (by gcongr; exact hqb t)
    · exact hgb t
  have hrb : ∃ D ≥ 0, ∀ t, ‖r t‖ ≤ D := ⟨K + C, by positivity, fun t ↦ by
    apply (norm_sub_le _ _).trans
    gcongr
    · exact (norm_partialDeriv_le 0 _).trans (hΦb t)
    · exact (norm_lowerOrderCLM_apply_le _ _).trans (hqb t)⟩
  have hSrbound (t : Icc (0 : ℝ) T) : ‖Sr t‖ ≤ ((12 + 12 * |lam|) * K) * ‖r t‖ :=
    (hSrn t).trans (by gcongr; exact hWb t)
  have hreq (a : ℝ) (t : Icc (0 : ℝ) T) : realLineRepresentative (r t) (X a t) =
      ∫ s in 0..(t : ℝ), realLineRepresentative (Sr (projIcc 0 T hT s)) (X a s) := by
    have hi1 := intervalIntegrable_h1_along_flow (hT := hT) hchar.flow_continuous hSrcm hSrcb a t
    have hi2 := intervalIntegrable_h1_along_flow (hT := hT) hchar.flow_continuous hLqm hLqb a t
    simp only [r, realLineRepresentative_sub, Pi.sub_apply]
    rw [hE a t, hqeq a t, hQ₀, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub hi1 hi2]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [Src, Lq, r, hLapply, realLineRepresentative_add, realLineRepresentative_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, hSa, hSr, map_add, map_smul, hSdef,
      realLineRepresentative_firstDerivativeSourceH2CLM, realHilbertH1_sub,
      realLineRepresentative_sub, Pi.sub_apply]
    ring
  have hr0 := hchar.eq_zero_of_h1_integral hSrm hrb (by positivity) hSrbound hreq
  have hid (t : Icc (0 : ℝ) T) : ∂[0] (Φ t) = lowerOrderCLM (by decide : 1 ≤ 2) (q t) :=
    sub_eq_zero.mp (hr0 t)
  refine ⟨q, hq, ⟨C, hC, hqb⟩, hid, fun a t ↦ ?_⟩
  rw [hqeq a t, hQ₀, hid]
  rfl

end DeGregorio.Iteration
