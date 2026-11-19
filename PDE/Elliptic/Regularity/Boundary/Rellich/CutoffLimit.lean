/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Rellich.CutoffFlux
public import PDE.Analysis.MeasureTheory.Integral.CollarEstimate

/-!
# The limit of the weak collar flux

The vanishing terms are controlled by a single integrable Green density. The
height is positive on the part of the domain meeting the test support and is
zero on its boundary. Both facts are consequences of a C¹ graph chart.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped Sobolev Gradient Topology

namespace SobolevSpace.GraphSpace.Rellich

open Approximation.UpToBoundary

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
  [H : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The transversal volume flux converges to the outward weak Green pairing.
Only the state and its weak Laplacian are Sobolev/L² data. -/
theorem tendsto_collar_flux
    (P : InwardPartition Ω) (z : H¹(Ω)) (f : DerivLp (m + 1) 2 Ω)
    (hweak : ∀ v : TestFunctionOn (m + 1) Ω,
      (∫ x, baseRepresentative z x * PDE.laplacian v.1.toFun x
        ∂domainMeasure (m + 1) Ω) =
      ∫ x, (f : ℝ^(m + 1) → ℝ) x * v.1.toFun x ∂domainMeasure (m + 1) Ω)
    {φ d : ℝ^(m + 1) → ℝ} {χ : ℝ → ℝ} {C : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hd : ContDiff ℝ 1 d) (hχ : ContDiff ℝ 1 χ)
    (hχ0 : χ 0 = 1) (hbound : ∀ s, ‖χ s‖ ≤ C)
    (hzero : ∀ s, 1 ≤ s → χ s = 0)
    (hboundary : ∀ x ∈ frontier Ω, φ x ≠ 0 → d x = 0)
    (hpos : ∀ x ∈ Ω, x ∈ tsupport φ → 0 < d x) :
    Tendsto (fun t : ℝ ↦ t⁻¹ *
      ∫ x, φ x * deriv χ (d x / t) *
        inner ℝ ((wkpGradientCLM z : ℝ^(m + 1) → ℝ^(m + 1)) x) (∇ d x)
          ∂domainMeasure (m + 1) Ω)
      (𝓝[>] 0)
      (𝓝 ((∫ x, (f : ℝ^(m + 1) → ℝ) x * φ x ∂domainMeasure (m + 1) Ω) +
        ∫ x, inner ℝ ((wkpGradientCLM z : ℝ^(m + 1) → ℝ^(m + 1)) x) (∇ φ x)
          ∂domainMeasure (m + 1) Ω)) := by
  let Z : ℝ^(m + 1) → ℝ^(m + 1) := wkpGradientCLM z
  have hZ : MemLp Z 2 (domainMeasure (m + 1) Ω) := Lp.memLp _
  have hgrad {g : ℝ^(m + 1) → ℝ} (hg : ContDiff ℝ 1 g) : Continuous (∇ g) :=
    (InnerProductSpace.toDual ℝ (ℝ^(m + 1))).symm.continuous.comp
      (hg.continuous_fderiv one_ne_zero)
  have hmem {E : Type} [NormedAddCommGroup E] {g : ℝ^(m + 1) → E} (hg : Continuous g) :
      MemLp g 2 (domainMeasure (m + 1) Ω) := hg.continuousOn.memLp_of_subset_isCompact
    H.bounded.isCompact_closure H.isOpen.measurableSet subset_closure
  have hfφ : Integrable (fun x ↦ (f : ℝ^(m + 1) → ℝ) x * φ x)
      (domainMeasure (m + 1) Ω) := (Lp.memLp f).integrable_mul (hmem hφ.continuous)
  have hgφ : Integrable (fun x ↦ inner ℝ (Z x) (∇ φ x))
      (domainMeasure (m + 1) Ω) := integrable_inner_of_memLp_two hZ (hmem (hgrad hφ))
  let F : ℝ^(m + 1) → ℝ := fun x ↦ (f : ℝ^(m + 1) → ℝ) x * φ x +
    inner ℝ (Z x) (∇ φ x)
  have hF : Integrable F (domainMeasure (m + 1) Ω) := hfφ.add hgφ
  have hFpos : ∀ᵐ x ∂domainMeasure (m + 1) Ω, F x ≠ 0 → 0 < d x := by
    filter_upwards [ae_restrict_mem H.isOpen.measurableSet] with x hx hFx
    apply hpos x hx
    by_contra hs
    have hval : φ x = 0 := image_eq_zero_of_notMem_tsupport hs
    have hgrad : ∇ φ x = 0 := by
      simp only [gradient, fderiv_of_notMem_tsupport ℝ hs, map_zero]
    exact hFx (by simp only [F, hval, hgrad, mul_zero, inner_zero_right, add_zero])
  have hvanish := tendsto_integral_collar_cutoff_mul_zero hd.continuous.measurable hF
    hχ.continuous hbound hzero hFpos
  have heq (t : ℝ) : t⁻¹ *
      ∫ x, φ x * deriv χ (d x / t) * inner ℝ (Z x) (∇ d x)
        ∂domainMeasure (m + 1) Ω =
      (∫ x, F x ∂domainMeasure (m + 1) Ω) -
        ∫ x, χ (d x / t) * F x ∂domainMeasure (m + 1) Ω := by
    obtain ⟨v, hv₀, hv₁⟩ := exists_H10_collarComplement P hφ hd hχ hχ0 hboundary t
    have hw := integral_greenPairing_eq_zero_of_H10 z f hweak v hv₀ hv₁
    let W : ℝ^(m + 1) → ℝ^(m + 1) := fun x ↦
      (φ x * deriv χ (d x / t)) • ∇ d x
    have hmW : MemLp W 2 (domainMeasure (m + 1) Ω) := hmem ((hφ.continuous.mul
      ((hχ.continuous_deriv_one).comp (hd.continuous.div_const t))).smul (hgrad hd))
    have hcross : Integrable (fun x ↦ φ x * deriv χ (d x / t) *
        inner ℝ (Z x) (∇ d x)) (domainMeasure (m + 1) Ω) := by
      simpa only [W, inner_smul_right, RCLike.conj_to_real] using
        integrable_inner_of_memLp_two hZ hmW
    have hχF : Integrable (fun x ↦ χ (d x / t) * F x)
        (domainMeasure (m + 1) Ω) :=
      hF.bdd_mul (hχ.continuous.comp (hd.continuous.div_const t)).aestronglyMeasurable
        (ae_of_all _ fun x ↦ hbound (d x / t))
    have hbaseInt : Integrable (fun x ↦ (f : ℝ^(m + 1) → ℝ) x *
        (φ x * (1 - χ (d x / t)))) (domainMeasure (m + 1) Ω) :=
      (Lp.memLp f).integrable_mul (hmem (hφ.continuous.mul (continuous_const.sub
        (hχ.continuous.comp (hd.continuous.div_const t)))))
    have hgradInt : Integrable (fun x ↦ inner ℝ (Z x)
        (∇ (fun y ↦ φ y * (1 - χ (d y / t))) x)) (domainMeasure (m + 1) Ω) :=
      (L2.integrable_inner (𝕜 := ℝ) (wkpGradientCLM z)
        (wkpGradientCLM (v : H¹(Ω)))).congr (hv₁.mono fun x hx ↦ congrArg (inner ℝ (Z x)) hx)
    rw [← integral_add hbaseInt hgradInt] at hw
    have hpoint (x : ℝ^(m + 1)) :
        (f : ℝ^(m + 1) → ℝ) x * (φ x * (1 - χ (d x / t))) +
          inner ℝ (Z x) (∇ (fun y ↦ φ y * (1 - χ (d y / t))) x) =
        F x - χ (d x / t) * F x -
          t⁻¹ * (φ x * deriv χ (d x / t) * inner ℝ (Z x) (∇ d x)) := by
      rw [gradient_collarComplement (hφ.differentiable one_ne_zero x)
        (hd.differentiable one_ne_zero x) t (hχ.differentiable one_ne_zero _),
        inner_sub_right, inner_smul_right, inner_smul_right]
      simp only [F]
      ring
    simp_rw [hpoint] at hw
    have hsub : Integrable (fun x ↦ F x - χ (d x / t) * F x) (domainMeasure (m + 1) Ω) :=
      hF.sub hχF
    rw [integral_sub hsub (hcross.const_mul t⁻¹),
      integral_sub hF hχF, integral_const_mul] at hw
    linarith
  rw [← integral_add hfφ hgφ]
  simpa only [sub_zero] using
    (tendsto_const_nhds.sub hvanish).congr' (Eventually.of_forall fun t ↦ (heq t).symm)

end SobolevSpace.GraphSpace.Rellich
