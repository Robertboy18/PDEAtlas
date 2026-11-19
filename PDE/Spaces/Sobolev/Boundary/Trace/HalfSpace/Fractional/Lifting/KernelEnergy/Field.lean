/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.Slicing.NormalIntegral.Lebesgue
public import PDE.Analysis.Convolution.FractionalEnergy

/-!
# Signed kernel fields on the upper half-space

The Banach-valued field `t⁻¹ • ∫ y, ψ(y) • g(x - t • y)` uses the tangential-normal
coordinates. Its energy is the height integral of the signed-kernel estimate;
the volume-preserving coordinate map introduces no dimensional factor.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Trace.HalfSpace

variable {n : ℕ}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The signed convolution field, with the inverse-height derivative prefactor. -/
def signedKernelField (ψ : ℝ^n → ℝ) (g : ℝ^n → F) (z : ℝ^(n + 1)) : F :=
  (splitTangentialNormal z).2⁻¹ •
    ∫ y, ψ y • g ((splitTangentialNormal z).1 - (splitTangentialNormal z).2 • y)

/-- The field in tangential-normal coordinates is the signed convolution. -/
@[simp]
theorem signedKernelField_join (ψ : ℝ^n → ℝ) (g : ℝ^n → F) (x : ℝ^n) (t : ℝ) :
    signedKernelField ψ g (joinTangentialNormal (x, t)) =
      t⁻¹ • ∫ y, ψ y • g (x - t • y) := by
  simp only [signedKernelField, split_joinTangentialNormal]

/-- Strongly measurable boundary representatives give a strongly measurable signed field. -/
theorem stronglyMeasurable_signedKernelField {ψ : ℝ^n → ℝ} {g : ℝ^n → F}
    (hψ : Measurable ψ) (hg : StronglyMeasurable g) :
    StronglyMeasurable (signedKernelField ψ g) := by
  have hs : Measurable (splitTangentialNormal (n := n)) := by
    convert (tangentialNormalMeasurableEquiv (n := n)).measurable using 1
    exact (funext tangentialNormalMeasurableEquiv_apply).symm
  have hm : StronglyMeasurable fun v : ℝ^(n + 1) × ℝ^n ↦
      ψ v.2 • g ((splitTangentialNormal v.1).1 -
        (splitTangentialNormal v.1).2 • v.2) :=
    (hψ.comp measurable_snd).stronglyMeasurable.smul
      (hg.comp_measurable (by fun_prop))
  exact hs.snd.inv.stronglyMeasurable.smul hm.integral_prod_right'

/-- Positive-height power energy agrees with the energy on the half-space. -/
theorem lintegral_signedKernelField_rpow_eq {ψ : ℝ^n → ℝ} {g : ℝ^n → F}
    (hψ : Measurable ψ) (hg : StronglyMeasurable g) (p : ℝ) :
    (∫⁻ z in ℝ^(n + 1)₊, ENNReal.ofReal (‖signedKernelField ψ g z‖ ^ p)) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : ℝ^n,
        ENNReal.ofReal (‖t⁻¹ • ∫ y, ψ y • g (x - t • y)‖ ^ p) := by
  rw [← lintegral_joinTangentialNormal_eq_lintegral_upper]
  have hm : Measurable fun q : ℝ^n × ℝ ↦
      ENNReal.ofReal (‖signedKernelField ψ g (joinTangentialNormal q)‖ ^ p) := by
    have hj : Measurable (joinTangentialNormal (n := n)) := by
      convert (tangentialNormalMeasurableEquiv (n := n)).symm.measurable using 1
      exact (funext tangentialNormalMeasurableEquiv_symm_apply).symm
    have hf := (stronglyMeasurable_signedKernelField hψ hg).comp_measurable hj
    exact (hf.norm.measurable.pow_const p).ennreal_ofReal
  rw [lintegral_prod_symm _ hm.aemeasurable]
  simp only [signedKernelField_join, positiveNormalMeasure]

variable [CompleteSpace F]

/-- A support ball and a bound on the kernel give the physical half-space energy estimate. -/
theorem lintegral_signedKernelField_rpow_le {p R M : ℝ} (hp : 1 < p) (hR : 0 < R)
    {ψ : ℝ^n → ℝ} {g : ℝ^n → F} (hψ : Continuous ψ)
    (hψsupport : Function.support ψ ⊆ Metric.ball 0 R)
    (hψbound : ∀ y, |ψ y| ≤ M) (hψzero : ∫ y, ψ y = 0)
    (hg : MemLp g (ENNReal.ofReal p) volume) (hgm : StronglyMeasurable g) :
    (∫⁻ z in ℝ^(n + 1)₊, ENNReal.ofReal (‖signedKernelField ψ g z‖ ^ p)) ≤
      ENNReal.ofReal ((volume.real (Metric.ball (0 : ℝ^n) R)) ^ (p - 1) * M ^ p *
        (R ^ ((n : ℝ) + p - 1) / ((n : ℝ) + p - 1))) *
        ∫⁻ h : ℝ^n, ∫⁻ x : ℝ^n,
          ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1))) *
            ENNReal.ofReal (‖g (x - h) - g x‖ ^ p) := by
  rw [lintegral_signedKernelField_rpow_eq hψ.measurable hgm]
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using
    lintegral_signedKernel_rpow_le volume hp hR hψ hψsupport hψbound hψzero hg

end SobolevSpace.Trace.HalfSpace
