/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.LpBound
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.Linearity

/-!
# The mollified extension on Lebesgue spaces

The cutoff makes the extension bounded from boundary `Lᵖ` into interior `Lᵖ`.
Its norm is at most `2^(1/p)`: mollification contracts each slice, and the
cutoff occupies at most two units of height. Fractional regularity is needed
only for the derivatives, not for this function estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.Trace.HalfSpace

open SobolevSpace.Approximation

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private def extensionLp (μ : Mollifier n) (hp : p ≠ ∞)
    (g : Lp F p (volume : Measure ℝ^n)) :
    Lp F p (volume.restrict ℝ^(n + 1)₊) :=
  (memLp_mollifiedExtension μ hp (Lp.memLp g)).toLp (mollifiedExtension μ g)

private theorem extensionLp_apply_ae (μ : Mollifier n) (hp : p ≠ ∞)
    (g : Lp F p (volume : Measure ℝ^n)) :
    (extensionLp μ hp g : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] mollifiedExtension μ g :=
  MemLp.coeFn_toLp _

private theorem extensionLp_add (μ : Mollifier n) (hp : p ≠ ∞)
    (g h : Lp F p (volume : Measure ℝ^n)) :
    extensionLp μ hp (g + h) = extensionLp μ hp g + extensionLp μ hp h := by
    have hraw : mollifiedExtension μ (g + h : Lp F p volume) =
        mollifiedExtension μ g + mollifiedExtension μ h :=
      (mollifiedExtension_congr_ae μ (Lp.coeFn_add g h)).trans
        (mollifiedExtension_add μ ((Lp.memLp g).locallyIntegrable (Fact.out : 1 ≤ p))
          ((Lp.memLp h).locallyIntegrable (Fact.out : 1 ≤ p)))
    apply Lp.ext
    filter_upwards [extensionLp_apply_ae μ hp (g + h), extensionLp_apply_ae μ hp g,
      extensionLp_apply_ae μ hp h, Lp.coeFn_add (extensionLp μ hp g) (extensionLp μ hp h)]
      with z hsum hg hh hout
    exact hsum.trans ((congrFun hraw z).trans ((congrArg₂ (· + ·) hg.symm hh.symm).trans
      hout.symm))
private theorem extensionLp_smul (μ : Mollifier n) (hp : p ≠ ∞)
    (c : ℝ) (g : Lp F p (volume : Measure ℝ^n)) :
    extensionLp μ hp (c • g) = c • extensionLp μ hp g := by
    have hraw : mollifiedExtension μ (c • g : Lp F p volume) =
        c • mollifiedExtension μ g :=
      (mollifiedExtension_congr_ae μ (Lp.coeFn_smul c g)).trans
        (mollifiedExtension_smul μ c g)
    apply Lp.ext
    filter_upwards [extensionLp_apply_ae μ hp (c • g), extensionLp_apply_ae μ hp g,
      Lp.coeFn_smul c (extensionLp μ hp g)] with z hsmul hg hout
    exact hsmul.trans ((congrFun hraw z).trans ((congrArg (c • ·) hg.symm).trans hout.symm))

private theorem norm_extensionLp_le (μ : Mollifier n) (hp : p ≠ ∞)
    (g : Lp F p (volume : Measure ℝ^n)) :
    ‖extensionLp μ hp g‖ ≤ (2 : ℝ) ^ (1 / p.toReal) * ‖g‖ := by
  have hbound := eLpNorm_mollifiedExtension_le μ hp (Lp.memLp g)
  have hfinite : (2 : ℝ≥0∞) ^ (1 / p.toReal) * eLpNorm g p volume ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr ENNReal.toReal_nonneg)
        (by norm_num))
      (Lp.memLp g).eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono hfinite hbound
  change ‖(memLp_mollifiedExtension μ hp (Lp.memLp g)).toLp (mollifiedExtension μ g)‖ ≤ _
  rw [Lp.norm_toLp]
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofNat, Lp.norm_def] using hreal

/-- Cutoff mollification extends boundary `Lᵖ` data to interior `Lᵖ` data.
The map is bounded for every finite exponent `p ≥ 1`. -/
def mollifiedExtensionLp (μ : Mollifier n) (hp : p ≠ ∞) :
    Lp F p (volume : Measure ℝ^n) →L[ℝ] Lp F p (volume.restrict ℝ^(n + 1)₊) :=
  LinearMap.mkContinuous
    { toFun := fun g ↦
        (memLp_mollifiedExtension μ hp (Lp.memLp g)).toLp (mollifiedExtension μ g)
      map_add' := by exact extensionLp_add μ hp
      map_smul' := by exact extensionLp_smul μ hp }
    ((2 : ℝ) ^ (1 / p.toReal)) (by exact norm_extensionLp_le μ hp)

/-- The bounded map is represented by the original cutoff and convolution formula. -/
theorem mollifiedExtensionLp_apply_ae (μ : Mollifier n) (hp : p ≠ ∞)
    (g : Lp F p (volume : Measure ℝ^n)) :
    (mollifiedExtensionLp μ hp g : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] mollifiedExtension μ g :=
  extensionLp_apply_ae μ hp g

/-- The interior norm costs at most the `p`-th root of the cutoff's height. -/
theorem norm_mollifiedExtensionLp_le (μ : Mollifier n) (hp : p ≠ ∞) :
    ‖mollifiedExtensionLp (F := F) μ hp‖ ≤ (2 : ℝ) ^ (1 / p.toReal) :=
  (mollifiedExtensionLp (F := F) μ hp).opNorm_le_bound (by positivity) (norm_extensionLp_le μ hp)

end SobolevSpace.Trace.HalfSpace
