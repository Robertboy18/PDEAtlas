/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Classical.Representative
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Conjugation

/-!
# Canonical classical representatives of real Sobolev data

The representative is constructed from the complex Bessel distribution
and is identified with its physical `L²` class. Realness of the original datum
therefore gives pointwise realness of the continuous representative.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BesselPotentialSpace SchwartzMap

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

/-- The canonical complex representative agrees with the physical `L²` class. -/
theorem c1Representative_ae_eq_toL2Fun (hs : (n : ℝ) < 2 * (s - 1))
    (hs0 : 0 ≤ s) (f : H^{s}(ℝ^n)) :
    (BesselPotentialSpace.c1Representative (by simpa using hs) f : ℝ^n → ℂ)
      =ᵐ[volume] toL2Fun hs0 f := by
  apply PDE.ae_eq_of_integral_schwartz_smul_eq
    (BesselPotentialSpace.c1Representative (by simpa using hs) f).continuous.locallyIntegrable
    ((Lp.memLp (toL2Fun hs0 f)).locallyIntegrable (by norm_num))
  intro φ
  rw [BesselPotentialSpace.integral_smul_c1Representative,
    toDistr_eq_toL2Fun hs0, Lp.toTemperedDistribution_apply]

/-- The canonical complex representative of a real datum is real at every point. -/
theorem HsSpaceReal.im_c1Representative_eq_zero
    (hs : (n : ℝ) < 2 * (s - 1)) (f : HsSpaceReal n s) (x : ℝ^n) :
    (BesselPotentialSpace.c1Representative (by simpa using hs) f.1 x).im = 0 := by
  have hs0 : 0 ≤ s := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hae : (fun y : ℝ^n ↦
      (BesselPotentialSpace.c1Representative (by simpa using hs) f.1 y).im)
      =ᵐ[volume] fun _ ↦ (0 : ℝ) := by
    filter_upwards [c1Representative_ae_eq_toL2Fun hs hs0 f.1,
      f.isRealL2_toL2Fun hs0] with y hy him
    rw [hy, him]
  exact congrFun (Measure.eq_of_ae_eq hae
    (Complex.continuous_im.comp
      (BesselPotentialSpace.c1Representative (by simpa using hs) f.1).continuous)
    continuous_const) x

/-- The natural real `C¹` representative of a real fractional datum. -/
def HsSpaceReal.c1Representative (hs : (n : ℝ) < 2 * (s - 1))
    (f : HsSpaceReal n s) (x : ℝ^n) : ℝ :=
  (BesselPotentialSpace.c1Representative (by simpa using hs) f.1 x).re

/-- The natural representative is jointly differentiable in the spatial variables. -/
theorem HsSpaceReal.contDiff_c1Representative (hs : (n : ℝ) < 2 * (s - 1))
    (f : HsSpaceReal n s) :
    ContDiff ℝ 1 (f.c1Representative hs) :=
  Complex.reCLM.contDiff.comp
    (BesselPotentialSpace.contDiff_c1Representative (by simpa using hs) f.1)

/-- The canonical real representative is the original physical real `L²` datum. -/
theorem HsSpaceReal.c1Representative_ae_eq (hs : (n : ℝ) < 2 * (s - 1))
    (hs0 : 0 ≤ s) (f : HsSpaceReal n s) :
    f.c1Representative hs =ᵐ[volume] (HsSpaceReal.toL2FunCLM n hs0 f : ℝ^n → ℝ) := by
  filter_upwards [c1Representative_ae_eq_toL2Fun hs hs0 f.1,
    HsSpaceReal.toL2FunCLM_apply_ae hs0 f] with x hx hreal
  exact (congrArg Complex.re hx).trans hreal.symm

/-- Any continuous literal datum in the same physical `L²` class is the
canonical representative pointwise. -/
theorem HsSpaceReal.eq_c1Representative_of_ae_eq
    (hs : (n : ℝ) < 2 * (s - 1)) (hs0 : 0 ≤ s) (f : HsSpaceReal n s)
    {v : ℝ^n → ℝ} (hv : Continuous v)
    (h : v =ᵐ[volume] (HsSpaceReal.toL2FunCLM n hs0 f : ℝ^n → ℝ)) :
    v = f.c1Representative hs :=
  Measure.eq_of_ae_eq (h.trans (f.c1Representative_ae_eq hs hs0).symm)
    hv (f.contDiff_c1Representative hs).continuous

end SobolevSpace.Fractional
