/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.InitialValueWeakForm
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import PDE.Analysis.Scalar.Semiconcavity.Lipschitz
import PDE.Hyperbolic.ConservationLaw.InitialBoundary.TimeCutoff
import PDE.Spaces.Sobolev.Calculus.Product.LipschitzCoefficient
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import Mathlib.Analysis.Calculus.Rademacher

/-!
# From Oleinik's almost-everywhere slope bound to semiconcavity

The spatial weak derivative of a Lipschitz potential agrees with its
classical partial almost everywhere. Fubini therefore identifies the
derivatives of almost every time slice. The scalar absolutely continuous
argument gives every spatial second difference on those slices. Continuity
extends the result to every positive time, retaining the factor `1 + 1/t`.

The hypothesis is the slope condition (ii) in the definition of entropy solution of Evans,
§3.4.3(b), imposed almost everywhere, and the conclusion is the semiconcavity condition (c) in
the definition of weak solution of Evans, §3.3.3(b), for the potential.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(b), definition of weak solution, condition (c);
  §3.4.3(b), definition of an entropy solution, condition (ii).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Common
open scoped NNReal

namespace PDE.Hyperbolic.ConservationLaw

/-- A fixed-time scalar slice has the same Lipschitz constant as the
Euclidean spacetime field. -/
private theorem lipschitzWith_scalarSpatialSlice
    {V : ℝ^2 → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) (t : ℝ) :
    LipschitzWith L (fun x ↦ V !₂[t, x]) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have hsub : (!₂[t, x] : ℝ^2) - !₂[t, y] = PiLp.single 2 (1 : Fin 2) (x - y) := by
    ext i
    fin_cases i <;> simp
  have hdist : dist (!₂[t, x] : ℝ^2) !₂[t, y] = dist x y := by
    rw [dist_eq_norm, hsub, PiLp.norm_single, dist_eq_norm]
  simpa only [hdist] using hV.dist_le_mul !₂[t, x] !₂[t, y]

/-- The spatial partial, at a differentiability point, is the
derivative of the scalar spatial slice. -/
private theorem hasDerivAt_scalarSpatialSlice
    {V : ℝ^2 → ℝ} {t x : ℝ} (hV : DifferentiableAt ℝ V !₂[t, x]) :
    HasDerivAt (fun y ↦ V !₂[t, y]) ((∂[1] V) !₂[t, x]) x := by
  have hline : (fun y ↦ (!₂[t, y] : ℝ^2)) = coordinateLine 1 !₂[t, x] := by
    funext y
    ext i
    fin_cases i <;> simp [coordinateLine]
  have hV' : DifferentiableAt ℝ V (coordinateLine 1 !₂[t, x] x) := by
    rw [← hline]
    exact hV
  have hd := hV'.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_coordinateLine 1 !₂[t, x] x)
  have hpoint : coordinateLine 1 !₂[t, x] x = !₂[t, x] := congrFun hline.symm x
  rw [hpoint] at hd
  change HasDerivAt (V ∘ fun y ↦ (!₂[t, y] : ℝ^2)) _ x
  rw [hline]
  simpa [partialDeriv] using hd

/-- A Lipschitz potential whose weak spatial derivative has Oleinik's
AE slope bound satisfies the pointwise second-difference bound at every
positive time. -/
theorem secondDifference_le_of_lipschitz_weakDerivative_oleinik {V u : ℝ^2 → ℝ} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hweak : SobolevSpace.HasWeakDerivativeOn forwardHalfSpace [1] V u)
    {C : ℝ}
    (hslope : ∀ᵐ t ∂volume, 0 < t → ∀ᵐ z ∂volume, 0 < z → ∀ᵐ x ∂volume,
      u !₂[t, x + z] - u !₂[t, x] ≤ C * (1 + t⁻¹) * z) :
    ∀ x z t, 0 < t → V !₂[t, x + z] - 2 * V !₂[t, x] + V !₂[t, x - z] ≤ C * (1 + t⁻¹) * z ^ 2 := by
  have hclassical :=
    SobolevSpace.GraphSpace.LipschitzWith.hasWeakDerivativeOn_lipschitzWeakCoord hV 1
  have hclassical' := SobolevSpace.HasWeakDerivativeOn.mono
    forwardHalfSpace.isOpen.measurableSet (subset_univ _) hclassical
  have heq := hclassical'.unique_ae forwardHalfSpace.isOpen hweak
  have heq' : ∀ᵐ p ∂volume, 0 < p 0 → SobolevSpace.GraphSpace.lipschitzWeakCoord V 1 p = u p :=
    (ae_restrict_iff' forwardHalfSpace.isOpen.measurableSet).mp heq
  have hpoint : ∀ᵐ p ∂volume, 0 < p 0 →
      HasDerivAt (fun y ↦ V !₂[p 0, y]) (u p) (p 1) := by
    filter_upwards [hV.ae_differentiableAt (μ := volume), heq'] with p hp he ht
    have hpair : (!₂[p 0, p 1] : ℝ^2) = p := by
      ext i
      fin_cases i <;> simp
    have hpartial : (∂[1] V) p = u p := by
      have hh := he ht
      rwa [SobolevSpace.GraphSpace.lipschitzWeakCoord, hp.lineDeriv_eq_fderiv] at hh
    have hd := hasDerivAt_scalarSpatialSlice
      (show DifferentiableAt ℝ V !₂[p 0, p 1] from hpair.symm ▸ hp)
    simpa only [hpair, hpartial] using hd
  have hpairPoint : ∀ᵐ p : ℝ × ℝ ∂volume,
      0 < p.1 → HasDerivAt (fun y ↦ V !₂[p.1, y]) (u !₂[p.1, p.2]) p.2 := by
    have h := measurePreserving_spaceTimePair.quasiMeasurePreserving.ae hpoint
    simpa [spaceTimePair_apply] using h
  have hslices : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      0 < t → HasDerivAt (fun y ↦ V !₂[t, y]) (u !₂[t, x]) x := by
    rw [Measure.volume_eq_prod] at hpairPoint
    exact Measure.ae_ae_of_ae_prod hpairPoint
  have hsemi : ∀ᵐ t ∂volume, 0 < t → ∀ x z, V !₂[t, x + z] - 2 * V !₂[t, x] + V !₂[t, x - z] ≤
        C * (1 + t⁻¹) * z ^ 2 := by
    filter_upwards [hslices, hslope] with t ht hs htpos
    have hd : ∀ᵐ x ∂volume, HasDerivAt (fun y ↦ V !₂[t, y]) (u !₂[t, x]) x := by
      filter_upwards [ht] with x hx using hx htpos
    exact PDE.Analysis.Scalar.secondDifference_le_of_lipschitz_ae_deriv_slope
      (lipschitzWith_scalarSpatialSlice hV t) hd (hs htpos)
  intro x z t ht
  have hleft : Continuous (fun s : ℝ ↦
      V !₂[s, x + z] - 2 * V !₂[s, x] + V !₂[s, x - z]) := by
    have hc (y : ℝ) : Continuous (fun s : ℝ ↦ V !₂[s, y]) := by
      apply hV.continuous.comp
      exact (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm.continuous.comp
        (continuous_pi fun i ↦ by fin_cases i <;> fun_prop)
    exact ((hc (x + z)).sub (continuous_const.mul (hc x))).add (hc (x - z))
  have hright : ContinuousOn (fun s : ℝ ↦ C * (1 + s⁻¹) * z ^ 2) (Ioi 0) :=
    (continuousOn_const.mul (continuousOn_const.add
      (continuousOn_id.inv₀ (fun s hs ↦ ne_of_gt hs)))).mul continuousOn_const
  have hae : (fun s : ℝ ↦ min (V !₂[s, x + z] - 2 * V !₂[s, x] + V !₂[s, x - z])
        (C * (1 + s⁻¹) * z ^ 2)) =ᵐ[volume.restrict (Ioi 0)]
      fun s ↦ V !₂[s, x + z] - 2 * V !₂[s, x] + V !₂[s, x - z] := by
    change ∀ᵐ s ∂volume.restrict (Ioi 0), min (V !₂[s, x + z] - 2 * V !₂[s, x] + V !₂[s, x - z])
      (C * (1 + s⁻¹) * z ^ 2) = V !₂[s, x + z] - 2 * V !₂[s, x] + V !₂[s, x - z]
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hsemi] with s hs hspos using min_eq_left (hs hspos x z)
  exact min_eq_left_iff.mp (Measure.eqOn_open_of_ae_eq hae isOpen_Ioi
      (hleft.continuousOn.inf hright) hleft.continuousOn ht)

end PDE.Hyperbolic.ConservationLaw
