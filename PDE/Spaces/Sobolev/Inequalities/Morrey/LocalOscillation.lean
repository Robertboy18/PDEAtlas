/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.FullEmbedding
public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.Ball
import PDE.Elliptic.Regularity.Boundary.ConcreteUnitBallAtlas
import PDE.Spaces.Sobolev.GraphSpace.Norms
import CAS.ExactTactic

/-!
# Interior oscillation controlled by the weak gradient

Subtracting the mean removes the zeroth-order term in the Morrey estimate on the unit
ball. The affine Sobolev pullback then gives an estimate on every ball with its exact
radius dependence: for `n < p ≤ ∞`, `|f a - f b| ≤ C r^(1-n/p) ‖∇U‖_{Lᵖ(B(x,r))}` for all `a` and
`b` in `B(x, r)`, where `f` is a continuous representative of `U ∈ W^{1,p}(B(x, r))`.

Evans states Morrey's local estimate with `B(x, 2r)` on the right (the Remark after the proof of
§5.6.2, Theorem 4, and estimate (14) in the proof of §5.8.3, Theorem 5), and remarks that the
form with `B(x, r)` also holds, with a trickier proof. We get the unit-ball estimate from the
`C¹` extension operator, the Morrey embedding and the Poincaré inequality for the mean. Two
scalar identities are closed by the `cas` tactic of SymLean.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.2, Remark after Theorem 4, p. 283; and §5.8.3,
  Theorem 5, (14), p. 295.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

/-- For `n < p ≤ ∞` there is `C ≥ 0` such that, for every `U ∈ W^{1,p}(B(0, 1))` and every `f`
continuous on `B(0, 1)` and equal almost everywhere there to the base representative of `U`,
`‖f a - f b‖ ≤ C * ‖∇ U‖` for all `a` and `b` in `B(0, 1)`. -/
theorem exists_oscillation_bound_unitBall
    {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : (n : ℝ≥0∞) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : W^{1,p}(ball (0 : ℝ^n) 1))
      (f : ℝ^n → ℝ), ContinuousOn f (ball 0 1) →
      f =ᵐ[domainMeasure n (ball 0 1)] baseRepresentative U →
      ∀ a ∈ ball (0 : ℝ^n) 1, ∀ b ∈ ball (0 : ℝ^n) 1,
        ‖f a - f b‖ ≤ C * ‖∇ U‖ := by
  let : Boundary.C1ExtensionAtlas n (ball (0 : ℝ^n) 1) :=
    (Boundary.Atlas.UnitBall.ConcreteAtlas.c2BoundaryAtlas n).toC1ExtensionAtlas
  let E := Extension.C1.extensionCLM (n := n) (p := p) (Ω := ball 0 1)
  obtain ⟨A, hA, hMorrey⟩ := exists_morreyEmbeddingBound (Fact.out : 0 < n) hp
  obtain ⟨P, hP, hPoincare⟩ := exists_norm_base_subtractMean_le_of_c1Domain (p := p)
    ((convex_ball (0 : ℝ^n) 1).isConnected (nonempty_ball.mpr zero_lt_one))
  refine ⟨2 * A * ‖E‖ * (P + n), by positivity, ?_⟩
  intro U f hf heq a ha b hb
  let V := subtractMean U
  have hVnorm : ‖V‖ ≤ (P + n) * ‖∇ U‖ := by
    calc
      ‖V‖ ≤ ‖wkpBaseCoordinateCLM V‖ +
          ∑ i : Fin n, ‖(V : WkpAmbientOn n 1 p (ball 0 1)) (singleDerivIndex n i)‖ :=
        ambient_norm_le_base_add_sum_deriv V.val
      _ ≤ P * ‖∇ U‖ + ∑ _i : Fin n, ‖∇ U‖ := by
        apply add_le_add (hPoincare U)
        apply Finset.sum_le_sum
        intro i _
        simpa only [V, wkpGradientCLM_subtractMean] using
          norm_derivCoordinate_le_wkpGradientCLM V i
      _ = (P + n) * ‖∇ U‖ := by simp [add_mul]
  obtain ⟨F, hF, hFnorm⟩ := hMorrey (E V)
  let m := ⨍ x, wkpBaseCoordinateCLM U x ∂domainMeasure n (ball 0 1)
  have hFrep : (fun x ↦ F x) =ᵐ[domainMeasure n (ball 0 1)] fun x ↦ f x - m := by
    filter_upwards [ae_restrict_of_ae (s := ball (0 : ℝ^n) 1) hF,
      Extension.C1.extensionCLM_agree_ae V, subtractMean_base_ae U, heq]
      with x hx hE hV hfx
    change f x = wkpBaseCoordinateCLM U x at hfx
    exact hx.trans (hE.trans (hV.trans (congrArg (fun t ↦ t - m) hfx.symm)))
  have hpoint := Measure.eqOn_open_of_ae_eq hFrep isOpen_ball
    F.continuous.continuousOn (hf.sub continuousOn_const)
  have hnorm : ‖F‖ ≤ A * ‖E‖ * ((P + n) * ‖∇ U‖) := by
    calc
      ‖F‖ ≤ A * ‖E V‖ := hFnorm
      _ ≤ A * (‖E‖ * ‖V‖) := mul_le_mul_of_nonneg_left (E.le_opNorm V) hA
      _ ≤ A * (‖E‖ * ((P + n) * ‖∇ U‖)) := by gcongr
      _ = _ := by rw [mul_assoc]
  have hFa : ‖F a‖ ≤ ‖F‖ := F.norm_apply_le a
  have hFb : ‖F b‖ ≤ ‖F‖ := F.norm_apply_le b
  calc
    ‖f a - f b‖ = ‖F a - F b‖ := by
      have hpa : F a = f a - m := hpoint ha
      have hpb : F b = f b - m := hpoint hb
      rw [hpa, hpb]
      congr 1
      abel
    _ ≤ ‖F a‖ + ‖F b‖ := norm_sub_le _ _
    _ ≤ 2 * (A * ‖E‖ * ((P + n) * ‖∇ U‖)) := by linarith
    _ = (2 * A * ‖E‖ * (P + n)) * ‖∇ U‖ := by cas

/-- The local Morrey oscillation estimate on balls: for `n < p ≤ ∞` there is `C ≥ 0` such that,
for every ball `B(x, r)`, every `U ∈ W^{1,p}(B(x, r))` and every `f` continuous on `B(x, r)` and
equal almost everywhere there to the base representative of `U`,
`‖f a - f b‖ ≤ C * normFactor n r p * (r * ‖∇ U‖)` for all `a` and `b` in `B(x, r)`. For finite
`p`, `normFactor n r p` is `r^(-n/p)`, so the bound scales as `r^(1-n/p)`. -/
theorem exists_oscillation_bound_ball
    {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : (n : ℝ≥0∞) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ^n) (r : ℝ), 0 < r →
      ∀ (U : W^{1,p}(ball x r)) (f : ℝ^n → ℝ),
        ContinuousOn f (ball x r) →
        f =ᵐ[domainMeasure n (ball x r)] baseRepresentative U →
        ∀ a ∈ ball x r, ∀ b ∈ ball x r,
          ‖f a - f b‖ ≤ C * MeanScaling.normFactor n r p *
            (r * ‖∇ U‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_oscillation_bound_unitBall hp
  refine ⟨C, hC, ?_⟩
  intro x r hr U f hf heq a ha b hb
  obtain ⟨V, hbase, hgrad⟩ := MeanScaling.exists_ballPullback x hr U
  let e := MeanScaling.ballHomeomorph x hr
  have hmap : MapsTo e (ball 0 1) (ball x r) := by
    intro y hy
    exact (MeanScaling.image_ball x hr).subset ⟨y, hy, rfl⟩
  have hrep : (fun y ↦ f (e y)) =ᵐ[domainMeasure n (ball 0 1)]
      baseRepresentative V :=
    ((MeanScaling.quasiMeasurePreserving_ballHomeomorph x hr).ae_eq_comp heq).trans
      hbase.symm
  have hnorm : ‖∇ V‖ =
      MeanScaling.normFactor n r p * (r * ‖∇ U‖) := by
    rw [Lp.norm_def, eLpNorm_congr_ae hgrad]
    change (eLpNorm (r • (fun y ↦ ∇ U (e y)))
      p (domainMeasure n (ball 0 1))).toReal = _
    rw [eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, Real.norm_of_nonneg hr.le,
      MeanScaling.eLpNorm_comp_ballHomeomorph x hr p, ← Lp.norm_def]
    cas
  have ha' : e.symm a ∈ ball (0 : ℝ^n) 1 := by
    rw [← MeanScaling.preimage_ball x hr]
    change e (e.symm a) ∈ ball x r
    simpa only [e.apply_symm_apply] using ha
  have hb' : e.symm b ∈ ball (0 : ℝ^n) 1 := by
    rw [← MeanScaling.preimage_ball x hr]
    change e (e.symm b) ∈ ball x r
    simpa only [e.apply_symm_apply] using hb
  simpa only [e.apply_symm_apply, hnorm, mul_assoc] using
    hbound V (fun y ↦ f (e y)) (hf.comp e.continuous.continuousOn hmap) hrep
      (e.symm a) ha' (e.symm b) hb'

end SobolevSpace.GraphSpace
