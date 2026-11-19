/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.LipschitzEnergy
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.Truncation

/-!
# Uniform-energy sign-preserving wave approximations

Smooth arbitrary-growth reactions satisfying the sign condition admit a sequence of globally
Lipschitz reactions and Cauchy energy solutions. The reactions agree with the original on expanding
amplitude balls. The original finite initial potential energy bounds every approximate physical
energy uniformly, for all time. The full H¹ × L² bound is uniform on each finite time interval.
These are steps 1-2 of the proof of Theorem 1 of Evans, §12.3.1, with the bounds (6)-(7).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.1, steps 1-2 of the proof of Theorem 1,
  equations (4)-(7).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Topology
open PDE.Analysis (primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

variable {n : ℕ}

/-- The sign condition makes the physical energy nonnegative. -/
theorem physicalEnergy_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    (hs : ∀ z, 0 ≤ z * f z) (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    0 ≤ physicalEnergy f x :=
  add_nonneg (mul_nonneg (by norm_num)
    (add_nonneg (General.Nonlinearity.gradientForm_nonneg x.1) (sq_nonneg _)))
    (integral_nonneg fun _ ↦ primitive_nonneg hf hs _)

/-- Potential domination bounds truncated energy by the original initial energy;
the truncated potential's integrability is a conclusion of the Lipschitz theorem. -/
theorem physicalEnergy_le_of_potential_le {f g : ℝ → ℝ} {K : NNReal} (hg : LipschitzWith K g)
    (hg0 : g 0 = 0) (hdom : ∀ z, primitive g z ≤ primitive f z) (x : H¹(ℝ^n) × DerivLp n 2 univ)
    (hF :
      Integrable (fun y ↦ primitive f ((energyTriple n).inclusion x.1 y)) (domainMeasure n univ)) :
    physicalEnergy g x ≤ physicalEnergy f x :=
  add_le_add le_rfl (integral_mono
    (integrable_potential_of_lipschitz hg hg0 ((energyTriple n).inclusion x.1)) hF
    (fun y ↦ hdom ((energyTriple n).inclusion x.1 y)))

/-- Arbitrary finite-energy data give energy solutions for a sequence
of smooth sign-preserving truncations. Their physical energy bounds are uniform
for all forward time; their full H¹ × L² bounds grow with the time horizon. -/
theorem exists_energy_approximations {m : ℕ∞} {f : ℝ → ℝ} (hf : ContDiff ℝ m f) (hm : m ≠ 0)
    (hs : ∀ z, 0 ≤ z * f z) (x : H¹(ℝ^n) × DerivLp n 2 univ)
    (hF :
      Integrable (fun y ↦ primitive f ((energyTriple n).inclusion x.1 y)) (domainMeasure n univ)) :
    ∃ (g : ℕ → ℝ → ℝ) (K : ℕ → NNReal)
      (hg : ∀ k, LipschitzWith (K k) (g k)) (hg0 : ∀ k, g k 0 = 0)
      (u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)),
      (∀ k, ContDiff ℝ m (g k) ∧ HasCompactSupport (g k) ∧
        EqOn (g k) f (Metric.closedBall 0 ((k : ℝ) + 1)) ∧
        (∀ z, 0 ≤ z * g k z) ∧ (∀ z, |g k z| ≤ |f z|) ∧
        ∀ z, primitive (g k) z ≤ primitive f z) ∧
      (∀ k, Cauchy.IsEnergySolution (hg k) (hg0 k) x (u k)) ∧
      (∀ k, Filter.Tendsto (u k) (𝓝[≥] (0 : ℝ)) (𝓝 x)) ∧
      (∀ k t, 0 ≤ t → physicalEnergy (g k) (u k t) = physicalEnergy (g k) x) ∧
      (∀ k t, 0 ≤ t → physicalEnergy (g k) (u k t) ≤ physicalEnergy f x) ∧
      (∀ k t, 0 ≤ t →
        gradientForm n (u k t).1 (u k t).1 + ‖(u k t).2‖ ^ 2 ≤
          2 * physicalEnergy f x) ∧
      ∀ k t, 0 ≤ t → ‖u k t‖ ≤
        ‖(energyTriple n).inclusion x.1‖ + (t + 1) * Real.sqrt (2 * physicalEnergy f x) := by
  have htr (k : ℕ) := exists_sign_preserving_lipschitz_reaction hf hm hs
    (R := (k : ℝ) + 1) (by positivity)
  choose g K hreg hsupport hg hagree hsign habs hdom using htr
  let hg0 (k : ℕ) : g k 0 = 0 := reaction_zero (hg k).continuous (hsign k)
  have hsol (k : ℕ) := exists_energySolution_of_lipschitz (hg k) (hsign k) x
  choose u hu htrace he hgrad hnorm huniq using hsol
  have hinit (k : ℕ) : physicalEnergy (g k) x ≤ physicalEnergy f x :=
    physicalEnergy_le_of_potential_le (hg k) (hg0 k) (hdom k) x hF
  refine ⟨g, K, hg, hg0, u, fun k ↦ ⟨hreg k, hsupport k, hagree k, hsign k, habs k, hdom k⟩,
    hu, htrace, he, ?_, ?_, ?_⟩
  · intro k t ht
    rw [he k t ht]
    exact hinit k
  · exact fun k t ht ↦ (hgrad k t ht).trans (mul_le_mul_of_nonneg_left (hinit k) (by norm_num))
  · intro k t ht
    apply (hnorm k t ht).trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hinit k) (by norm_num : (0 : ℝ) ≤ 2)))
      (by linarith : 0 ≤ t + 1))

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
