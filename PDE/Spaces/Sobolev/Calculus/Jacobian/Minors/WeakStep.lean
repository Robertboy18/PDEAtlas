/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Jacobian.Minors.Distribution
public import PDE.Analysis.WeakSequentialBoundedness

/-!
# Induction steps for weak continuity of Sobolev minors

Degree one is a continuous linear coordinate of the graph. At higher
degree, the distribution formula pairs a strongly convergent value with a
weakly convergent lower minor. Uniform bounds follow from weak sequential
convergence and the determinant norm estimate. Reflexivity then identifies
the weak limit along the whole original sequence.

These are the induction steps of step 3 of the proof of Evans's lemma on weak continuity of
determinants (§8.2.4(b)), where a cofactor is expanded in minors of one degree less times uniformly
convergent factors, down to the entries of `Du_k`, which converge weakly. Our factors converge
strongly in `L^p` instead of uniformly.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(b), proof of the Lemma (Weak continuity of
  determinants), steps 3-4, pp. 477-478.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology Distributions Matrix.Norms.Elementwise Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Opens (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "μΩ" => domainMeasure n Ω

/-- Degree-one minors are weakly sequentially continuous: if `1 < p < ∞` and `u k → U` weakly
in `(W^{1,p}(Ω))^1`, then `wkpJacobianMinorLp σ (u k) → wkpJacobianMinorLp σ U` weakly in `L^p`.
No compactness is used. -/
theorem tendsto_weak_wkpJacobianMinorLp_one
    [Fact (1 ≤ p / ENNReal.ofReal ((1 : ℕ) : ℝ))]
    (hr : 1 < p / ENNReal.ofReal ((1 : ℕ) : ℝ))
    (hr_top : p / ENNReal.ofReal ((1 : ℕ) : ℝ) ≠ ∞)
    (σ : Fin 1 → Fin n) {u : ℕ → Fin 1 → W^{1,p}(Ω)} {U : Fin 1 → W^{1,p}(Ω)}
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ (Fin 1 → W^{1,p}(Ω)) (u k)) atTop
      (𝓝 (toWeakSpace ℝ (Fin 1 → W^{1,p}(Ω)) U))) :
    Tendsto (fun k ↦ toWeakSpace ℝ
        (Lp ℝ (p / ENNReal.ofReal ((1 : ℕ) : ℝ)) μΩ)
          (wkpJacobianMinorLp (m := 1) (n := n) (p := p) (Ω := Ω) σ (u k))) atTop
      (𝓝 (toWeakSpace ℝ (Lp ℝ (p / ENNReal.ofReal ((1 : ℕ) : ℝ)) μΩ)
        (wkpJacobianMinorLp (m := 1) (n := n) (p := p) (Ω := Ω) σ U))) := by
  have hmatrix : Tendsto (fun k ↦ toWeakSpace ℝ
      (Lp (Matrix (Fin 1) (Fin 1) ℝ) p μΩ) (wkpSelectedJacobianCLM σ (u k))) atTop
      (𝓝 (toWeakSpace ℝ (Lp (Matrix (Fin 1) (Fin 1) ℝ) p μΩ)
        (wkpSelectedJacobianCLM σ U))) :=
    ((WeakSpace.map (wkpSelectedJacobianCLM (p := p) (Ω := Ω) σ)).continuous.tendsto
      (toWeakSpace ℝ _ U)).comp hu
  have hminor := Lp.isBounded_matrixDet_range (by decide : 0 < 1) _
    (PDE.Analysis.isBounded_range_of_tendsto_weak hmatrix)
  apply Lp.tendsto_weak_of_test_integrals Ω hr hr_top
    (fun k ↦ wkpJacobianMinorLp σ (u k)) (wkpJacobianMinorLp σ U) hminor
  intro φ
  let D : (Fin 1 → W^{1,p}(Ω)) →L[ℝ] Lp ℝ p μΩ :=
    (wkpCoordinateCLM (singleDerivIndex n (σ 0))).comp (ContinuousLinearMap.proj 0)
  have htest (V : Fin 1 → W^{1,p}(Ω)) :
      (∫ x, wkpJacobianMinorLp (m := 1) (p := p) (Ω := Ω) σ V x * φ x ∂μΩ) =
        Lp.testFunctionPairing Ω φ (D V) := by
    rw [Lp.testFunctionPairing_apply]
    apply integral_congr_ae
    filter_upwards [coeFn_wkpJacobianMinorLp (p := p) (Ω := Ω) σ V] with x hx
    rw [hx, Matrix.det_fin_one]
    rfl
  simp_rw [htest]
  exact (WeakBilin.eval_continuous (topDualPairing ℝ (Fin 1 → W^{1,p}(Ω))).flip
    ((Lp.testFunctionPairing Ω φ).comp D)).continuousAt.tendsto.comp hu

variable {m : ℕ}
    [Fact (1 ≤ p / ENNReal.ofReal (m : ℝ))]
    [Fact (1 ≤ p / ENNReal.ofReal ((m + 1 : ℕ) : ℝ))]
    [ENNReal.HolderTriple p (p / ENNReal.ofReal (m : ℝ))
      (p / ENNReal.ofReal ((m + 1 : ℕ) : ℝ))]

local notation "ρ" => p / ENNReal.ofReal ((m + 1 : ℕ) : ℝ)
local notation "θ" => p / ENNReal.ofReal (m : ℝ)

/-- One induction step, for `0 < m`, `p ≠ ∞` and `1 < p/(m + 1) < ∞`: if `u k → U` weakly in
`(W^{1,p}(Ω))^{m+1}`, `u k 0 → U 0` strongly in `L^p`, and each lower minor
`wkpJacobianMinorLp (σ ∘ j.succAbove) (u k ∘ Fin.succ)` converges weakly in `L^{p/m}` to that of
`U`, then `wkpJacobianMinorLp σ (u k) → wkpJacobianMinorLp σ U` weakly in `L^{p/(m+1)}`.
`tendsto_weak_wkpJacobianMinorLp_of_strong_base` derives the hypotheses on the lower minors by
induction. -/
theorem tendsto_weak_wkpJacobianMinorLp_succ_of_strong_base
    (hm : 0 < m) (hp : p ≠ ∞) (hr : 1 < ρ) (hr_top : ρ ≠ ∞)
    (σ : Fin (m + 1) → Fin n) {u : ℕ → Fin (m + 1) → W^{1,p}(Ω)} {U : Fin (m + 1) → W^{1,p}(Ω)}
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ (Fin (m + 1) → W^{1,p}(Ω)) (u k)) atTop
      (𝓝 (toWeakSpace ℝ (Fin (m + 1) → W^{1,p}(Ω)) U)))
    (hbase : Tendsto (fun k ↦ wkpBaseCoordinateCLM (u k 0)) atTop
      (𝓝 (wkpBaseCoordinateCLM (U 0))))
    (hlower : ∀ j : Fin (m + 1),
      Tendsto (fun k ↦ toWeakSpace ℝ (Lp ℝ θ μΩ)
        (wkpJacobianMinorLp (σ ∘ j.succAbove) (u k ∘ Fin.succ))) atTop
        (𝓝 (toWeakSpace ℝ (Lp ℝ θ μΩ)
          (wkpJacobianMinorLp (σ ∘ j.succAbove) (U ∘ Fin.succ))))) :
    Tendsto (fun k ↦ toWeakSpace ℝ (Lp ℝ ρ μΩ) (wkpJacobianMinorLp σ (u k))) atTop
      (𝓝 (toWeakSpace ℝ (Lp ℝ ρ μΩ) (wkpJacobianMinorLp σ U))) := by
  have hmatrix : Tendsto (fun k ↦ toWeakSpace ℝ
      (Lp (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) p μΩ)
        (wkpSelectedJacobianCLM σ (u k))) atTop
      (𝓝 (toWeakSpace ℝ (Lp (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) p μΩ)
        (wkpSelectedJacobianCLM σ U))) :=
    ((WeakSpace.map (wkpSelectedJacobianCLM (p := p) (Ω := Ω) σ)).continuous.tendsto
      (toWeakSpace ℝ _ U)).comp hu
  have hminor := Lp.isBounded_matrixDet_range (Nat.succ_pos m) _
    (PDE.Analysis.isBounded_range_of_tendsto_weak hmatrix)
  apply Lp.tendsto_weak_of_test_integrals Ω hr hr_top
    (fun k ↦ wkpJacobianMinorLp σ (u k)) (wkpJacobianMinorLp σ U) hminor
  intro φ
  simp only [← Lp.testFunctionPairing_apply, testFunctionPairing_wkpJacobianMinorLp hm hp]
  have hpair (j : Fin (m + 1)) :=
    Lp.tendsto_testProductPairing_of_strong_weak Ω (r := ρ)
      hbase (hlower j) (PDE.Analysis.isBounded_range_of_tendsto_weak (hlower j))
      (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single (σ j) (1 : ℝ)) φ)
  have hsum := tendsto_finsetSum Finset.univ
    (fun (j : Fin (m + 1)) _ ↦
      (tendsto_const_nhds (x := (-1 : ℝ) ^ (j : ℕ))).mul (hpair j))
  simpa only [Lp.testProductPairing_apply] using hsum.neg

end SobolevSpace.GraphSpace
