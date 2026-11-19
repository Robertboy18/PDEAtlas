/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Jacobian.Minors.WeakStep
public import PDE.Analysis.MeasureTheory.Lp.Exponent.Division

/-!
# Weak continuity of minors at finite real exponents

Induction on the degree derives weak continuity of every minor from weak
convergence of the graphs and strong convergence of their values.
There is no assumed continuity of lower minors: degree one is linear and the
higher steps use the distribution formula.

The exponent `q` is real and may be nonintegral. Every intermediate divided
exponent is greater than one, so the weak identification takes place in its
reflexive Lebesgue space.

For `m = n` and `σ = id` the conclusion is that of Evans's lemma on weak continuity of determinants
(§8.2.4(b)), `det Du_k ⇀ det Du` weakly in `L^{q/n}`, here with the strong convergence of the values
as a hypothesis. Evans gets uniform convergence of `u_k` from Morrey's inequality and the
Arzelà–Ascoli theorem (step 3) and identifies the weak limit through the `L^{q/n}` bound (step 4).
`Minors.Domain` derives the strong convergence from compactness.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(b), Lemma (Weak continuity of determinants), p. 476,
  and its proof, pp. 477-478.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- Let `q` be real with `0 < m < q`. If `u k → U` weakly in `(W^{1,q}(Ω))^m` and
`u k i → U i` strongly in `L^q` for every `i`, then `wkpJacobianMinorLp σ (u k)` converges
weakly in `L^{q/m}` to `wkpJacobianMinorLp σ U`, along the whole sequence. -/
theorem tendsto_weak_wkpJacobianMinorLp_of_strong_base
    {m n : ℕ} {Ω : Opens (ℝ^n)} {q : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)]
    [Fact (1 ≤ ENNReal.ofReal q / ENNReal.ofReal (m : ℝ))]
    (hm : 0 < m) (hmq : (m : ℝ) < q) (σ : Fin m → Fin n)
    {u : ℕ → Fin m → W^{1,ENNReal.ofReal q}(Ω)}
    {U : Fin m → W^{1,ENNReal.ofReal q}(Ω)}
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ
      (Fin m → W^{1,ENNReal.ofReal q}(Ω)) (u k)) atTop
      (𝓝 (toWeakSpace ℝ (Fin m → W^{1,ENNReal.ofReal q}(Ω)) U)))
    (hbase : ∀ i, Tendsto (fun k ↦ wkpBaseCoordinateCLM (u k i)) atTop
      (𝓝 (wkpBaseCoordinateCLM (U i)))) :
    Tendsto (fun k ↦ toWeakSpace ℝ
        (Lp ℝ (ENNReal.ofReal q / ENNReal.ofReal (m : ℝ)) (domainMeasure n Ω))
        (wkpJacobianMinorLp σ (u k))) atTop
      (𝓝 (toWeakSpace ℝ
        (Lp ℝ (ENNReal.ofReal q / ENNReal.ofReal (m : ℝ)) (domainMeasure n Ω))
        (wkpJacobianMinorLp σ U))) := by
  induction m generalizing q with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      exact tendsto_weak_wkpJacobianMinorLp_one
        (ENNReal.one_lt_ofReal_div_nat hm hmq) (ENNReal.ofReal_div_nat_ne_top q hm) σ hu
    | succ k =>
      have hk : 0 < k + 1 := Nat.succ_pos k
      have hkq : ((k + 1 : ℕ) : ℝ) < q := by
        push_cast at hmq ⊢
        linarith
      have : Fact (1 ≤ ENNReal.ofReal q / ENNReal.ofReal ((k + 1 : ℕ) : ℝ)) :=
        ⟨(ENNReal.one_lt_ofReal_div_nat hk hkq).le⟩
      have := ENNReal.holderTriple_div_nat_succ (ENNReal.ofReal q) hk
      let T :
          (Fin (k + 1 + 1) → W^{1,ENNReal.ofReal q}(Ω)) →L[ℝ]
            (Fin (k + 1) → W^{1,ENNReal.ofReal q}(Ω)) :=
        ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj i.succ
      have htail : Tendsto (fun a ↦ toWeakSpace ℝ
          (Fin (k + 1) → W^{1,ENNReal.ofReal q}(Ω)) (u a ∘ Fin.succ)) atTop
          (𝓝 (toWeakSpace ℝ
            (Fin (k + 1) → W^{1,ENNReal.ofReal q}(Ω)) (U ∘ Fin.succ))) :=
        (WeakSpace.map T).continuous.continuousAt.tendsto.comp hu
      apply tendsto_weak_wkpJacobianMinorLp_succ_of_strong_base hk ENNReal.ofReal_ne_top
        (ENNReal.one_lt_ofReal_div_nat hm hmq) (ENNReal.ofReal_div_nat_ne_top q hm)
        σ hu (hbase 0)
      intro j
      exact ih hk hkq (σ ∘ j.succAbove) htail (fun i ↦ hbase i.succ)

end SobolevSpace.GraphSpace
