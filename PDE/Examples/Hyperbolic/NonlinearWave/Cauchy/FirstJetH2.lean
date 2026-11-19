/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.NonlinearWave.Cauchy.FirstJet
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.Regularity.IntegratedTime

/-!
# H² persistence with a nonsmooth first-jet reaction

For the Lipschitz reaction `F = ‖Du‖ + |u_t| + u`, which is not differentiable, and
data `g ∈ H²(ℝⁿ)`, `v ∈ H¹(ℝⁿ)`, the energy solution of `FirstJet.exists_energySolution_h2`
has essentially bounded lifts `U`, `V`, `A` to `H²`, `H¹` and `L²` on every interval
`[0, T]`. The trajectory is absolutely continuous on `[0, T]`, and almost everywhere its
strong time derivative is `(V, A)` with `A = ΔU - F(u)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Examples.Cauchy.FirstJet

open PDE.Hyperbolic.NonlinearWave.Cauchy

/-- With `H² × H¹` data the energy solution stays in `H² × H¹` and is strongly
differentiable in time almost everywhere. -/
example {n : ℕ} (g : W^{2,2}(ℝ^n)) (v : H¹(ℝ^n)) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
      FirstJet.IsEnergySolution (normReaction_lipschitz n) (by simp [normReaction])
        (lowerOrderCLM (by decide : 1 ≤ 2) g, (energyTriple n).inclusion v) u ∧
      ∃ (U : ℝ → W^{2,2}(ℝ^n)) (V : ℝ → H¹(ℝ^n)) (A : ℝ → DerivLp n 2 univ),
        MemLp U ∞ (volume.restrict (Icc 0 T)) ∧
        MemLp V ∞ (volume.restrict (Icc 0 T)) ∧
        MemLp A ∞ (volume.restrict (Icc 0 T)) ∧
        AbsolutelyContinuousOnInterval u 0 T ∧
        (∀ᵐ t ∂volume.restrict (Ioo 0 T), HasDerivAt u (V t, A t) t) ∧
        ∀ t ∈ Icc (0 : ℝ) T,
          lowerOrderCLM (by decide : 1 ≤ 2) (U t) = (u t).1 ∧
          (energyTriple n).inclusion (V t) = (u t).2 ∧
          A t = wkpLaplacianCLM (U t) -
            FirstJet.reaction (normReaction_lipschitz n) (by simp [normReaction]) (u t) := by
  obtain ⟨u, hu, hh⟩ := FirstJet.exists_energySolution_h2
    (normReaction_lipschitz n) (by simp [normReaction]) g v
  obtain ⟨U, V, A, hU, hV, hA, hrep⟩ := hh T
  obtain ⟨hAC, hd⟩ := hu.absolutelyContinuous_of_lifts hT hV hA
    (fun t ht ↦ (hrep t ht).2.1) (fun t ht ↦ (hrep t ht).2.2.1)
  exact ⟨u, hu, U, V, A, hU, hV, hA, hAC, hd,
    fun t ht ↦ ⟨(hrep t ht).1, (hrep t ht).2.1, (hrep t ht).2.2.2⟩⟩

end PDE.Examples.Cauchy.FirstJet
