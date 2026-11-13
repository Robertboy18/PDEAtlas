/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.SimpleEigenpair
public import PDE.Hyperbolic.ConservationLaw.System.Basic

/-!
# Local characteristic eigenpairs from strict hyperbolicity

At a strictly hyperbolic state, strict hyperbolicity supplies a real
eigenbasis of the flux Jacobian with distinct speeds. Local C² regularity of the flux makes
the Jacobian locally C¹. Composing it with the constructed normalized eigenpair gives C¹
characteristic vectors and speeds near that state.

The eigenpairs vary with the state, with each vector normalized by its coordinate
in the original eigenbasis. The eigenvalue gap makes the normalized equation locally
invertible, and the chain rule transfers this dependence to the flux Jacobian.

`exists_local_eigenpairs_of_strict_hyperbolicity` is the local form of Evans, §11.1.2,
Theorem 2, for a `C²` flux and with `C¹` dependence: near a strictly hyperbolic state the
eigenvalues `λ_k` and right eigenvectors `r_k` of `DF` depend continuously differentiably
on the state. We normalize `r_k` by its `k`-th coordinate in the eigenbasis at the base
state instead of by `|r_k| = 1`. As in Evans's proof, the dependence comes from the implicit
function theorem, which Mathlib provides.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.2, the definition of strict hyperbolicity and
  Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Analysis.Calculus.SimpleEigenpair

/-- A locally C² flux that is strictly hyperbolic at one state has locally C¹ normalized
characteristic eigenpairs through its eigenbasis. Differentiability of the flux is
included on the resulting neighborhood, so every displayed `fderiv` is its Jacobian. -/
theorem exists_local_eigenpairs_of_strict_hyperbolicity {m : ℕ} {flux : ℝ^m → ℝ^m} {u₀ : ℝ^m}
    (hhyper : IsStrictlyHyperbolicAt flux u₀) (hflux : ContDiffAt ℝ 2 flux u₀) :
    ∃ b : Module.Basis (Fin m) ℝ (ℝ^m),
      ∃ eig : Fin m → ℝ, Function.Injective eig ∧
        ∀ k, ∃ ψ : ℝ^m → ℝ^m × ℝ,
          ψ u₀ = (b k, eig k) ∧ ContDiffAt ℝ 1 ψ u₀ ∧
          ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℝ flux u ∧ ContDiffAt ℝ 1 ψ u ∧
            Module.End.HasEigenvector (fderiv ℝ flux u).toLinearMap
              (ψ u).2 (ψ u).1 ∧ b.equivFun (ψ u).1 k = 1 := by
  obtain ⟨_, b, eig, hinj, hvec⟩ := hhyper
  have hD : ContDiffAt ℝ 1 (fderiv ℝ flux) u₀ :=
    hflux.fderiv_right (by decide)
  refine ⟨b, eig, hinj, fun k ↦ ?_⟩
  obtain ⟨χ, hχ₀, hχ, hnear, _⟩ := exists_normalized_eigenpair b (fderiv ℝ flux u₀)
    eig k (fun j ↦ (hvec j).apply_eq_smul) (fun j hj heq ↦ hj (hinj heq))
  let ψ := fun u ↦ χ (fderiv ℝ flux u)
  refine ⟨ψ, hχ₀, (hχ.of_le (show (1 : ℕ∞ω) ≤ ω from le_top)).comp u₀ hD, ?_⟩
  filter_upwards [hD.continuousAt.eventually hnear,
    hflux.eventually (by simp)] with u hu hfu
  have hDu : ContDiffAt ℝ 1 (fderiv ℝ flux) u := hfu.fderiv_right (by decide)
  refine ⟨hfu.differentiableAt (by decide),
    (hu.1.of_le (show (1 : ℕ∞ω) ≤ ω from le_top)).comp u hDu, ?_, hu.2.2.1⟩
  exact Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hu.2.1, hu.2.2.2⟩

end PDE.Hyperbolic.ConservationLaw.System
