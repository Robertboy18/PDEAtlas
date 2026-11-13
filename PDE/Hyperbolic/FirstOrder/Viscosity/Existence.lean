/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.Coefficients.SpaceTime
public import PDE.Parabolic.Systems.Transport.Existence.Unique
public import PDE.Spaces.Sobolev.Calculus.Slicing.SpaceTime.FiniteProduct

/-!
# Viscous approximations of symmetric first-order systems

Bounded C² matrix coefficients on a closed spacetime slab and H¹
initial and forcing data determine a strong solution of
`u_t - ε Δu + ∑ j, B_j ∂j u = f` for every ε > 0. Its initial value is the
canonical standard-mollifier convolution of the given data. The state is
L²(H³), its weak time derivative is L²(H¹), and the H¹ trace is
continuous through both endpoints. Uniqueness applies to every strong
solution with the same data.

This is the viscous approximate problem (11) and Theorem 1 of Evans, §7.3.2. The construction uses
the whole-space heat response. The equation retains the full coupled matrices; the target and
spatial dimensions may both be zero.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.2, equation (11) and Theorem 1, equation (12).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Hyperbolic.FirstOrder

open MeasureTheory Set PDE.Common
open PDE.Parabolic.Systems
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal NNReal

variable {n m : ℕ} {ε T : ℝ}

/-- The norm on a scalar Sobolev space is its inherited weak-derivative graph norm. -/
local instance viscousHkNormedAddCommGroup {k : ℕ} :
    NormedAddCommGroup (W^{k,2}(ℝ^n)) :=
  Submodule.normedAddCommGroup (wkpSubmoduleOn n k 2 univ)

/-- Real scalar multiplication on the scalar Sobolev graph. -/
local instance viscousHkNormedSpace {k : ℕ} : NormedSpace ℝ (W^{k,2}(ℝ^n)) :=
  Submodule.normedSpace (wkpSubmoduleOn n k 2 univ)

/-- The finite Hilbert product of the component Sobolev graphs. -/
local instance viscousProductHkNormedAddCommGroup {k : ℕ} :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin m ↦ W^{k,2}(ℝ^n))) :=
  PiLp.normedAddCommGroup 2 (fun _ : Fin m ↦ W^{k,2}(ℝ^n))

/-- Real scalar multiplication on the finite Sobolev product. -/
local instance viscousProductHkNormedSpace {k : ℕ} :
    NormedSpace ℝ (PiLp 2 (fun _ : Fin m ↦ W^{k,2}(ℝ^n))) :=
  PiLp.normedSpace 2 ℝ (fun _ : Fin m ↦ W^{k,2}(ℝ^n))

/-- Symmetric C² coefficients and H¹ data give a unique viscous
solution on every finite positive interval. The mollifier scale is ε itself;
there is no upper bound on ε in this existence and uniqueness theorem. -/
theorem exists_unique_viscous_approximation (hT : 0 < T)
    (B : Fin n → SpaceTime n → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ j p q, ContDiffOn ℝ 2 (fun y ↦ B j y p q) {y | y 0 ∈ Icc 0 T})
    (hsym : ∀ j y, y 0 ∈ Icc 0 T → (B j y).IsSymm) (M : ℝ≥0)
    (hzero : ∀ j p q y, y 0 ∈ Icc 0 T → ‖B j y p q‖ ≤ M)
    (hone : ∀ j p q y, y 0 ∈ Icc 0 T →
      ‖fderivWithin ℝ (fun z ↦ B j z p q) {z | z 0 ∈ Icc 0 T} y‖ ≤ M)
    (htwo : ∀ j p q y, y 0 ∈ Icc 0 T →
      ‖iteratedFDerivWithin ℝ 2 (fun z ↦ B j z p q) {z | z 0 ∈ Icc 0 T} y‖ ≤ M)
    (hε : 0 < ε) (g : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)))
    (f : PiLp 2 (fun _ : Fin m ↦ W^{1,2}({y : ℝ^(n + 1) | y 0 ∈ Ioo 0 T}))) :
    ∃ (U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2
        (volume.restrict (Ioc 0 T)))
      (G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
        (volume.restrict (Ioc 0 T)))
      (z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))),
      IsStrongTransportDiffusionSolution ε 0 T
        (fun j y p q ↦ B j (timeSpaceCons y.1 y.2) p q)
        (fun p y ↦ wkpBaseCoordinateCLM (f p) (timeSpaceCons y.1 y.2))
        (ContinuousLinearMap.piLpMap 2
          (fun _ : Fin m ↦ mollifierHkCLM (standardMollifier n) hε) g) U G z ∧
      (∀ V H w, IsStrongTransportDiffusionSolution ε 0 T
        (fun j y p q ↦ B j (timeSpaceCons y.1 y.2) p q)
        (fun p y ↦ wkpBaseCoordinateCLM (f p) (timeSpaceCons y.1 y.2))
        (ContinuousLinearMap.piLpMap 2
          (fun _ : Fin m ↦ mollifierHkCLM (standardMollifier n) hε) g) V H w →
        V = U ∧ H = G ∧ EqOn w z (Icc 0 T)) := by
  let μ := volume.restrict (Ioc 0 T)
  obtain ⟨A, hA, _hAnorm, hAbase, _hAfirst⟩ :=
    exists_wkpSpace_matrix_timeSlices hT B hB M hzero hone htwo
  have hAsym := base_timeSlices_symmetric B hsym A hAbase
  have hBrep : ∀ᵐ t ∂μ, ∀ᵐ x ∂volume, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (timeSpaceCons t x) p q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ae_all_iff.mpr fun j ↦ ae_all_iff.mpr fun p ↦ ae_all_iff.mpr fun q ↦
      hAbase t (Ioc_subset_Icc_self ht) j p q
  obtain ⟨F, Ft, _hFt, hFbase, _hFfirst, _hFtime⟩ := Slices.exists_vector_timeSlices_of_wkpSpaceOn f
  let P (p : Fin m) : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) →L[ℝ] W^{1,2}(ℝ^n) :=
    PiLp.proj 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) p
  let Fi (p : Fin m) := (P p).compLpL 2 μ F
  have hFi : ∀ᵐ t ∂μ, ∀ p, Fi p t = F t p := ae_all_iff.mpr fun p ↦ (P p).coeFn_compLpL F
  have hf : ∀ᵐ t ∂μ, ∀ᵐ x ∂volume, ∀ p, wkpBaseCoordinateCLM (Fi p t) x =
        wkpBaseCoordinateCLM (f p) (timeSpaceCons t x) := by
    filter_upwards [hFi, hFbase] with t ht hf
    exact hf.mono fun x hx p ↦ by simpa only [ht p] using hx p
  exact exists_unique_strongTransportDiffusionSolution_mollified hε hT A hA hAsym
    (fun j y p q ↦ B j (timeSpaceCons y.1 y.2) p q) hBrep Fi
    (fun p y ↦ wkpBaseCoordinateCLM (f p) (timeSpaceCons y.1 y.2)) hf (standardMollifier n) hε g

end PDE.Hyperbolic.FirstOrder
