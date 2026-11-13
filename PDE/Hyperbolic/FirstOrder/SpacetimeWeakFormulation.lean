/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.SmoothFormulation
public import PDE.DistributionTheory.TestFunction.Slice

/-!
# Smooth spacetime tests for the transport equation

The test is a smooth compactly supported function on ℝ × ℝⁿ, supported before
its terminal time. Its time derivative is the directional derivative in `(1, 0)`.
The proper-slice operation gives a compactly supported smooth spatial function
at each time, and the canonical Sobolev embedding supplies its derivative rows.

The identity is written with spatial L² pairings. Thus its spatial term is
`sum p,j,q ∫ u_q (a_jpq ∂_j Φ_p + (∂_j a_jpq) Φ_p)` and its initial term is
`sum p ∫ x_p Φ_p(a, ·)`. The coefficient derivatives are their weak Sobolev derivatives.

External tensor products are admissible spacetime tests. Their slice and derivative
identities reduce the distribution identity to the smooth separated formulation, which
then extends to H¹ and `TimeTest` by the preceding density argument.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology Distributions ContDiff

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)

/-- Embed each spatial slice of a vector spacetime test in the H¹ graph
space. Compact support and smoothness follow from the canonical proper-slice operation. -/
def spacetimeTestH1Slice
    (Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) (t : ℝ) : V :=
  WithLp.toLp 2 (fun p ↦ globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ)
    (TestFunction.sliceRight t (Φ p)))

/-- The standard initial-value distribution identity, tested against all smooth compactly
supported spacetime functions whose support lies before `b`. Spatial integrals are
written as L² pairings of the slices and their Sobolev derivative rows.
Membership of the state and forcing in Bochner L² is supplied separately. -/
def IsSpacetimeTransportWeakSolution
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (u f : ℝ → H) (x : H) (a b : ℝ) : Prop :=
  ∀ Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ),
    (∀ p, tsupport (Φ p) ⊆ {z | z.1 < b}) →
    -(∫ t, inner ℝ (u t) (transportBaseCLM
        (spacetimeTestH1Slice (fun p ↦ TestFunction.lineDerivCLM ℝ (1, 0) (Φ p)) t))
          ∂volume.restrict (Ioc a b)) =
      (∫ t, transportTestFunctional (A t) (spacetimeTestH1Slice Φ t) (u t)
        ∂volume.restrict (Ioc a b)) +
      (∫ t, inner ℝ (f t) (transportBaseCLM (spacetimeTestH1Slice Φ t))
        ∂volume.restrict (Ioc a b)) +
      inner ℝ x (transportBaseCLM (spacetimeTestH1Slice Φ a))

/-- Slicing a separated spacetime test gives its time value times the spatial H¹ test. -/
private theorem spacetimeTestH1Slice_tensorProduct
    (ζ : 𝓓((⊤ : Opens ℝ), ℝ)) (ψ : Fin m → 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (t : ℝ) :
    spacetimeTestH1Slice (fun p ↦ TestFunction.tensorProduct ζ (ψ p)) t = ζ t •
      WithLp.toLp 2 (fun p ↦ globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) (ψ p)) := by
  apply PiLp.ext
  intro p
  change globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ)
      (TestFunction.sliceRight t (TestFunction.tensorProduct ζ (ψ p))) =
    ζ t • globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) (ψ p)
  rw [TestFunction.sliceRight_tensorProduct, globalTestFunctionToWkpOn_smul]

/-- The spacetime distribution formulation implies the `TimeTest × H¹`
formulation for L² states. The proof retains the prescribed initial boundary term.
No symmetry is needed for the formulation extension. -/
theorem IsSpacetimeTransportWeakSolution.timeTest (hab : a < b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {u f : ℝ → H} (hu : MemLp u 2 ν) (hf : MemLp f 2 ν) {x : H}
    (hweak : IsSpacetimeTransportWeakSolution A u f x a b) (φ : V) (τ : TimeTest a b) :
    -(∫ t, inner ℝ (u t) (transportBaseCLM φ) * τ.derivFun t ∂ν) =
      (∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν) +
      (∫ t, inner ℝ (f t) (transportBaseCLM φ) * τ.toFun t ∂ν) +
      inner ℝ x (transportBaseCLM φ) * τ.toFun a := by
  apply transport_timeTest_identity_of_smooth_tests hab A hA L hL hu hf x ?_ φ τ
  intro ψ
  dsimp only
  intro ζ hζ hζcs hζsupp
  let Z : 𝓓((⊤ : Opens ℝ), ℝ) := ⟨ζ, hζ, hζcs, subset_univ _⟩
  let Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ) := fun p ↦ TestFunction.tensorProduct Z (ψ p)
  have hsupp (p : Fin m) : tsupport (Φ p) ⊆ {z | z.1 < b} := by
    intro z hz
    exact hζsupp ((TestFunction.tsupport_tensorProduct_subset Z (ψ p) hz).1)
  have hd (t : ℝ) : (TestFunction.lineDerivCLM ℝ (1 : ℝ) Z :
      𝓓((⊤ : Opens ℝ), ℝ)) t = deriv ζ t := by
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
    change lineDeriv ℝ ζ t 1 = deriv ζ t
    rw [(hζ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    exact fderiv_apply_one_eq_deriv
  have hs (t : ℝ) : spacetimeTestH1Slice Φ t = ζ t • WithLp.toLp 2 (fun p ↦
        globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) (ψ p)) :=
    spacetimeTestH1Slice_tensorProduct Z ψ t
  have hds (t : ℝ) : spacetimeTestH1Slice (fun p ↦ TestFunction.lineDerivCLM ℝ (1, 0) (Φ p)) t =
      deriv ζ t • WithLp.toLp 2 (fun p ↦
        globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) (ψ p)) := by
    change spacetimeTestH1Slice (fun p ↦
      TestFunction.lineDerivCLM ℝ (1, 0) (TestFunction.tensorProduct Z (ψ p))) t = _
    simp only [TestFunction.lineDerivCLM_tensorProduct_fst, spacetimeTestH1Slice_tensorProduct, hd]
  have hscale (t c : ℝ) (v : V) : transportTestFunctional (A t) (c • v) (u t) =
        c * transportTestFunctional (A t) v (u t) := by
    rw [← transportTestInTestCLM_apply, map_smul, transportTestInTestCLM_apply, smul_eq_mul]
  have h := hweak Φ hsupp
  simpa only [hs, hds, hscale, map_smul, inner_smul_right, mul_comm] using h

end PDE.Hyperbolic.FirstOrder
