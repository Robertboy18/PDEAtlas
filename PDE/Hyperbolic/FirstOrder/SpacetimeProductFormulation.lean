/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.SpacetimeProductTransport
import PDE.Spaces.Sobolev.Approximation.Mollification.JointCoefficientRepresentative

/-!
# The transport equation as a product-measure distribution identity

The four terms are scalar integrals: the time derivative of the test, the transport
term, the forcing, and the initial spatial pairing. All are proved integrable from
the Bochner L² and Sobolev coefficient hypotheses. Thus the product-measure identity
is equivalent to the formulation with spatial L² pairings.

Joint representatives are constructed from the Bochner curves and multiplier
classes. Coefficient derivatives are weak Sobolev derivatives, and representative
agreement holds almost everywhere in time and space.
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
local notation "ν" => volume.restrict (Ioc a b)
local notation "σ" => domainMeasure n univ

/-- The transport equation written entirely as integrals of scalar functions on the
time-space product, with the prescribed spatial initial datum. The coefficient `B`
represents the indicated weak derivative of `C`; that correspondence is supplied
separately when relating this predicate to a Sobolev coefficient field.

Each test is smooth, compactly supported, and supported before the terminal time.
Integrability of all four terms is part of the predicate. -/
def IsProductSpacetimeTransportWeakSolution
    (C B : Fin n → Fin m → Fin m → ℝ × ℝ^n → ℝ)
    (U F : Fin m → ℝ × ℝ^n → ℝ) (x₀ : H) (a b : ℝ) : Prop :=
  ∀ Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ),
    (∀ p, tsupport (Φ p) ⊆ {z | z.1 < b}) →
    Integrable (fun z ↦ ∑ p, U p z *
      (TestFunction.lineDerivCLM (k := ⊤) ℝ (1, 0) (Φ p)) z)
        ((volume.restrict (Ioc a b)).prod σ) ∧
    Integrable (fun z ↦ ∑ p, ∑ j, ∑ q, U q z *
      (C j p q z *
        (TestFunction.lineDerivCLM (k := ⊤) ℝ (0, EuclideanSpace.single j (1 : ℝ)) (Φ p)) z +
          B j p q z * Φ p z)) ((volume.restrict (Ioc a b)).prod σ) ∧
    Integrable (fun z ↦ ∑ p, F p z * Φ p z)
      ((volume.restrict (Ioc a b)).prod σ) ∧
    Integrable (fun x ↦ ∑ p, (x₀ p) x * Φ p (a, x)) σ ∧
    -(∫ z, ∑ p, U p z * (TestFunction.lineDerivCLM (k := ⊤) ℝ (1, 0) (Φ p)) z
      ∂(volume.restrict (Ioc a b)).prod σ) =
      (∫ z, ∑ p, ∑ j, ∑ q, U q z *
        (C j p q z *
          (TestFunction.lineDerivCLM (k := ⊤) ℝ (0, EuclideanSpace.single j (1 : ℝ)) (Φ p)) z +
            B j p q z * Φ p z) ∂(volume.restrict (Ioc a b)).prod σ) +
      (∫ z, ∑ p, F p z * Φ p z ∂(volume.restrict (Ioc a b)).prod σ) +
      (∫ x, ∑ p, (x₀ p) x * Φ p (a, x) ∂σ)

/-- For joint representatives of Bochner L² states and the Sobolev coefficient rows,
the product-measure distribution identity is equivalent to the formulation
with spatial L² pairings. Integrability follows from L² duality and the coefficient
multiplier estimates, including for the initial term. The weak state has no assumed
time derivative or pointwise initial value. -/
theorem isProductSpacetimeTransportWeakSolution_iff
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a ≤ b) (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {u f : ℝ → H} (hu : MemLp u 2 ν) (hf : MemLp f 2 ν) (U F : Fin m → ℝ × ℝ^n → ℝ)
    (hU : ∀ p, AEStronglyMeasurable (U p) ((ν).prod σ))
    (hF : ∀ p, AEStronglyMeasurable (F p) ((ν).prod σ))
    (hUsec : ∀ p, ∀ᵐ t ∂ν, (fun x ↦ U p (t, x)) =ᵐ[σ] (u t p : ℝ^n → ℝ))
    (hFsec : ∀ p, ∀ᵐ t ∂ν, (fun x ↦ F p (t, x)) =ᵐ[σ] (f t p : ℝ^n → ℝ))
    (C B : Fin n → Fin m → Fin m → ℝ × ℝ^n → ℝ)
    (hC : ∀ j p q, AEStronglyMeasurable (C j p q) ((ν).prod σ))
    (hB : ∀ j p q, AEStronglyMeasurable (B j p q) ((ν).prod σ))
    (hCsec : ∀ j p q, ∀ᵐ t ∂ν, (fun x ↦ C j p q (t, x)) =ᵐ[σ]
      ((A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) : ℝ^n → ℝ))
    (hBsec : ∀ j p q, ∀ᵐ t ∂ν, (fun x ↦ B j p q (t, x)) =ᵐ[σ]
      ((A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j) : ℝ^n → ℝ))
    (x₀ : H) :
    IsProductSpacetimeTransportWeakSolution C B U F x₀ a b ↔
      IsSpacetimeTransportWeakSolution A u f x₀ a b := by
  have htime (Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) :=
    integral_spacetime_test_pairing hu U hU hUsec (fun p ↦ TestFunction.lineDerivCLM ℝ (1, 0) (Φ p))
  have hspace (Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) :=
    integral_spacetime_transport_pairing A hA hab L hL hu U hU hUsec C B hC hB hCsec hBsec Φ
  have hload (Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) :=
    integral_spacetime_test_pairing hf F hF hFsec Φ
  constructor
  · intro hweak Φ hΦ
    have h := (hweak Φ hΦ).2.2.2.2
    rwa [(htime Φ).2, (hspace Φ).2, (hload Φ).2, (integral_spacetime_initial_pairing x₀ Φ a).2] at h
  · intro hweak Φ hΦ
    refine ⟨(htime Φ).1, (hspace Φ).1, (hload Φ).1,
      (integral_spacetime_initial_pairing x₀ Φ a).1, ?_⟩
    rw [(htime Φ).2, (hspace Φ).2, (hload Φ).2, (integral_spacetime_initial_pairing x₀ Φ a).2]
    exact hweak Φ hΦ

/-- A solution in the spatial-L² formulation has jointly measurable state,
forcing, coefficient, and weak-coefficient-derivative representatives satisfying the
product-measure equation. The state and forcing representatives are product-space L².
The coefficients need not be product-space L² on the unbounded spatial domain. -/
theorem exists_product_representatives_of_spacetime_weak_solution
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q, ContinuousOn (fun t ↦
      (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a ≤ b) (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {u f : ℝ → H} (hu : MemLp u 2 ν) (hf : MemLp f 2 ν) (x₀ : H)
    (hweak : IsSpacetimeTransportWeakSolution A u f x₀ a b) :
    ∃ (U F : Fin m → ℝ × ℝ^n → ℝ)
      (C B : Fin n → Fin m → Fin m → ℝ × ℝ^n → ℝ),
      (∀ p, StronglyMeasurable (U p) ∧ MemLp (U p) 2 ((ν).prod σ) ∧
        ∀ᵐ t ∂ν, (fun x ↦ U p (t, x)) =ᵐ[σ] (u t p : ℝ^n → ℝ)) ∧
      (∀ p, StronglyMeasurable (F p) ∧ MemLp (F p) 2 ((ν).prod σ) ∧
        ∀ᵐ t ∂ν, (fun x ↦ F p (t, x)) =ᵐ[σ] (f t p : ℝ^n → ℝ)) ∧
      (∀ j p q, StronglyMeasurable (C j p q) ∧ StronglyMeasurable (B j p q) ∧
        (∀ᵐ t ∂ν, (fun x ↦ C j p q (t, x)) =ᵐ[σ]
          ((A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) : ℝ^n → ℝ)) ∧
        (∀ᵐ t ∂ν, (fun x ↦ B j p q (t, x)) =ᵐ[σ]
          ((A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j) : ℝ^n → ℝ))) ∧
      IsProductSpacetimeTransportWeakSolution C B U F x₀ a b := by
  classical
  have hucoord (p : Fin m) : MemLp (fun t ↦ u t p) 2 ν := by
    simpa only [Function.comp_def, PiLp.proj_apply] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ D) p).comp_memLp' hu
  have hfcoord (p : Fin m) : MemLp (fun t ↦ f t p) 2 ν := by
    simpa only [Function.comp_def, PiLp.proj_apply] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ D) p).comp_memLp' hf
  choose U hU hUm hUsec using fun p ↦ (hucoord p).exists_jointRepresentative
  choose F hF hFm hFsec using fun p ↦ (hfcoord p).exists_jointRepresentative
  choose C B hC hB hCsec hBsec using fun j p q ↦
    exists_joint_coefficient_representatives hab (fun t ↦ A t j p q)
      (hA j p q) j L (fun t ht ↦ hL t ht j p q)
  refine ⟨U, F, C, B, (fun p ↦ ⟨hU p, hUm p, hUsec p⟩), (fun p ↦ ⟨hF p, hFm p, hFsec p⟩),
    (fun j p q ↦ ⟨hC j p q, hB j p q, hCsec j p q, hBsec j p q⟩), ?_⟩
  exact (isProductSpacetimeTransportWeakSolution_iff A hA hab L hL hu hf U F
    (fun p ↦ (hU p).aestronglyMeasurable) (fun p ↦ (hF p).aestronglyMeasurable)
    hUsec hFsec C B (fun j p q ↦ (hC j p q).aestronglyMeasurable)
    (fun j p q ↦ (hB j p q).aestronglyMeasurable) hCsec hBsec x₀).mpr hweak

end PDE.Hyperbolic.FirstOrder
