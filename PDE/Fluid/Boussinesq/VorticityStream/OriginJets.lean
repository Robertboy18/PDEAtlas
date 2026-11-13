/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.Model
public import PDE.FDeriv.PartialDeriv.HalfSpaceLimit
public import PDE.FDeriv.Reflection.Local
import PDE.Analysis.Calculus.HalfSpaceGluing

/-!
# Jets of the rescaled Boussinesq equations at the origin

In the variables `(ω, η, ξ) = (ω, θ_x, θ_y)` the dynamically rescaled equations read
`∂_t (ω, η, ξ) = (R_ω, R_η, R_ξ)` with transport `V = c_l x + ∇^⊥ψ`:

* `R_ω = c_ω ω + η - V·∇ω`,
* `R_η = (c_θ - ∂ₓV₁) η - ∂ₓV₂ ξ - V·∇η`,
* `R_ξ = (c_θ - ∂ᵧV₂) ξ - ∂ᵧV₁ η - V·∇ξ`,

where `R_η = ∂ₓR_θ` and `R_ξ = ∂ᵧR_θ` for `R_θ = c_θ θ - V·∇θ` when `η = θ_x`, `ξ = θ_y`
(`partialDeriv_temperatureTendency_eq`). For fields with the symmetry of Chen and Hou (`ω`, `η`
odd and `ξ` even in `x₁` with `ξ = 0` on the vertical axis, `ψ` odd and zero on the boundary),
the jets at the origin used in the proof of Part I, Lemma 4.7 (the identities (4.64)) depend
only on finitely many jets of the fields. With every jet taken as a limit from the open upper
half-plane, `ω_x(0)`, `η_x(0)`, `A = ω_xy(0)`, `q = η_xy(0)`, `r = ξ_xx(0)`,
`u_x(0) = -ψ_xy(0)` and `u_xy(0) = -ψ_xyy(0)`:

* `∂ₓR_ω(0) = (c_ω - c_l - u_x(0)) ω_x(0) + η_x(0)`,
* `∂ₓ∂ᵧR_ω(0) = (c_ω - 2 c_l) A - u_xy(0) ω_x(0) + q`,
* `∂ₓR_η(0) = (c_θ - 2 c_l - 2 u_x(0)) η_x(0)`,
* `∂ₓ∂ᵧR_η(0) = (c_θ - 3 c_l - u_x(0)) q - 2 u_xy(0) η_x(0)`,
* `∂ₓ²R_ξ(0) = (c_θ - 3 c_l - u_x(0)) r - 2 u_xy(0) η_x(0)`.

For a stream function of the vorticity, `-Δψ = ω` and `ψ_xxx(0) = 0` give `u_xy(0) = ω_x(0)`
(`tendsto_stream_xyy`). The first and third formulas are the trace ODEs of the normalization
(Part I, (2.9)-(2.10) and footnote 3); the others give the evolution (4.12) of the second-order
jets `ω_xy(0)`, `θ_xxy(0)` of a solution, the residual jets of a profile and, with `ψ` the profile
stream and `(ω, η, ξ)` a perturbation vanishing to second order, the jets of the local part of the
linearized operator (Part I, (4.63)-(4.64); Part II, (3.21)-(3.22) and Section 3.5). The fields
need only be regular up to the boundary near the origin (`IsSmoothToBoundary`).

## Main definitions and results

* `Boussinesq.rescaledVorticityTendency`, `rescaledEtaTendency`, `rescaledXiTendency`,
  `rescaledTemperatureTendency`.
* `Boussinesq.IsSmoothToBoundary`, `IsOddJetField`, `IsEvenAxisJetField`, `IsJetStream`.
* `tendsto_partialDeriv_vorticityTendency`, `tendsto_mixedDeriv_vorticityTendency`,
  `tendsto_partialDeriv_etaTendency`, `tendsto_mixedDeriv_etaTendency`,
  `tendsto_partialDeriv_partialDeriv_xiTendency`, `IsJetStream.tendsto_stream_xyy`.

## How it works

Each formula is proved on the open upper half-plane and then passed to the limit at the origin. At
points of the open half-plane we expand the derivative of the tendency by the product rule. Every
jet in the expansion has a limit at the origin, because the field extends to a `C^k` function on the
closed half-plane (`IsSmoothToBoundary.exists_tendsto`). The symmetries make many of these limits
zero. A derivative that is odd in `x₁` vanishes on the vertical axis, so its limit is zero
(`IsSmoothToBoundary.tendsto_zero_of_parity`); the same holds for vertical derivatives of a field
vanishing on that axis (`IsSmoothToBoundary.tendsto_zero_of_axis`) and for horizontal derivatives of
a stream function vanishing on the boundary (`IsJetStream.tendsto_x`, `IsJetStream.tendsto_xxx`).
The limit of the expansion is then computed term by term. For `IsJetStream.tendsto_stream_xyy` we
differentiate `-Δψ = ω` in `x` on the open half-plane and use `ψ_xxx(0) = 0`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.8)-(2.10) and
  footnote 3; Section 4.2.1, (4.12); Section 4.4, Lemma 4.7 and (4.63)-(4.64).
  <https://arxiv.org/abs/2210.07191v4>
* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Section 3.3, (3.21)-(3.23),
  and Section 3.5.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open Filter Set PDE PDE.Common IncompressibleFlow
open PDE (laplacian advectiveDerivative)
open scoped Topology

namespace Boussinesq

set_option linter.missingDocs true

/-- The right side `c_ω ω + η - (c_l x + ∇^⊥ψ)·∇ω` of the rescaled vorticity equation, with
`η = θ_x`. -/
def rescaledVorticityTendency (cl cw : ℝ) (ω η ψ : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  cw * ω x + η x - advectiveDerivative (fun y ↦ cl • y + planarStreamVelocity ψ y) ω x

/-- The right side `c_θ θ - (c_l x + ∇^⊥ψ)·∇θ` of the rescaled temperature equation. -/
def rescaledTemperatureTendency (cl cθ : ℝ) (θ ψ : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  cθ * θ x - advectiveDerivative (fun y ↦ cl • y + planarStreamVelocity ψ y) θ x

/-- The right side `(c_θ - c_l + ψ_xy) η - ψ_xx ξ - V·∇η` of the equation of `η = θ_x`, with
`V = c_l x + ∇^⊥ψ`. -/
def rescaledEtaTendency (cl cθ : ℝ) (η ξ ψ : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  (cθ - cl + (∂[0] (∂[1] ψ)) x) * η x - (∂[0] (∂[0] ψ)) x * ξ x -
    advectiveDerivative (fun y ↦ cl • y + planarStreamVelocity ψ y) η x

/-- The right side `(c_θ - c_l - ψ_yx) ξ + ψ_yy η - V·∇ξ` of the equation of `ξ = θ_y`, with
`V = c_l x + ∇^⊥ψ`. -/
def rescaledXiTendency (cl cθ : ℝ) (η ξ ψ : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  (cθ - cl - (∂[1] (∂[0] ψ)) x) * ξ x + (∂[1] (∂[1] ψ)) x * η x -
    advectiveDerivative (fun y ↦ cl • y + planarStreamVelocity ψ y) ξ x

/-- The restriction of `f` to the open upper half-plane extends to a function `C^k` on the
closed upper half-plane. -/
def IsSmoothToBoundary (k : ℕ) (f : ℝ^2 → ℝ) : Prop :=
  ∃ F : ℝ^2 → ℝ, ContDiffOn ℝ k F {x | 0 ≤ x 1} ∧ EqOn f F upperHalfPlane

/-- An odd field for the jet computations: smooth up to the boundary and odd in `x₁`. -/
structure IsOddJetField (k : ℕ) (f : ℝ^2 → ℝ) : Prop where
  /-- Regularity up to the boundary. -/
  smooth : IsSmoothToBoundary k f
  /-- Oddness in `x₁`. -/
  odd : IsReflectionEigenfunctionOn upperHalfPlane 0 (-1) f

/-- An even field vanishing on the vertical axis: smooth up to the boundary, even in `x₁` and
zero on the vertical axis. -/
structure IsEvenAxisJetField (k : ℕ) (f : ℝ^2 → ℝ) : Prop where
  /-- Regularity up to the boundary. -/
  smooth : IsSmoothToBoundary k f
  /-- Evenness in `x₁`. -/
  even : IsReflectionEigenfunctionOn upperHalfPlane 0 1 f
  /-- Vanishing on the vertical axis. -/
  axis : ∀ x ∈ upperHalfPlane, x 0 = 0 → f x = 0

/-- A stream function for the jet computations: `C⁴` on the closed upper half-plane, odd in `x₁`
and zero on the boundary. -/
structure IsJetStream (ψ : ℝ^2 → ℝ) : Prop where
  /-- Regularity up to the boundary. -/
  contDiffOn : ContDiffOn ℝ 4 ψ {x | 0 ≤ x 1}
  /-- Oddness in `x₁`. -/
  odd : IsReflectionEigenfunctionOn upperHalfPlane 0 (-1) ψ
  /-- The boundary condition. -/
  boundary : ∀ x : ℝ^2, x 1 = 0 → ψ x = 0

section Limits

/-- The open upper half-plane lies in the closed one. -/
theorem upperHalfPlane_subset_closed : upperHalfPlane ⊆ {x : ℝ^2 | 0 ≤ x 1} :=
  fun x (hx : 0 < x 1) ↦ (le_of_lt hx : 0 ≤ x 1)

/-- The reflection `x₀ ↦ -x₀` maps the open upper half-plane into itself. -/
theorem coordinateReflection_mem_upperHalfPlane {x : ℝ^2} (hx : x ∈ upperHalfPlane) :
    coordinateReflection (0 : Fin 2) x ∈ upperHalfPlane :=
  (coordinateReflection_mem_coordinateUpperHalfSpace_iff_of_ne 0 1 (by decide) x).2 hx

/-- The origin is a limit of points of the vertical axis in the open upper half-plane. -/
theorem neBot_upperHalfPlane_axis :
    (𝓝[upperHalfPlane ∩ {x : ℝ^2 | x 0 = 0}] (0 : ℝ^2)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  refine ⟨EuclideanSpace.single 1 (ε / 2), ⟨?_, ?_⟩, ?_⟩
  · change 0 < (EuclideanSpace.single (1 : Fin 2) (ε / 2) : ℝ^2) 1
    simp [hε]
  · simp
  · rw [dist_zero_left, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith

/-- The origin is a limit point of the open upper half-plane. -/
theorem neBot_upperHalfPlane : (𝓝[upperHalfPlane] (0 : ℝ^2)).NeBot :=
  neBot_upperHalfPlane_axis.mono (nhdsWithin_mono _ inter_subset_left)

variable {f : ℝ^2 → ℝ}

/-- The iterated partial derivatives of a function `C^k` on the closed upper half-plane have limits
at the origin from the open upper half-plane. -/
theorem tendsto_iteratedPartialDeriv_upperHalfPlane (l : List (Fin 2))
    (hf : ContDiffOn ℝ l.length f {x | 0 ≤ x 1}) :
    Tendsto (iteratedPartialDeriv l f) (𝓝[upperHalfPlane] 0)
      (𝓝 (iteratedPartialDerivWithin l f {x | 0 ≤ x 1} 0)) :=
  tendsto_iteratedPartialDeriv isOpen_upperHalfPlane upperHalfPlane_subset_closed
    (PDE.Analysis.uniqueDiffOn_coordinateHalfSpace 1) l hf (by simp)

/-- An iterated partial derivative that is odd in `x₁` tends to zero at the origin. -/
theorem tendsto_iteratedPartialDeriv_of_parity (l : List (Fin 2))
    (hf : ContDiffOn ℝ l.length f {x | 0 ≤ x 1}) {ε : ℝ}
    (hpar : IsReflectionEigenfunctionOn upperHalfPlane 0 ε f) (hε : ε * (-1) ^ l.count 0 = -1) :
    Tendsto (iteratedPartialDeriv l f) (𝓝[upperHalfPlane] 0) (𝓝 0) := by
  have ht := tendsto_iteratedPartialDeriv_upperHalfPlane l hf
  have hp := hpar.iteratedPartialDeriv isOpen_upperHalfPlane
    (fun _ hx ↦ coordinateReflection_mem_upperHalfPlane hx) l
    (hf.mono upperHalfPlane_subset_closed)
  rw [hε] at hp
  rwa [hp.eq_zero_of_tendsto neBot_upperHalfPlane_axis ht] at ht

/-- Vertical derivatives of a function vanishing on the vertical axis tend to zero at the
origin. -/
theorem tendsto_iteratedPartialDeriv_replicate_one {k : ℕ}
    (hf : ContDiffOn ℝ k f {x | 0 ≤ x 1}) (hax : ∀ x ∈ upperHalfPlane, x 0 = 0 → f x = 0) :
    Tendsto (iteratedPartialDeriv (List.replicate k 1) f) (𝓝[upperHalfPlane] 0) (𝓝 0) := by
  have ht := tendsto_iteratedPartialDeriv_upperHalfPlane (List.replicate k 1) (by simpa using hf)
  have hz := iteratedPartialDeriv_replicate_eq_zero (i := 0) (j := 1) (by decide)
    isOpen_upperHalfPlane (hf.mono upperHalfPlane_subset_closed) hax
  rwa [eq_zero_of_tendsto_of_eqOn_hyperplane hz neBot_upperHalfPlane_axis ht] at ht

/-- Horizontal derivatives of a function vanishing on the boundary tend to zero at the origin. -/
theorem tendsto_iteratedPartialDeriv_replicate_zero {k : ℕ}
    (hf : ContDiffOn ℝ k f {x | 0 ≤ x 1}) (hb : ∀ x : ℝ^2, x 1 = 0 → f x = 0) :
    Tendsto (iteratedPartialDeriv (List.replicate k 0) f) (𝓝[upperHalfPlane] 0) (𝓝 0) := by
  have ht := tendsto_iteratedPartialDeriv_upperHalfPlane (List.replicate k 0) (by simpa using hf)
  rwa [iteratedPartialDerivWithin_replicate_eq_zero (c := 1) (j := 0) (by decide) hf hb 0
    (by simp)] at ht

/-- Mixed partial derivatives commute on the open upper half-plane. -/
theorem eqOn_partialDeriv_comm (hf : ContDiffOn ℝ 2 f upperHalfPlane) :
    EqOn (∂[1] (∂[0] f)) (∂[0] (∂[1] f)) upperHalfPlane := fun _ hx ↦
  partialDeriv_partialDeriv_comm_at 1 0 (hf.contDiffAt (isOpen_upperHalfPlane.mem_nhds hx))

/-- Lowering the order of a `C^k` hypothesis to the length of a word. -/
theorem _root_.ContDiffOn.of_length {s : Set (ℝ^2)} {k : ℕ} (hf : ContDiffOn ℝ k f s)
    (l : List (Fin 2)) (hl : l.length ≤ k) : ContDiffOn ℝ l.length f s :=
  hf.of_le (by exact_mod_cast hl)

/-- The coordinates tend to `0` at the origin from the open upper half-plane. -/
theorem tendsto_coord_upperHalfPlane (i : Fin 2) :
    Tendsto (fun x : ℝ^2 ↦ x i) (𝓝[upperHalfPlane] 0) (𝓝 0) := by
  have : Tendsto (fun x : ℝ^2 ↦ x i) (𝓝 0) (𝓝 ((0 : ℝ^2) i)) :=
    (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).continuous.tendsto 0
  simpa using this.mono_left nhdsWithin_le_nhds

end Limits

section Smooth

variable {f : ℝ^2 → ℝ} {k : ℕ}

/-- A function `C^k` on the closed upper half-plane is `C^k` up to the boundary. -/
theorem IsSmoothToBoundary.of_contDiffOn (hf : ContDiffOn ℝ k f {x | 0 ≤ x 1}) :
    IsSmoothToBoundary k f :=
  ⟨f, hf, fun _ _ ↦ rfl⟩

/-- A function `C^k` up to the boundary is `C^m` up to the boundary for `m ≤ k`. -/
theorem IsSmoothToBoundary.mono (hf : IsSmoothToBoundary k f) {m : ℕ} (hm : m ≤ k) :
    IsSmoothToBoundary m f := by
  obtain ⟨F, hF, hfF⟩ := hf
  exact ⟨F, hF.of_le (by exact_mod_cast hm), hfF⟩

/-- A function `C^k` up to the boundary is `C^k` on the open upper half-plane. -/
theorem IsSmoothToBoundary.contDiffOn (hf : IsSmoothToBoundary k f) :
    ContDiffOn ℝ k f upperHalfPlane := by
  obtain ⟨F, hF, hfF⟩ := hf
  exact (hF.mono upperHalfPlane_subset_closed).congr fun x hx ↦ hfF hx

/-- Iterated partial derivatives of order at most `k` have limits at the origin. -/
theorem IsSmoothToBoundary.exists_tendsto (hf : IsSmoothToBoundary k f) (l : List (Fin 2))
    (hl : l.length ≤ k) : ∃ L, Tendsto (iteratedPartialDeriv l f) (𝓝[upperHalfPlane] 0) (𝓝 L) := by
  obtain ⟨F, hF, hfF⟩ := hf
  refine ⟨_, (tendsto_iteratedPartialDeriv_upperHalfPlane l (hF.of_length l hl)).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ((eventuallyEq_of_mem (isOpen_upperHalfPlane.mem_nhds hx) hfF).iteratedPartialDeriv
    l).eq_of_nhds.symm

/-- The partial derivatives of a function `C^{k+1}` up to the boundary are `C^k` up to the
boundary. -/
theorem IsSmoothToBoundary.partialDeriv (hf : IsSmoothToBoundary (k + 1) f) (i : Fin 2) :
    IsSmoothToBoundary k (∂[i] f) := by
  obtain ⟨F, hF, hfF⟩ := hf
  refine ⟨partialDerivWithin i F {x | 0 ≤ x 1},
    hF.partialDerivWithin i (PDE.Analysis.uniqueDiffOn_coordinateHalfSpace 1) (by norm_cast), ?_⟩
  have h := eqOn_iteratedPartialDeriv isOpen_upperHalfPlane upperHalfPlane_subset_closed
    (PDE.Analysis.uniqueDiffOn_coordinateHalfSpace 1) [i] (m := k) (by simpa [add_comm] using hF)
  intro x hx
  have h1 : iteratedPartialDeriv [i] F x = partialDerivWithin i F {x | 0 ≤ x 1} x := h.1 hx
  rw [← h1]
  exact partialDeriv_eq_of_fderiv_eq
    ((eventuallyEq_of_mem (isOpen_upperHalfPlane.mem_nhds hx) hfF).fderiv_eq (𝕜 := ℝ)) i

/-- For a function `C^k` up to the boundary, the iterated partial derivatives along words of length
at most `k - 1` are differentiable on the open upper half-plane. -/
theorem IsSmoothToBoundary.differentiableAt (hf : IsSmoothToBoundary k f) (l : List (Fin 2))
    (hk : l.length + 1 ≤ k) {x : ℝ^2} (hx : x ∈ upperHalfPlane) :
    DifferentiableAt ℝ (iteratedPartialDeriv l f) x := by
  have h := contDiffOn_iteratedPartialDeriv isOpen_upperHalfPlane l (m := 1)
    (hf.contDiffOn.of_le (by exact_mod_cast hk))
  exact (h.differentiableOn (by norm_num) x hx).differentiableAt
    (isOpen_upperHalfPlane.mem_nhds hx)

/-- An iterated partial derivative that is odd in `x₁` tends to zero at the origin. -/
theorem IsSmoothToBoundary.tendsto_zero_of_parity (hf : IsSmoothToBoundary k f)
    (l : List (Fin 2)) (hl : l.length ≤ k) {ε : ℝ}
    (hpar : IsReflectionEigenfunctionOn upperHalfPlane 0 ε f) (hε : ε * (-1) ^ l.count 0 = -1) :
    Tendsto (iteratedPartialDeriv l f) (𝓝[upperHalfPlane] 0) (𝓝 0) := by
  obtain ⟨L, ht⟩ := hf.exists_tendsto l hl
  have hp := hpar.iteratedPartialDeriv isOpen_upperHalfPlane
    (fun _ hx ↦ coordinateReflection_mem_upperHalfPlane hx) l
    (hf.contDiffOn.of_le (by exact_mod_cast hl))
  rw [hε] at hp
  rwa [hp.eq_zero_of_tendsto neBot_upperHalfPlane_axis ht] at ht

/-- Vertical derivatives of a function vanishing on the vertical axis tend to zero at the
origin. -/
theorem IsSmoothToBoundary.tendsto_zero_of_axis (hf : IsSmoothToBoundary k f)
    (hax : ∀ x ∈ upperHalfPlane, x 0 = 0 → f x = 0) :
    Tendsto (iteratedPartialDeriv (List.replicate k 1) f) (𝓝[upperHalfPlane] 0) (𝓝 0) := by
  obtain ⟨L, ht⟩ := hf.exists_tendsto (List.replicate k 1) (by simp)
  have hz := iteratedPartialDeriv_replicate_eq_zero (i := 0) (j := 1) (by decide)
    isOpen_upperHalfPlane hf.contDiffOn hax
  rwa [eq_zero_of_tendsto_of_eqOn_hyperplane hz neBot_upperHalfPlane_axis ht] at ht

end Smooth

/-- An odd jet field of order `k` is an odd jet field of every order `m ≤ k`. -/
theorem IsOddJetField.mono {f : ℝ^2 → ℝ} {k m : ℕ} (hf : IsOddJetField k f) (hm : m ≤ k) :
    IsOddJetField m f := ⟨hf.smooth.mono hm, hf.odd⟩

/-- An even jet field of order `k` vanishing on the axis is one of every order `m ≤ k`. -/
theorem IsEvenAxisJetField.mono {f : ℝ^2 → ℝ} {k m : ℕ} (hf : IsEvenAxisJetField k f)
    (hm : m ≤ k) : IsEvenAxisJetField m f := ⟨hf.smooth.mono hm, hf.even, hf.axis⟩

/-- The horizontal derivative of an even field vanishing on the axis is odd, and the vertical one
is even and vanishes on the axis. -/
theorem IsEvenAxisJetField.partialDeriv_zero {f : ℝ^2 → ℝ} {k : ℕ}
    (hf : IsEvenAxisJetField (k + 1) f) : IsOddJetField k (∂[0] f) := by
  refine ⟨hf.smooth.partialDeriv 0, ?_⟩
  have := hf.even.partialDeriv_same isOpen_upperHalfPlane
    (fun _ hx ↦ coordinateReflection_mem_upperHalfPlane hx)
    (hf.smooth.contDiffOn.differentiableOn (by norm_cast))
  simpa using this

/-- The vertical derivative `∂₁ f` of an even jet field of order `k + 1` vanishing on the axis is an
even jet field of order `k` vanishing on the axis. -/
theorem IsEvenAxisJetField.partialDeriv_one {f : ℝ^2 → ℝ} {k : ℕ}
    (hf : IsEvenAxisJetField (k + 1) f) : IsEvenAxisJetField k (∂[1] f) := by
  have hd : DifferentiableOn ℝ f upperHalfPlane :=
    hf.smooth.contDiffOn.differentiableOn (by norm_cast)
  refine ⟨hf.smooth.partialDeriv 1, hf.even.partialDeriv_of_ne isOpen_upperHalfPlane
    (fun _ hx ↦ coordinateReflection_mem_upperHalfPlane hx) hd (by decide), fun x hx hx0 ↦ ?_⟩
  exact partialDeriv_eq_zero_of_eqOn_hyperplane (i := 0) (j := 1) (by decide)
    isOpen_upperHalfPlane hf.axis hx hx0 ((hd x hx).differentiableAt
      (isOpen_upperHalfPlane.mem_nhds hx))

/-- The advective derivative along `c_l x + ∇^⊥ψ` in coordinates. -/
theorem advectiveDerivative_rescaled_eq (cl : ℝ) (ψ f : ℝ^2 → ℝ) (x : ℝ^2) :
    advectiveDerivative (fun y ↦ cl • y + planarStreamVelocity ψ y) f x =
      (cl * x 0 - (∂[1] ψ) x) * (∂[0] f) x + (cl * x 1 + (∂[0] ψ) x) * (∂[1] f) x := by
  rw [advectiveDerivative_eq_sum_mul_partialDeriv, Fin.sum_univ_two]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, planarStreamVelocity,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The temperature tendency in coordinates. -/
theorem rescaledTemperatureTendency_eq (cl cθ : ℝ) (θ ψ : ℝ^2 → ℝ) :
    rescaledTemperatureTendency cl cθ θ ψ = fun y ↦ cθ * θ y -
      ((cl * y 0 - (∂[1] ψ) y) * (∂[0] θ) y + (cl * y 1 + (∂[0] ψ) y) * (∂[1] θ) y) := by
  funext y
  rw [rescaledTemperatureTendency, advectiveDerivative_rescaled_eq]

/-- The vorticity tendency in coordinates. -/
private theorem rescaledVorticityTendency_eq (cl cw : ℝ) (ω η ψ : ℝ^2 → ℝ) :
    rescaledVorticityTendency cl cw ω η ψ = fun y ↦ cw * ω y + η y -
      ((cl * y 0 - (∂[1] ψ) y) * (∂[0] ω) y + (cl * y 1 + (∂[0] ψ) y) * (∂[1] ω) y) := by
  funext y
  rw [rescaledVorticityTendency, advectiveDerivative_rescaled_eq]

namespace IsJetStream

variable {ψ : ℝ^2 → ℝ} (hψ : IsJetStream ψ)
include hψ

/-- A jet stream function is `C⁴` up to the boundary. -/
theorem smooth : IsSmoothToBoundary 4 ψ := IsSmoothToBoundary.of_contDiffOn hψ.contDiffOn

/-- The iterated partial derivatives of order at most three of a jet stream function are
differentiable on the open upper half-plane. -/
theorem differentiableAt (l : List (Fin 2)) (hl : l.length ≤ 3) {x : ℝ^2}
    (hx : x ∈ upperHalfPlane) : DifferentiableAt ℝ (iteratedPartialDeriv l ψ) x :=
  hψ.smooth.differentiableAt l (by omega) hx

/-- `ψ_x → 0`: the stream function vanishes on the boundary. -/
theorem tendsto_x : Tendsto (∂[0] ψ) (𝓝[upperHalfPlane] 0) (𝓝 0) :=
  tendsto_iteratedPartialDeriv_replicate_zero (k := 1) (hψ.contDiffOn.of_le (by norm_num))
    hψ.boundary

/-- `ψ_xxx → 0`: the stream function vanishes on the boundary. -/
theorem tendsto_xxx : Tendsto (∂[0] (∂[0] (∂[0] ψ))) (𝓝[upperHalfPlane] 0) (𝓝 0) :=
  tendsto_iteratedPartialDeriv_replicate_zero (k := 3) (hψ.contDiffOn.of_le (by norm_num))
    hψ.boundary

/-- A derivative of `ψ` with an even number of horizontal derivatives tends to zero. -/
theorem tendsto_of_parity (l : List (Fin 2)) (hl : l.length ≤ 4) (he : Even (l.count 0)) :
    Tendsto (iteratedPartialDeriv l ψ) (𝓝[upperHalfPlane] 0) (𝓝 0) :=
  hψ.smooth.tendsto_zero_of_parity l hl hψ.odd (by rw [he.neg_one_pow]; ring)

/-- The iterated partial derivatives of order at most four of a jet stream function have limits at
the origin. -/
theorem exists_tendsto (l : List (Fin 2)) (hl : l.length ≤ 4) :
    ∃ L, Tendsto (iteratedPartialDeriv l ψ) (𝓝[upperHalfPlane] 0) (𝓝 L) :=
  hψ.smooth.exists_tendsto l hl

/-- `∂₁ ∂₀` and `∂₀ ∂₁` agree on the open upper half-plane on the iterated partial derivatives of
order at most two of a jet stream function. -/
theorem eqOn_comm (l : List (Fin 2)) (hl : l.length ≤ 2) :
    EqOn (∂[1] (∂[0] (iteratedPartialDeriv l ψ))) (∂[0] (∂[1] (iteratedPartialDeriv l ψ)))
      upperHalfPlane :=
  eqOn_partialDeriv_comm (contDiffOn_iteratedPartialDeriv isOpen_upperHalfPlane l (m := 2)
    (hψ.smooth.contDiffOn.of_le (by exact_mod_cast (by omega))))

/-- **`u_xy(0) = ω_x(0)`**: by `-Δψ = ω` and `ψ_xxx(0) = 0`, the third derivative `ψ_xyy` tends to
`-ω_x(0)` at the origin. -/
theorem tendsto_stream_xyy {ω : ℝ^2 → ℝ} (hpoisson : ∀ x ∈ upperHalfPlane, -laplacian ψ x = ω x)
    {ωx : ℝ} (hωx : Tendsto (∂[0] ω) (𝓝[upperHalfPlane] 0) (𝓝 ωx)) :
    Tendsto (∂[0] (∂[1] (∂[1] ψ))) (𝓝[upperHalfPlane] 0) (𝓝 (-ωx)) := by
  have hH := isOpen_upperHalfPlane
  have hlap : EqOn (fun x ↦ (∂[0] (∂[0] ψ)) x + (∂[1] (∂[1] ψ)) x) (fun x ↦ -ω x)
      upperHalfPlane := fun x hx ↦ by
    have := hpoisson x hx
    simp only [laplacian, Fin.sum_univ_two] at this
    simp only
    linarith
  have h1 := eqOn_partialDeriv hH hlap 0
  have hd : ∀ (l : List (Fin 2)), l.length = 2 →
      DifferentiableOn ℝ (iteratedPartialDeriv l ψ) upperHalfPlane := fun l hl ↦
    (contDiffOn_iteratedPartialDeriv hH l (m := 1)
      (by rw [hl]; exact hψ.smooth.contDiffOn.of_le (by norm_num))).differentiableOn
      (by norm_num)
  have hd00 : DifferentiableOn ℝ (∂[0] (∂[0] ψ)) upperHalfPlane := hd [0, 0] rfl
  have hd11 : DifferentiableOn ℝ (∂[1] (∂[1] ψ)) upperHalfPlane := hd [1, 1] rfl
  have h2 := eqOn_partialDeriv_add hH hd00 hd11 0
  have hrel : ∀ x ∈ upperHalfPlane, (∂[0] (∂[1] (∂[1] ψ))) x =
      -(∂[0] ω) x - (∂[0] (∂[0] (∂[0] ψ))) x := fun x hx ↦ by
    have e1 := h1 hx
    rw [h2 hx] at e1
    have e2 : (∂[0] (fun x ↦ -ω x)) x = -(∂[0] ω) x := partialDeriv_neg
    simp only at e1
    rw [e2] at e1
    linarith
  rw [← sub_zero (-ωx)]
  exact (hωx.neg.sub hψ.tendsto_xxx).congr'
    (eventually_nhdsWithin_of_forall fun x hx ↦ (hrel x hx).symm)

end IsJetStream

section Jets

variable {ω η ξ ψ : ℝ^2 → ℝ}

/-- **The first-order vorticity trace**: `∂ₓR_ω → (c_ω - c_l - u_x(0)) ω_x(0) + η_x(0)`. -/
theorem tendsto_partialDeriv_vorticityTendency (cl cw : ℝ) (hω : IsOddJetField 2 ω)
    (hη : IsSmoothToBoundary 1 η) (hψ : IsJetStream ψ) {ωx ηx ux : ℝ}
    (hωx : Tendsto (∂[0] ω) (𝓝[upperHalfPlane] 0) (𝓝 ωx))
    (hηx : Tendsto (∂[0] η) (𝓝[upperHalfPlane] 0) (𝓝 ηx))
    (hux : Tendsto (∂[0] (∂[1] ψ)) (𝓝[upperHalfPlane] 0) (𝓝 (-ux))) :
    Tendsto (∂[0] (rescaledVorticityTendency cl cw ω η ψ)) (𝓝[upperHalfPlane] 0)
      (𝓝 ((cw - cl - ux) * ωx + ηx)) := by
  have hexp : ∀ x ∈ upperHalfPlane, (∂[0] (rescaledVorticityTendency cl cw ω η ψ)) x =
      cw * (∂[0] ω) x + (∂[0] η) x -
        ((cl - (∂[0] (∂[1] ψ)) x) * (∂[0] ω) x + (cl * x 0 - (∂[1] ψ) x) * (∂[0] (∂[0] ω)) x +
          ((∂[0] (∂[0] ψ)) x * (∂[1] ω) x +
            (cl * x 1 + (∂[0] ψ) x) * (∂[0] (∂[1] ω)) x)) := by
    intro x hx
    have dc (i : Fin 2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y i) x :=
      (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiableAt
    have d1 : DifferentiableAt ℝ ω x := hω.smooth.differentiableAt [] (by norm_num) hx
    have dω1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] ω) x :=
      hω.smooth.differentiableAt [i] (by norm_num) hx
    have d4 : DifferentiableAt ℝ η x := hη.differentiableAt [] (by norm_num) hx
    have dψ1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] ψ) x := hψ.differentiableAt [i] (by norm_num) hx
    rw [rescaledVorticityTendency_eq]
    simp (disch := fun_prop) only [partialDeriv_add, partialDeriv_sub, partialDeriv_mul,
      partialDeriv_coord]
    simp
  have t0 := tendsto_coord_upperHalfPlane 0
  have t1 := tendsto_coord_upperHalfPlane 1
  obtain ⟨L₁, t2⟩ := hω.smooth.exists_tendsto [0, 0] (by simp)
  obtain ⟨L₂, t3⟩ := hω.smooth.exists_tendsto [0, 1] (by simp)
  have tω1 := hω.smooth.tendsto_zero_of_parity [1] (by simp) hω.odd (by simp)
  have tψ1 := hψ.tendsto_of_parity [1] (by simp) (by decide)
  have tψ00 := hψ.tendsto_of_parity [0, 0] (by simp) (by decide)
  have hlim := ((hωx.const_mul cw).add hηx).sub
    ((((tendsto_const_nhds (x := cl)).sub hux).mul hωx).add
      (((t0.const_mul cl).sub tψ1).mul t2) |>.add
      ((tψ00.mul tω1).add (((t1.const_mul cl).add hψ.tendsto_x).mul t3)))
  convert hlim.congr' (eventually_nhdsWithin_of_forall fun x hx ↦ (hexp x hx).symm) using 2
  ring

/-- **The mixed vorticity jet**: `∂ₓ∂ᵧR_ω → (c_ω - 2 c_l) ω_xy(0) - u_xy(0) ω_x(0) + η_xy(0)`. -/
theorem tendsto_mixedDeriv_vorticityTendency (cl cw : ℝ) (hω : IsOddJetField 3 ω)
    (hη : IsSmoothToBoundary 2 η) (hψ : IsJetStream ψ) {ωx A q ux uxy : ℝ}
    (hωx : Tendsto (∂[0] ω) (𝓝[upperHalfPlane] 0) (𝓝 ωx))
    (hA : Tendsto (∂[0] (∂[1] ω)) (𝓝[upperHalfPlane] 0) (𝓝 A))
    (hq : Tendsto (∂[0] (∂[1] η)) (𝓝[upperHalfPlane] 0) (𝓝 q))
    (hux : Tendsto (∂[0] (∂[1] ψ)) (𝓝[upperHalfPlane] 0) (𝓝 (-ux)))
    (huxy : Tendsto (∂[0] (∂[1] (∂[1] ψ))) (𝓝[upperHalfPlane] 0) (𝓝 (-uxy))) :
    Tendsto (∂[0] (∂[1] (rescaledVorticityTendency cl cw ω η ψ))) (𝓝[upperHalfPlane] 0)
      (𝓝 ((cw - 2 * cl) * A - uxy * ωx + q)) := by
  set E₁ : ℝ^2 → ℝ := fun y ↦ cw * (∂[1] ω) y + (∂[1] η) y -
    (-(∂[1] (∂[1] ψ)) y * (∂[0] ω) y + (cl * y 0 - (∂[1] ψ) y) * (∂[1] (∂[0] ω)) y +
      ((cl + (∂[1] (∂[0] ψ)) y) * (∂[1] ω) y + (cl * y 1 + (∂[0] ψ) y) * (∂[1] (∂[1] ω)) y))
    with hE₁
  have hexp1 : ∀ x ∈ upperHalfPlane,
      (∂[1] (rescaledVorticityTendency cl cw ω η ψ)) x = E₁ x := by
    intro x hx
    have dc (i : Fin 2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y i) x :=
      (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiableAt
    have d1 : DifferentiableAt ℝ ω x := hω.smooth.differentiableAt [] (by norm_num) hx
    have dω1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] ω) x :=
      hω.smooth.differentiableAt [i] (by norm_num) hx
    have d4 : DifferentiableAt ℝ η x := hη.differentiableAt [] (by norm_num) hx
    have dψ1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] ψ) x := hψ.differentiableAt [i] (by norm_num) hx
    rw [rescaledVorticityTendency_eq, hE₁]
    simp (disch := fun_prop) only [partialDeriv_add, partialDeriv_sub, partialDeriv_mul,
      partialDeriv_coord]
    simp
  have hexp2 : ∀ x ∈ upperHalfPlane, (∂[0] E₁) x =
      cw * (∂[0] (∂[1] ω)) x + (∂[0] (∂[1] η)) x -
        (-(∂[0] (∂[1] (∂[1] ψ))) x * (∂[0] ω) x - (∂[1] (∂[1] ψ)) x * (∂[0] (∂[0] ω)) x +
          ((cl - (∂[0] (∂[1] ψ)) x) * (∂[1] (∂[0] ω)) x +
            (cl * x 0 - (∂[1] ψ) x) * (∂[0] (∂[1] (∂[0] ω))) x) +
          ((∂[0] (∂[1] (∂[0] ψ))) x * (∂[1] ω) x + (cl + (∂[1] (∂[0] ψ)) x) * (∂[0] (∂[1] ω)) x +
            ((∂[0] (∂[0] ψ)) x * (∂[1] (∂[1] ω)) x +
              (cl * x 1 + (∂[0] ψ) x) * (∂[0] (∂[1] (∂[1] ω))) x))) := by
    intro x hx
    have dc (i : Fin 2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y i) x :=
      (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiableAt
    have dω1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] ω) x :=
      hω.smooth.differentiableAt [i] (by norm_num) hx
    have dψ1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] ψ) x := hψ.differentiableAt [i] (by norm_num) hx
    have e1 : DifferentiableAt ℝ (∂[1] η) x := hη.differentiableAt [1] (by norm_num) hx
    have dψ2 (i j : Fin 2) : DifferentiableAt ℝ (∂[i] (∂[j] ψ)) x :=
      hψ.differentiableAt [i, j] (by norm_num) hx
    have dω2 (i j : Fin 2) : DifferentiableAt ℝ (∂[i] (∂[j] ω)) x :=
      hω.smooth.differentiableAt [i, j] (by norm_num) hx
    rw [hE₁]
    simp (disch := fun_prop) only [partialDeriv_add, partialDeriv_sub, partialDeriv_mul,
      partialDeriv_neg_fun, partialDeriv_coord, partialDeriv_const]
    simp
    ring
  have hcomm : EqOn (∂[1] (∂[0] ω)) (∂[0] (∂[1] ω)) upperHalfPlane :=
    eqOn_partialDeriv_comm (hω.smooth.contDiffOn.of_le (by norm_num))
  have tA' : Tendsto (∂[1] (∂[0] ω)) (𝓝[upperHalfPlane] 0) (𝓝 A) :=
    hA.congr' (eventuallyEq_nhdsWithin_of_eqOn hcomm.symm)
  have tux' : Tendsto (∂[1] (∂[0] ψ)) (𝓝[upperHalfPlane] 0) (𝓝 (-ux)) :=
    hux.congr' (eventuallyEq_nhdsWithin_of_eqOn (hψ.eqOn_comm [] (by simp)).symm)
  have t0 := tendsto_coord_upperHalfPlane 0
  have t1 := tendsto_coord_upperHalfPlane 1
  have tψ1 := hψ.tendsto_of_parity [1] (by simp) (by decide)
  have tψ00 := hψ.tendsto_of_parity [0, 0] (by simp) (by decide)
  have tψ11 := hψ.tendsto_of_parity [1, 1] (by simp) (by decide)
  have tψ010 := hψ.tendsto_of_parity [0, 1, 0] (by simp) (by decide)
  have tω1 := hω.smooth.tendsto_zero_of_parity [1] (by simp) hω.odd (by simp)
  have tω11 := hω.smooth.tendsto_zero_of_parity [1, 1] (by simp) hω.odd (by simp)
  obtain ⟨L₁, tω00⟩ := hω.smooth.exists_tendsto [0, 0] (by simp)
  obtain ⟨L₂, tω010⟩ := hω.smooth.exists_tendsto [0, 1, 0] (by simp)
  obtain ⟨L₃, tω011⟩ := hω.smooth.exists_tendsto [0, 1, 1] (by simp)
  have hlim := ((hA.const_mul cw).add hq).sub
    (((huxy.neg.mul hωx).sub (tψ11.mul tω00)) |>.add
      ((((tendsto_const_nhds (x := cl)).sub hux).mul tA').add
        (((t0.const_mul cl).sub tψ1).mul tω010)) |>.add
      (((tψ010.mul tω1).add (((tendsto_const_nhds (x := cl)).add tux').mul hA)).add
        ((tψ00.mul tω11).add (((t1.const_mul cl).add hψ.tendsto_x).mul tω011))))
  have heq : ∀ x ∈ upperHalfPlane, (∂[0] (∂[1] (rescaledVorticityTendency cl cw ω η ψ))) x =
      (∂[0] E₁) x := fun x hx ↦ eqOn_partialDeriv isOpen_upperHalfPlane hexp1 0 hx
  convert hlim.congr' (eventually_nhdsWithin_of_forall fun x hx ↦
    ((heq x hx).trans (hexp2 x hx)).symm) using 2
  ring

/-- The `η` tendency in coordinates. -/
theorem rescaledEtaTendency_eq (cl cθ : ℝ) (η ξ ψ : ℝ^2 → ℝ) :
    rescaledEtaTendency cl cθ η ξ ψ = fun y ↦
      (cθ - cl + (∂[0] (∂[1] ψ)) y) * η y - (∂[0] (∂[0] ψ)) y * ξ y -
        ((cl * y 0 - (∂[1] ψ) y) * (∂[0] η) y + (cl * y 1 + (∂[0] ψ) y) * (∂[1] η) y) := by
  funext y
  rw [rescaledEtaTendency, advectiveDerivative_rescaled_eq]

/-- The `ξ` tendency in coordinates. -/
theorem rescaledXiTendency_eq (cl cθ : ℝ) (η ξ ψ : ℝ^2 → ℝ) :
    rescaledXiTendency cl cθ η ξ ψ = fun y ↦
      (cθ - cl - (∂[1] (∂[0] ψ)) y) * ξ y + (∂[1] (∂[1] ψ)) y * η y -
        ((cl * y 0 - (∂[1] ψ) y) * (∂[0] ξ) y + (cl * y 1 + (∂[0] ψ) y) * (∂[1] ξ) y) := by
  funext y
  rw [rescaledXiTendency, advectiveDerivative_rescaled_eq]

/-- **The first-order `η` trace**: `∂ₓR_η → (c_θ - 2 c_l - 2 u_x(0)) η_x(0)`. -/
theorem tendsto_partialDeriv_etaTendency (cl cθ : ℝ) (hη : IsOddJetField 2 η)
    (hξ : IsEvenAxisJetField 1 ξ) (hψ : IsJetStream ψ) {ηx ux : ℝ}
    (hηx : Tendsto (∂[0] η) (𝓝[upperHalfPlane] 0) (𝓝 ηx))
    (hux : Tendsto (∂[0] (∂[1] ψ)) (𝓝[upperHalfPlane] 0) (𝓝 (-ux))) :
    Tendsto (∂[0] (rescaledEtaTendency cl cθ η ξ ψ)) (𝓝[upperHalfPlane] 0)
      (𝓝 ((cθ - 2 * cl - 2 * ux) * ηx)) := by
  have hexp : ∀ x ∈ upperHalfPlane, (∂[0] (rescaledEtaTendency cl cθ η ξ ψ)) x =
      (∂[0] (∂[0] (∂[1] ψ))) x * η x + (cθ - cl + (∂[0] (∂[1] ψ)) x) * (∂[0] η) x -
        ((∂[0] (∂[0] (∂[0] ψ))) x * ξ x + (∂[0] (∂[0] ψ)) x * (∂[0] ξ) x) -
        ((cl - (∂[0] (∂[1] ψ)) x) * (∂[0] η) x + (cl * x 0 - (∂[1] ψ) x) * (∂[0] (∂[0] η)) x +
          ((∂[0] (∂[0] ψ)) x * (∂[1] η) x +
            (cl * x 1 + (∂[0] ψ) x) * (∂[0] (∂[1] η)) x)) := by
    intro x hx
    have dc (i : Fin 2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y i) x :=
      (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiableAt
    have d1 : DifferentiableAt ℝ η x := hη.smooth.differentiableAt [] (by norm_num) hx
    have dη1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] η) x :=
      hη.smooth.differentiableAt [i] (by norm_num) hx
    have d4 : DifferentiableAt ℝ ξ x := hξ.smooth.differentiableAt [] (by norm_num) hx
    have dψ1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] ψ) x := hψ.differentiableAt [i] (by norm_num) hx
    have dψ2 (i j : Fin 2) : DifferentiableAt ℝ (∂[i] (∂[j] ψ)) x :=
      hψ.differentiableAt [i, j] (by norm_num) hx
    rw [rescaledEtaTendency_eq]
    simp (disch := fun_prop) only [partialDeriv_add, partialDeriv_sub, partialDeriv_mul,
      partialDeriv_coord, partialDeriv_const]
    simp
  have t0 := tendsto_coord_upperHalfPlane 0
  have t1 := tendsto_coord_upperHalfPlane 1
  have tψ1 := hψ.tendsto_of_parity [1] (by simp) (by decide)
  have tψ00 := hψ.tendsto_of_parity [0, 0] (by simp) (by decide)
  have tψ001 := hψ.tendsto_of_parity [0, 0, 1] (by simp) (by decide)
  have tη := hη.smooth.tendsto_zero_of_parity [] (by simp) hη.odd (by simp)
  have tη1 := hη.smooth.tendsto_zero_of_parity [1] (by simp) hη.odd (by simp)
  have tξ' : Tendsto ξ (𝓝[upperHalfPlane] 0) (𝓝 0) :=
    (hξ.smooth.mono (m := 0) (by norm_num)).tendsto_zero_of_axis hξ.axis
  have tξ0 := hξ.smooth.tendsto_zero_of_parity [0] (by simp) hξ.even (by simp)
  obtain ⟨L₁, tη00⟩ := hη.smooth.exists_tendsto [0, 0] (by simp)
  obtain ⟨L₂, tη01⟩ := hη.smooth.exists_tendsto [0, 1] (by simp)
  have hcl := tendsto_const_nhds (x := cl) (f := 𝓝[upperHalfPlane] (0 : ℝ^2))
  have hcθ := tendsto_const_nhds (x := cθ - cl) (f := 𝓝[upperHalfPlane] (0 : ℝ^2))
  have hlim := (((tψ001.mul tη).add ((hcθ.add hux).mul hηx)).sub
      ((hψ.tendsto_xxx.mul tξ').add (tψ00.mul tξ0))).sub
    ((((hcl.sub hux).mul hηx).add (((t0.const_mul cl).sub tψ1).mul tη00)).add
      ((tψ00.mul tη1).add (((t1.const_mul cl).add hψ.tendsto_x).mul tη01)))
  convert hlim.congr' (eventually_nhdsWithin_of_forall fun x hx ↦ (hexp x hx).symm) using 2
  ring

/-- **The mixed `η` jet**: `∂ₓ∂ᵧR_η → (c_θ - 3 c_l - u_x(0)) η_xy(0) - 2 u_xy(0) η_x(0)`. -/
theorem tendsto_mixedDeriv_etaTendency (cl cθ : ℝ) (hη : IsOddJetField 3 η)
    (hξ : IsEvenAxisJetField 2 ξ) (hψ : IsJetStream ψ) {ηx q ux uxy : ℝ}
    (hηx : Tendsto (∂[0] η) (𝓝[upperHalfPlane] 0) (𝓝 ηx))
    (hq : Tendsto (∂[0] (∂[1] η)) (𝓝[upperHalfPlane] 0) (𝓝 q))
    (hux : Tendsto (∂[0] (∂[1] ψ)) (𝓝[upperHalfPlane] 0) (𝓝 (-ux)))
    (huxy : Tendsto (∂[0] (∂[1] (∂[1] ψ))) (𝓝[upperHalfPlane] 0) (𝓝 (-uxy))) :
    Tendsto (∂[0] (∂[1] (rescaledEtaTendency cl cθ η ξ ψ))) (𝓝[upperHalfPlane] 0)
      (𝓝 ((cθ - 3 * cl - ux) * q - 2 * uxy * ηx)) := by
  set E₁ : ℝ^2 → ℝ := fun y ↦
    (∂[1] (∂[0] (∂[1] ψ))) y * η y + (cθ - cl + (∂[0] (∂[1] ψ)) y) * (∂[1] η) y -
      ((∂[1] (∂[0] (∂[0] ψ))) y * ξ y + (∂[0] (∂[0] ψ)) y * (∂[1] ξ) y) -
      (-(∂[1] (∂[1] ψ)) y * (∂[0] η) y + (cl * y 0 - (∂[1] ψ) y) * (∂[1] (∂[0] η)) y +
        ((cl + (∂[1] (∂[0] ψ)) y) * (∂[1] η) y + (cl * y 1 + (∂[0] ψ) y) * (∂[1] (∂[1] η)) y))
    with hE₁
  have hexp1 : ∀ x ∈ upperHalfPlane, (∂[1] (rescaledEtaTendency cl cθ η ξ ψ)) x = E₁ x := by
    intro x hx
    have dc (i : Fin 2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y i) x :=
      (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiableAt
    have d1 : DifferentiableAt ℝ η x := hη.smooth.differentiableAt [] (by norm_num) hx
    have dη1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] η) x :=
      hη.smooth.differentiableAt [i] (by norm_num) hx
    have d4 : DifferentiableAt ℝ ξ x := hξ.smooth.differentiableAt [] (by norm_num) hx
    have dψ1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] ψ) x := hψ.differentiableAt [i] (by norm_num) hx
    have dψ2 (i j : Fin 2) : DifferentiableAt ℝ (∂[i] (∂[j] ψ)) x :=
      hψ.differentiableAt [i, j] (by norm_num) hx
    rw [rescaledEtaTendency_eq, hE₁]
    simp (disch := fun_prop) only [partialDeriv_add, partialDeriv_sub, partialDeriv_mul,
      partialDeriv_coord, partialDeriv_const]
    simp
  have hexp2 : ∀ x ∈ upperHalfPlane, (∂[0] E₁) x =
      ((∂[0] (∂[1] (∂[0] (∂[1] ψ)))) x * η x + (∂[1] (∂[0] (∂[1] ψ))) x * (∂[0] η) x +
          ((∂[0] (∂[0] (∂[1] ψ))) x * (∂[1] η) x +
            (cθ - cl + (∂[0] (∂[1] ψ)) x) * (∂[0] (∂[1] η)) x)) -
        (((∂[0] (∂[1] (∂[0] (∂[0] ψ)))) x * ξ x + (∂[1] (∂[0] (∂[0] ψ))) x * (∂[0] ξ) x) +
          ((∂[0] (∂[0] (∂[0] ψ))) x * (∂[1] ξ) x + (∂[0] (∂[0] ψ)) x * (∂[0] (∂[1] ξ)) x)) -
        (((-(∂[0] (∂[1] (∂[1] ψ))) x * (∂[0] η) x + -(∂[1] (∂[1] ψ)) x * (∂[0] (∂[0] η)) x) +
            ((cl - (∂[0] (∂[1] ψ)) x) * (∂[1] (∂[0] η)) x +
              (cl * x 0 - (∂[1] ψ) x) * (∂[0] (∂[1] (∂[0] η))) x)) +
          (((∂[0] (∂[1] (∂[0] ψ))) x * (∂[1] η) x + (cl + (∂[1] (∂[0] ψ)) x) * (∂[0] (∂[1] η)) x) +
            ((∂[0] (∂[0] ψ)) x * (∂[1] (∂[1] η)) x +
              (cl * x 1 + (∂[0] ψ) x) * (∂[0] (∂[1] (∂[1] η))) x))) := by
    intro x hx
    have dc (i : Fin 2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y i) x :=
      (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiableAt
    have d1 : DifferentiableAt ℝ η x := hη.smooth.differentiableAt [] (by norm_num) hx
    have dη1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] η) x :=
      hη.smooth.differentiableAt [i] (by norm_num) hx
    have d4 : DifferentiableAt ℝ ξ x := hξ.smooth.differentiableAt [] (by norm_num) hx
    have d4' : DifferentiableAt ℝ (∂[1] ξ) x := hξ.smooth.differentiableAt [1] (by norm_num) hx
    have dψ1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] ψ) x := hψ.differentiableAt [i] (by norm_num) hx
    have dψ2 (i j : Fin 2) : DifferentiableAt ℝ (∂[i] (∂[j] ψ)) x :=
      hψ.differentiableAt [i, j] (by norm_num) hx
    have dψ3 (i j k : Fin 2) : DifferentiableAt ℝ (∂[i] (∂[j] (∂[k] ψ))) x :=
      hψ.differentiableAt [i, j, k] (by norm_num) hx
    have dη2 (i j : Fin 2) : DifferentiableAt ℝ (∂[i] (∂[j] η)) x :=
      hη.smooth.differentiableAt [i, j] (by norm_num) hx
    rw [hE₁]
    simp (disch := fun_prop) only [partialDeriv_add, partialDeriv_sub, partialDeriv_mul,
      partialDeriv_neg_fun, partialDeriv_coord, partialDeriv_const]
    simp
  have hcommη : EqOn (∂[1] (∂[0] η)) (∂[0] (∂[1] η)) upperHalfPlane :=
    eqOn_partialDeriv_comm (hη.smooth.contDiffOn.of_le (by norm_num))
  have tq' : Tendsto (∂[1] (∂[0] η)) (𝓝[upperHalfPlane] 0) (𝓝 q) :=
    hq.congr' (eventuallyEq_nhdsWithin_of_eqOn hcommη.symm)
  have tux' : Tendsto (∂[1] (∂[0] ψ)) (𝓝[upperHalfPlane] 0) (𝓝 (-ux)) :=
    hux.congr' (eventuallyEq_nhdsWithin_of_eqOn (hψ.eqOn_comm [] (by simp)).symm)
  have tc : Tendsto (∂[1] (∂[0] (∂[1] ψ))) (𝓝[upperHalfPlane] 0) (𝓝 (-uxy)) :=
    huxy.congr' (eventuallyEq_nhdsWithin_of_eqOn (hψ.eqOn_comm [1] (by simp)).symm)
  have t0 := tendsto_coord_upperHalfPlane 0
  have t1 := tendsto_coord_upperHalfPlane 1
  have tψ1 := hψ.tendsto_of_parity [1] (by simp) (by decide)
  have tψ00 := hψ.tendsto_of_parity [0, 0] (by simp) (by decide)
  have tψ11 := hψ.tendsto_of_parity [1, 1] (by simp) (by decide)
  have tψ001 := hψ.tendsto_of_parity [0, 0, 1] (by simp) (by decide)
  have tψ010 := hψ.tendsto_of_parity [0, 1, 0] (by simp) (by decide)
  have tψ100 := hψ.tendsto_of_parity [1, 0, 0] (by simp) (by decide)
  obtain ⟨L₁, tψ0101⟩ := hψ.exists_tendsto [0, 1, 0, 1] (by simp)
  obtain ⟨L₂, tψ0100⟩ := hψ.exists_tendsto [0, 1, 0, 0] (by simp)
  have tη := hη.smooth.tendsto_zero_of_parity [] (by simp) hη.odd (by simp)
  have tη1 := hη.smooth.tendsto_zero_of_parity [1] (by simp) hη.odd (by simp)
  have tη00 := hη.smooth.tendsto_zero_of_parity [0, 0] (by simp) hη.odd (by norm_num)
  have tη11 := hη.smooth.tendsto_zero_of_parity [1, 1] (by simp) hη.odd (by simp)
  obtain ⟨L₃, tη010⟩ := hη.smooth.exists_tendsto [0, 1, 0] (by simp)
  obtain ⟨L₄, tη011⟩ := hη.smooth.exists_tendsto [0, 1, 1] (by simp)
  have tξ : Tendsto ξ (𝓝[upperHalfPlane] 0) (𝓝 0) :=
    (hξ.smooth.mono (m := 0) (by norm_num)).tendsto_zero_of_axis hξ.axis
  have tξ1 : Tendsto (∂[1] ξ) (𝓝[upperHalfPlane] 0) (𝓝 0) :=
    (hξ.smooth.mono (m := 1) (by norm_num)).tendsto_zero_of_axis hξ.axis
  have tξ0 := hξ.smooth.tendsto_zero_of_parity [0] (by simp) hξ.even (by simp)
  have tξ01 := hξ.smooth.tendsto_zero_of_parity [0, 1] (by simp) hξ.even (by simp)
  have hcl := tendsto_const_nhds (x := cl) (f := 𝓝[upperHalfPlane] (0 : ℝ^2))
  have hcθ := tendsto_const_nhds (x := cθ - cl) (f := 𝓝[upperHalfPlane] (0 : ℝ^2))
  have hlim := ((((tψ0101.mul tη).add (tc.mul hηx)).add
        ((tψ001.mul tη1).add ((hcθ.add hux).mul hq))).sub
      (((tψ0100.mul tξ).add (tψ100.mul tξ0)).add
        ((hψ.tendsto_xxx.mul tξ1).add (tψ00.mul tξ01)))).sub
    ((((huxy.neg.mul hηx).add (tψ11.neg.mul tη00)).add
        (((hcl.sub hux).mul tq').add (((t0.const_mul cl).sub tψ1).mul tη010))).add
      (((tψ010.mul tη1).add ((hcl.add tux').mul hq)).add
        ((tψ00.mul tη11).add (((t1.const_mul cl).add hψ.tendsto_x).mul tη011))))
  have heq : ∀ x ∈ upperHalfPlane, (∂[0] (∂[1] (rescaledEtaTendency cl cθ η ξ ψ))) x =
      (∂[0] E₁) x := fun x hx ↦ eqOn_partialDeriv isOpen_upperHalfPlane hexp1 0 hx
  convert hlim.congr' (eventually_nhdsWithin_of_forall fun x hx ↦
    ((heq x hx).trans (hexp2 x hx)).symm) using 2
  ring

/-- **The `ξ` jet**: `∂ₓ²R_ξ → (c_θ - 3 c_l - u_x(0)) ξ_xx(0) - 2 u_xy(0) η_x(0)`. -/
theorem tendsto_partialDeriv_partialDeriv_xiTendency (cl cθ : ℝ) (hη : IsOddJetField 2 η)
    (hξ : IsEvenAxisJetField 3 ξ) (hψ : IsJetStream ψ) {ηx r ux uxy : ℝ}
    (hηx : Tendsto (∂[0] η) (𝓝[upperHalfPlane] 0) (𝓝 ηx))
    (hr : Tendsto (∂[0] (∂[0] ξ)) (𝓝[upperHalfPlane] 0) (𝓝 r))
    (hux : Tendsto (∂[0] (∂[1] ψ)) (𝓝[upperHalfPlane] 0) (𝓝 (-ux)))
    (huxy : Tendsto (∂[0] (∂[1] (∂[1] ψ))) (𝓝[upperHalfPlane] 0) (𝓝 (-uxy))) :
    Tendsto (∂[0] (∂[0] (rescaledXiTendency cl cθ η ξ ψ))) (𝓝[upperHalfPlane] 0)
      (𝓝 ((cθ - 3 * cl - ux) * r - 2 * uxy * ηx)) := by
  set E₁ : ℝ^2 → ℝ := fun y ↦
    (-(∂[0] (∂[1] (∂[0] ψ))) y * ξ y + (cθ - cl - (∂[1] (∂[0] ψ)) y) * (∂[0] ξ) y) +
      ((∂[0] (∂[1] (∂[1] ψ))) y * η y + (∂[1] (∂[1] ψ)) y * (∂[0] η) y) -
      ((cl - (∂[0] (∂[1] ψ)) y) * (∂[0] ξ) y + (cl * y 0 - (∂[1] ψ) y) * (∂[0] (∂[0] ξ)) y +
        ((∂[0] (∂[0] ψ)) y * (∂[1] ξ) y + (cl * y 1 + (∂[0] ψ) y) * (∂[0] (∂[1] ξ)) y))
    with hE₁
  have hexp1 : ∀ x ∈ upperHalfPlane, (∂[0] (rescaledXiTendency cl cθ η ξ ψ)) x = E₁ x := by
    intro x hx
    have dc (i : Fin 2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y i) x :=
      (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiableAt
    have d1 : DifferentiableAt ℝ η x := hη.smooth.differentiableAt [] (by norm_num) hx
    have da : DifferentiableAt ℝ ξ x := hξ.smooth.differentiableAt [] (by norm_num) hx
    have dξ1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] ξ) x :=
      hξ.smooth.differentiableAt [i] (by norm_num) hx
    have dψ1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] ψ) x := hψ.differentiableAt [i] (by norm_num) hx
    have dψ2 (i j : Fin 2) : DifferentiableAt ℝ (∂[i] (∂[j] ψ)) x :=
      hψ.differentiableAt [i, j] (by norm_num) hx
    rw [rescaledXiTendency_eq, hE₁]
    simp (disch := fun_prop) only [partialDeriv_add, partialDeriv_sub, partialDeriv_mul,
      partialDeriv_coord, partialDeriv_const]
    simp
  have hexp2 : ∀ x ∈ upperHalfPlane, (∂[0] E₁) x =
      ((-(∂[0] (∂[0] (∂[1] (∂[0] ψ)))) x * ξ x + -(∂[0] (∂[1] (∂[0] ψ))) x * (∂[0] ξ) x) +
          (-(∂[0] (∂[1] (∂[0] ψ))) x * (∂[0] ξ) x +
            (cθ - cl - (∂[1] (∂[0] ψ)) x) * (∂[0] (∂[0] ξ)) x)) +
        (((∂[0] (∂[0] (∂[1] (∂[1] ψ)))) x * η x + (∂[0] (∂[1] (∂[1] ψ))) x * (∂[0] η) x) +
          ((∂[0] (∂[1] (∂[1] ψ))) x * (∂[0] η) x + (∂[1] (∂[1] ψ)) x * (∂[0] (∂[0] η)) x)) -
        (((-(∂[0] (∂[0] (∂[1] ψ))) x * (∂[0] ξ) x +
              (cl - (∂[0] (∂[1] ψ)) x) * (∂[0] (∂[0] ξ)) x) +
            ((cl - (∂[0] (∂[1] ψ)) x) * (∂[0] (∂[0] ξ)) x +
              (cl * x 0 - (∂[1] ψ) x) * (∂[0] (∂[0] (∂[0] ξ))) x)) +
          (((∂[0] (∂[0] (∂[0] ψ))) x * (∂[1] ξ) x + (∂[0] (∂[0] ψ)) x * (∂[0] (∂[1] ξ)) x) +
            ((∂[0] (∂[0] ψ)) x * (∂[0] (∂[1] ξ)) x +
              (cl * x 1 + (∂[0] ψ) x) * (∂[0] (∂[0] (∂[1] ξ))) x))) := by
    intro x hx
    have dc (i : Fin 2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y i) x :=
      (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiableAt
    have d1 : DifferentiableAt ℝ η x := hη.smooth.differentiableAt [] (by norm_num) hx
    have d2 : DifferentiableAt ℝ (∂[0] η) x := hη.smooth.differentiableAt [0] (by norm_num) hx
    have da : DifferentiableAt ℝ ξ x := hξ.smooth.differentiableAt [] (by norm_num) hx
    have dξ1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] ξ) x :=
      hξ.smooth.differentiableAt [i] (by norm_num) hx
    have dξ2 (i j : Fin 2) : DifferentiableAt ℝ (∂[i] (∂[j] ξ)) x :=
      hξ.smooth.differentiableAt [i, j] (by norm_num) hx
    have dψ1 (i : Fin 2) : DifferentiableAt ℝ (∂[i] ψ) x := hψ.differentiableAt [i] (by norm_num) hx
    have dψ2 (i j : Fin 2) : DifferentiableAt ℝ (∂[i] (∂[j] ψ)) x :=
      hψ.differentiableAt [i, j] (by norm_num) hx
    have dψ3 (i j k : Fin 2) : DifferentiableAt ℝ (∂[i] (∂[j] (∂[k] ψ))) x :=
      hψ.differentiableAt [i, j, k] (by norm_num) hx
    rw [hE₁]
    simp (disch := fun_prop) only [partialDeriv_add, partialDeriv_sub, partialDeriv_mul,
      partialDeriv_neg_fun, partialDeriv_coord, partialDeriv_const]
    simp
  have tux' : Tendsto (∂[1] (∂[0] ψ)) (𝓝[upperHalfPlane] 0) (𝓝 (-ux)) :=
    hux.congr' (eventuallyEq_nhdsWithin_of_eqOn (hψ.eqOn_comm [] (by simp)).symm)
  have t0 := tendsto_coord_upperHalfPlane 0
  have t1 := tendsto_coord_upperHalfPlane 1
  have tψ1 := hψ.tendsto_of_parity [1] (by simp) (by decide)
  have tψ00 := hψ.tendsto_of_parity [0, 0] (by simp) (by decide)
  have tψ11 := hψ.tendsto_of_parity [1, 1] (by simp) (by decide)
  have tψ001 := hψ.tendsto_of_parity [0, 0, 1] (by simp) (by decide)
  have tψ010 := hψ.tendsto_of_parity [0, 1, 0] (by simp) (by decide)
  obtain ⟨L₁, tψ0010⟩ := hψ.exists_tendsto [0, 0, 1, 0] (by simp)
  obtain ⟨L₂, tψ0011⟩ := hψ.exists_tendsto [0, 0, 1, 1] (by simp)
  have tη := hη.smooth.tendsto_zero_of_parity [] (by simp) hη.odd (by simp)
  have tη00 := hη.smooth.tendsto_zero_of_parity [0, 0] (by simp) hη.odd (by norm_num)
  have tξ : Tendsto ξ (𝓝[upperHalfPlane] 0) (𝓝 0) :=
    (hξ.smooth.mono (m := 0) (by norm_num)).tendsto_zero_of_axis hξ.axis
  have tξ1 : Tendsto (∂[1] ξ) (𝓝[upperHalfPlane] 0) (𝓝 0) :=
    (hξ.smooth.mono (m := 1) (by norm_num)).tendsto_zero_of_axis hξ.axis
  have tξ0 := hξ.smooth.tendsto_zero_of_parity [0] (by simp) hξ.even (by simp)
  have tξ01 := hξ.smooth.tendsto_zero_of_parity [0, 1] (by simp) hξ.even (by simp)
  obtain ⟨L₃, tξ000⟩ := hξ.smooth.exists_tendsto [0, 0, 0] (by simp)
  obtain ⟨L₄, tξ001⟩ := hξ.smooth.exists_tendsto [0, 0, 1] (by simp)
  have hcl := tendsto_const_nhds (x := cl) (f := 𝓝[upperHalfPlane] (0 : ℝ^2))
  have hcθ := tendsto_const_nhds (x := cθ - cl) (f := 𝓝[upperHalfPlane] (0 : ℝ^2))
  have hlim := ((((tψ0010.neg.mul tξ).add (tψ010.neg.mul tξ0)).add
        ((tψ010.neg.mul tξ0).add ((hcθ.sub tux').mul hr))).add
      (((tψ0011.mul tη).add (huxy.mul hηx)).add ((huxy.mul hηx).add (tψ11.mul tη00)))).sub
    ((((tψ001.neg.mul tξ0).add ((hcl.sub hux).mul hr)).add
        (((hcl.sub hux).mul hr).add (((t0.const_mul cl).sub tψ1).mul tξ000))).add
      (((hψ.tendsto_xxx.mul tξ1).add (tψ00.mul tξ01)).add
        ((tψ00.mul tξ01).add (((t1.const_mul cl).add hψ.tendsto_x).mul tξ001))))
  have heq : ∀ x ∈ upperHalfPlane, (∂[0] (∂[0] (rescaledXiTendency cl cθ η ξ ψ))) x =
      (∂[0] E₁) x := fun x hx ↦ eqOn_partialDeriv isOpen_upperHalfPlane hexp1 0 hx
  convert hlim.congr' (eventually_nhdsWithin_of_forall fun x hx ↦
    ((heq x hx).trans (hexp2 x hx)).symm) using 2
  ring

/-- The partial derivatives of a `C²` function on the open upper half-plane are differentiable
there. -/
private theorem differentiableAt_partialDeriv_of_contDiffOn_two {f : ℝ^2 → ℝ}
    (hf : ContDiffOn ℝ 2 f upperHalfPlane) {x : ℝ^2} (hx : x ∈ upperHalfPlane) (i : Fin 2) :
    DifferentiableAt ℝ (∂[i] f) x :=
  ((hf.partialDeriv i isOpen_upperHalfPlane (k := 1) (by norm_num)).differentiableOn
    (by norm_num) x hx).differentiableAt (isOpen_upperHalfPlane.mem_nhds hx)

/-- `∂ₓR_θ = R_η(θ_x, θ_y)` on the open upper half-plane. -/
theorem partialDeriv_temperatureTendency_eq (cl cθ : ℝ) {θ : ℝ^2 → ℝ}
    (hθ : ContDiffOn ℝ 2 θ upperHalfPlane) (hψ : ContDiffOn ℝ 2 ψ upperHalfPlane) {x : ℝ^2}
    (hx : x ∈ upperHalfPlane) :
    (∂[0] (rescaledTemperatureTendency cl cθ θ ψ)) x =
      rescaledEtaTendency cl cθ (∂[0] θ) (∂[1] θ) ψ x := by
  have dc (i : Fin 2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y i) x :=
    (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiableAt
  have d1 : DifferentiableAt ℝ θ x :=
    (hθ.differentiableOn (by norm_num) x hx).differentiableAt (isOpen_upperHalfPlane.mem_nhds hx)
  have dθ := differentiableAt_partialDeriv_of_contDiffOn_two hθ hx
  have dψ := differentiableAt_partialDeriv_of_contDiffOn_two hψ hx
  have hcomm := eqOn_partialDeriv_comm hθ hx
  rw [rescaledTemperatureTendency_eq, rescaledEtaTendency_eq]
  simp (disch := fun_prop) only [partialDeriv_add, partialDeriv_sub, partialDeriv_mul,
    partialDeriv_coord, partialDeriv_const]
  simp only [hcomm]
  simp
  ring

/-- `∂ᵧR_θ = R_ξ(θ_x, θ_y)` on the open upper half-plane. -/
theorem partialDeriv_one_temperatureTendency_eq (cl cθ : ℝ) {θ : ℝ^2 → ℝ}
    (hθ : ContDiffOn ℝ 2 θ upperHalfPlane) (hψ : ContDiffOn ℝ 2 ψ upperHalfPlane) {x : ℝ^2}
    (hx : x ∈ upperHalfPlane) :
    (∂[1] (rescaledTemperatureTendency cl cθ θ ψ)) x =
      rescaledXiTendency cl cθ (∂[0] θ) (∂[1] θ) ψ x := by
  have dc (i : Fin 2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y i) x :=
    (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiableAt
  have d1 : DifferentiableAt ℝ θ x :=
    (hθ.differentiableOn (by norm_num) x hx).differentiableAt (isOpen_upperHalfPlane.mem_nhds hx)
  have dθ := differentiableAt_partialDeriv_of_contDiffOn_two hθ hx
  have dψ := differentiableAt_partialDeriv_of_contDiffOn_two hψ hx
  have hcomm := eqOn_partialDeriv_comm hθ hx
  rw [rescaledTemperatureTendency_eq, rescaledXiTendency_eq]
  simp (disch := fun_prop) only [partialDeriv_add, partialDeriv_sub, partialDeriv_mul,
    partialDeriv_coord, partialDeriv_const]
  simp only [hcomm]
  simp
  ring

end Jets

end Boussinesq
