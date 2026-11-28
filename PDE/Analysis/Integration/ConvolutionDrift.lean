/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Integration.ConvolutionDerivative
public import PDE.FDeriv.Calculus.Convolution
public import PDE.FDeriv.PartialDeriv.Transport
import PDE.Elliptic.Regularity.Interior.Weyl.SecondOrder
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support
import PDE.FDeriv.PartialDeriv.Support.Iterated

/-!
# Mollification and the dilation drift `x·∇`

Mollification commutes with constant-coefficient operators, but not with the drift `x·∇` of the
self-similar equations. For a smooth compactly supported kernel `ρ` on `ℝⁿ` we write the
commutator `ρ ∗ (x·∇g) - x·∇(ρ ∗ g)` as `-(g ∗ K)` with the kernel
`K(z) = n ρ(z) + z·∇ρ(z) = div (z ρ(z))` (`driftCommutator`). No derivative of `g` appears, so
the formula makes sense for every locally integrable `g`. We then mollify a self-similar
equation in weak form: the mollifications satisfy it at every point, with the commutator as an
extra term (`mollified_similarity_eq`). This is the mollified equation (2.9) of Hou, Wang and
Yang, who write the commutator as `-∫ ρ(y) y·∇g(x - y) dy` for `g ∈ H¹`. That form is
`SobolevSpace.Approximation.convolution_iteratedPartialDeriv_driftKernel`, and the bound (2.10)
is `SobolevSpace.Approximation.integral_sq_convolution_iteratedPartialDeriv_driftKernel_le`.

## Main results

* `integrable_mul_comp_const_sub`: `y ↦ g(y) k(x - y)` is integrable for a locally integrable `g`
  and a continuous compactly supported `k`.
* `fderiv_convolution_right_apply`: `D(g ∗ ρ)(x) h = ∫ g(y) Dρ(x - y) h dy` for a locally
  integrable `g` and a `C¹` compactly supported `ρ`.
* `driftKernel`, `driftCommutator`, `driftCommutator_eq`: the kernel `K`, the commutator
  `-(g ∗ K)`, and its two terms `-(n (g ∗ ρ) + g ∗ κ)` with `κ(z) = z·∇ρ(z)`.
* `driftKernel_eq_sum`, `convolution_driftKernel_eq_sum`: `K = Σⱼ ∂ⱼ(zⱼ ρ)` and
  `g ∗ K = Σⱼ ∂ⱼ(g ∗ (zⱼ ρ))`.
* `driftKernel_iteratedPartialDeriv`, `driftCommutator_iteratedPartialDeriv`: for every word
  `α`, the kernel of `∂^α ρ` is `∂^α K - |α| ∂^α ρ`, so the commutator for the kernel `∂^α ρ` is
  `|α| (g ∗ ∂^α ρ) - g ∗ ∂^α K`.
* `mollified_similarity_eq`: in every dimension, if locally integrable `g`, `P`, `N₁, …, Nₙ`
  satisfy the weak form of `(1 - n/2) g - ½ x·∇g - Δg + Σⱼ ∂ⱼNⱼ + ∂ᵢP = F`, their
  mollifications satisfy the equation at every point, with the commutator.

## How it works

Every derivative goes on the kernel. For a smooth compactly supported `ρ`,
`x·∇(g ∗ ρ)(x) = ∫ g(y) ∇ρ(x - y)·x dy` (`fderiv_convolution_right_apply`), and the distribution
`x·∇g` tested with `ρ(x - ·)` is `-n (g ∗ ρ)(x) + ∫ g(y) ∇ρ(x - y)·y dy`. The difference is
`-(n (g ∗ ρ) + g ∗ κ)(x)` (`integral_mul_fderiv_comp_const_sub_apply_self`). Testing the weak
equation with `ψ = ρ(x - ·)` turns each term into a mollification or a derivative of one, which
gives `mollified_similarity_eq`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2, the mollified equation
  (2.9) and the commutator after it. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory
open ContinuousLinearMap (mul)
open scoped Convolution

namespace PDE.Analysis

variable {n : ℕ}

/-- A locally integrable function times a reflected translate of a continuous compactly
supported function is integrable. -/
theorem integrable_mul_comp_const_sub {g k : ℝ^n → ℝ} (hg : LocallyIntegrable g volume)
    (hk : Continuous k) (hkc : HasCompactSupport k) (x : ℝ^n) :
    Integrable fun y ↦ g y * k (x - y) :=
  hg.integrable_smul_right_of_hasCompactSupport (hk.comp (continuous_const.sub continuous_id))
    (hkc.comp_homeomorph (Homeomorph.subLeft x))

/-- The derivative of a convolution with a `C¹` compactly supported right factor, in a
direction: `D(g ∗ ρ)(x) h = ∫ g(y) Dρ(x-y) h dy`. It is the sum over the coordinates of
`convolution_partialDeriv_right`, weighted by the components of `h`. -/
theorem fderiv_convolution_right_apply {g ρ : ℝ^n → ℝ} (hg : LocallyIntegrable g volume)
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (x h : ℝ^n) :
    fderiv ℝ (g ⋆[mul ℝ ℝ, volume] ρ) x h = ∫ y, g y * fderiv ℝ ρ (x - y) h := by
  have hj : ∀ j : Fin n, ∂[j] (g ⋆[mul ℝ ℝ, volume] ρ) x = ∫ y, g y * ∂[j] ρ (x - y) :=
    fun j ↦ convolution_partialDeriv_right g ρ hg hρc hρ j x
  have hint : ∀ j : Fin n, Integrable fun y ↦ g y * ∂[j] ρ (x - y) * h j := fun j ↦
    (integrable_mul_comp_const_sub hg (hρ.continuous_partialDeriv j) (hρc.partialDeriv j)
      x).mul_const _
  rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul]
  simp only [hj]
  calc ∑ j, (∫ y, g y * ∂[j] ρ (x - y)) * h j
      = ∑ j, ∫ y, g y * ∂[j] ρ (x - y) * h j :=
        Finset.sum_congr rfl fun j _ ↦ (integral_mul_const _ _).symm
    _ = ∫ y, ∑ j, g y * ∂[j] ρ (x - y) * h j := (integral_finsetSum _ fun j _ ↦ hint j).symm
    _ = ∫ y, g y * fderiv ℝ ρ (x - y) h := integral_congr_ae (.of_forall fun y ↦ by
        beta_reduce
        rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ mul_assoc _ _ _)

/-- The kernel `z ↦ z·∇ρ(z)` is continuous. -/
theorem continuous_fderiv_apply_self {ρ : ℝ^n → ℝ} (hρ : ContDiff ℝ 1 ρ) :
    Continuous fun z ↦ fderiv ℝ ρ z z :=
  (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_id

/-- The kernel `z ↦ z·∇ρ(z)` has compact support. -/
theorem hasCompactSupport_fderiv_apply_self {ρ : ℝ^n → ℝ} (hρc : HasCompactSupport ρ) :
    HasCompactSupport fun z ↦ fderiv ℝ ρ z z :=
  HasCompactSupport.intro hρc.isCompact fun z hz ↦ by
    rw [fderiv_of_notMem_tsupport ℝ hz, zero_apply]

/-- **The kernel of the commutator of mollification and the drift**:
`K(z) = n ρ(z) + z·∇ρ(z)`, which is `div (z ρ(z))`. -/
def driftKernel (ρ : ℝ^n → ℝ) (z : ℝ^n) : ℝ :=
  n * ρ z + fderiv ℝ ρ z z

/-- The kernel of the commutator is smooth. -/
theorem contDiff_driftKernel {ρ : ℝ^n → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (driftKernel ρ) :=
  (contDiff_const.mul hρ).add ((contDiff_infty_iff_fderiv.mp hρ).2.clm_apply contDiff_id)

/-- The kernel of the commutator has compact support. -/
theorem hasCompactSupport_driftKernel {ρ : ℝ^n → ℝ} (hρc : HasCompactSupport ρ) :
    HasCompactSupport (driftKernel ρ) :=
  HasCompactSupport.intro hρc.isCompact fun z hz ↦ by
    rw [driftKernel, image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport ℝ hz,
      zero_apply, mul_zero, add_zero]

/-- The kernel of the commutator is a divergence: `K = Σⱼ ∂ⱼ(zⱼ ρ)`. -/
theorem driftKernel_eq_sum {ρ : ℝ^n → ℝ} {z : ℝ^n} (hρ : DifferentiableAt ℝ ρ z) :
    driftKernel ρ z = ∑ j, ∂[j] (fun y ↦ y j * ρ y) z := by
  have hc : ∀ j : Fin n, DifferentiableAt ℝ (fun y : ℝ^n ↦ y j) z := fun j ↦
    (EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt
  have hj : ∀ j : Fin n, ∂[j] (fun y ↦ y j * ρ y) z = ρ z + ∂[j] ρ z * z j := fun j ↦ by
    rw [PDE.partialDeriv_mul (hc j) hρ, PDE.partialDeriv_coord]
    simp only [↓reduceIte]
    ring
  simp only [hj]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← PDE.fderiv_apply_eq_sum_partialDeriv_mul]
  rfl

/-- The convolution with the kernel of the commutator is a divergence:
`g ∗ K = Σⱼ ∂ⱼ(g ∗ (zⱼ ρ))`, for a locally integrable `g`. -/
theorem convolution_driftKernel_eq_sum {g ρ : ℝ^n → ℝ} (hg : LocallyIntegrable g volume)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) (x : ℝ^n) :
    (g ⋆[mul ℝ ℝ, volume] driftKernel ρ) x =
      ∑ j, ∂[j] (g ⋆[mul ℝ ℝ, volume] fun z ↦ z j * ρ z) x := by
  have hkj : ∀ j : Fin n, ContDiff ℝ 1 (fun z : ℝ^n ↦ z j * ρ z) := fun j ↦
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.mul hρ).of_le (by simp)
  have hkjc : ∀ j : Fin n, HasCompactSupport (fun z : ℝ^n ↦ z j * ρ z) := fun j ↦
    hρc.mul_left
  have h2 : ∀ j : Fin n, ∂[j] (g ⋆[mul ℝ ℝ, volume] fun z ↦ z j * ρ z) x =
      ∫ y, g y * ∂[j] (fun z ↦ z j * ρ z) (x - y) := fun j ↦
    convolution_partialDeriv_right g _ hg (hkjc j) (hkj j) j x
  have hint : ∀ j : Fin n, Integrable fun y ↦ g y * ∂[j] (fun z ↦ z j * ρ z) (x - y) :=
    fun j ↦ integrable_mul_comp_const_sub hg ((hkj j).continuous_partialDeriv j)
      ((hkjc j).partialDeriv j) x
  simp only [h2]
  rw [← integral_finsetSum _ fun j _ ↦ hint j, convolution_def]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  simp only [ContinuousLinearMap.mul_apply']
  rw [driftKernel_eq_sum (hρ.differentiable (by simp) _), Finset.mul_sum]

/-- The kernel of the commutator for a differentiated kernel:
`K[∂^α ρ] = ∂^α K[ρ] - |α| ∂^α ρ`, because `∂^α (z·∇ρ) = z·∇(∂^α ρ) + |α| ∂^α ρ`. -/
theorem driftKernel_iteratedPartialDeriv {ρ : ℝ^n → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (α : List (Fin n)) (z : ℝ^n) :
    driftKernel (iteratedPartialDeriv α ρ) z =
      iteratedPartialDeriv α (driftKernel ρ) z - α.length * iteratedPartialDeriv α ρ z := by
  have hE : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ fderiv ℝ ρ z z) :=
    (contDiff_infty_iff_fderiv.mp hρ).2.clm_apply contDiff_id
  have hsplit : driftKernel ρ = ((n : ℝ) • ρ) + fun z ↦ fderiv ℝ ρ z z := by
    funext z
    simp [driftKernel]
  have hadd : iteratedPartialDeriv α (((n : ℝ) • ρ) + fun z ↦ fderiv ℝ ρ z z) z =
      iteratedPartialDeriv α ((n : ℝ) • ρ) z +
        iteratedPartialDeriv α (fun z ↦ fderiv ℝ ρ z z) z :=
    congrFun (iteratedPartialDeriv_add_of_contDiff α
      ((hρ.const_smul (n : ℝ)).of_le (by exact_mod_cast le_top))
      (hE.of_le (by exact_mod_cast le_top))) z
  have hsm : iteratedPartialDeriv α ((n : ℝ) • ρ) z = (n : ℝ) • iteratedPartialDeriv α ρ z :=
    congrFun (iteratedPartialDeriv_const_smul (n : ℝ) α ρ) z
  rw [hsplit, hadd, hsm, iteratedPartialDeriv_fderiv_apply_self hρ α z]
  simp only [driftKernel, smul_eq_mul]
  ring

/-- **The commutator of mollification and the drift `x·∇`** on `ℝⁿ`, for a kernel `ρ` and a
locally integrable `g`: `-(g ∗ K)` with the kernel `K(z) = n ρ(z) + z·∇ρ(z)`. For `g` with a
weak gradient it is `ρ ∗ (x·∇g) - x·∇(ρ ∗ g)`. -/
def driftCommutator (ρ g : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  -(g ⋆[mul ℝ ℝ, volume] driftKernel ρ) x

/-- The commutator in two terms: `-(n (g ∗ ρ) + g ∗ κ)` with `κ(z) = z·∇ρ(z)`. -/
theorem driftCommutator_eq {g ρ : ℝ^n → ℝ} (hg : LocallyIntegrable g volume)
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (x : ℝ^n) :
    driftCommutator ρ g x =
      -(n * (g ⋆[mul ℝ ℝ, volume] ρ) x + (g ⋆[mul ℝ ℝ, volume] fun z ↦ fderiv ℝ ρ z z) x) := by
  have h1 : Integrable fun y ↦ g y * ρ (x - y) :=
    integrable_mul_comp_const_sub hg hρ.continuous hρc x
  have h2 : Integrable fun y ↦ g y * fderiv ℝ ρ (x - y) (x - y) :=
    integrable_mul_comp_const_sub (k := fun z ↦ fderiv ℝ ρ z z) hg
      (continuous_fderiv_apply_self hρ) (hasCompactSupport_fderiv_apply_self hρc) x
  unfold driftCommutator
  simp only [convolution_def, ContinuousLinearMap.mul_apply', driftKernel]
  rw [← integral_const_mul, ← integral_add (h1.const_mul _) h2]
  congr 1
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  beta_reduce
  ring

/-- **The commutator for a differentiated kernel**: with the kernel `∂^α ρ` in the place of
`ρ`, the commutator is `|α| (g ∗ ∂^α ρ) - g ∗ ∂^α K`. The first term is what changes the
coefficient `-½` of the self-similar equation into `-(1 + |α|)/2` after `|α|` derivatives. -/
theorem driftCommutator_iteratedPartialDeriv {g ρ : ℝ^n → ℝ} (hg : LocallyIntegrable g volume)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) (α : List (Fin n)) (x : ℝ^n) :
    driftCommutator (iteratedPartialDeriv α ρ) g x =
      α.length * (g ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv α ρ) x -
        (g ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv α (driftKernel ρ)) x := by
  have h1 : Integrable fun y ↦ g y * iteratedPartialDeriv α ρ (x - y) :=
    integrable_mul_comp_const_sub hg (contDiff_top_iteratedPartialDeriv hρ α).continuous
      (hρc.iteratedPartialDeriv α) x
  have h2 : Integrable fun y ↦ g y * iteratedPartialDeriv α (driftKernel ρ) (x - y) :=
    integrable_mul_comp_const_sub hg
      (contDiff_top_iteratedPartialDeriv (contDiff_driftKernel hρ) α).continuous
      ((hasCompactSupport_driftKernel hρc).iteratedPartialDeriv α) x
  unfold driftCommutator
  simp only [convolution_def, ContinuousLinearMap.mul_apply',
    driftKernel_iteratedPartialDeriv hρ α]
  rw [← integral_const_mul, ← integral_sub (h1.const_mul _) h2, ← integral_neg]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  beta_reduce
  ring

/-- The drift tested with a reflected translate of the kernel:
`∫ g(y) ∇ρ(x-y)·y dy = x·∇(g ∗ ρ)(x) - (g ∗ κ)(x)`, with `κ(z) = z·∇ρ(z)`. -/
theorem integral_mul_fderiv_comp_const_sub_apply_self {g ρ : ℝ^n → ℝ}
    (hg : LocallyIntegrable g volume) (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ)
    (x : ℝ^n) :
    ∫ y, g y * fderiv ℝ ρ (x - y) y =
      fderiv ℝ (g ⋆[mul ℝ ℝ, volume] ρ) x x -
        (g ⋆[mul ℝ ℝ, volume] fun z ↦ fderiv ℝ ρ z z) x := by
  have hD : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv one_ne_zero
  have h1 : Integrable fun y ↦ g y * fderiv ℝ ρ (x - y) x :=
    integrable_mul_comp_const_sub (k := fun z ↦ fderiv ℝ ρ z x) hg
      (hD.clm_apply continuous_const) (hρc.fderiv_apply ℝ x) x
  have h2 : Integrable fun y ↦ g y * fderiv ℝ ρ (x - y) (x - y) :=
    integrable_mul_comp_const_sub (k := fun z ↦ fderiv ℝ ρ z z) hg
      (continuous_fderiv_apply_self hρ) (hasCompactSupport_fderiv_apply_self hρc) x
  rw [fderiv_convolution_right_apply hg hρc hρ x x, convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  rw [← integral_sub h1 h2]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  beta_reduce
  rw [map_sub]
  ring

/-- `y ↦ g(y) ∇ρ(x-y)·y` is integrable. -/
theorem integrable_mul_fderiv_comp_const_sub_apply_self {g ρ : ℝ^n → ℝ}
    (hg : LocallyIntegrable g volume) (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ)
    (x : ℝ^n) : Integrable fun y ↦ g y * fderiv ℝ ρ (x - y) y := by
  have hD : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv one_ne_zero
  have h1 : Integrable fun y ↦ g y * fderiv ℝ ρ (x - y) x :=
    integrable_mul_comp_const_sub (k := fun z ↦ fderiv ℝ ρ z x) hg
      (hD.clm_apply continuous_const) (hρc.fderiv_apply ℝ x) x
  have h2 : Integrable fun y ↦ g y * fderiv ℝ ρ (x - y) (x - y) :=
    integrable_mul_comp_const_sub (k := fun z ↦ fderiv ℝ ρ z z) hg
      (continuous_fderiv_apply_self hρ) (hasCompactSupport_fderiv_apply_self hρc) x
  refine (h1.sub h2).congr (.of_forall fun y ↦ ?_)
  beta_reduce
  rw [Pi.sub_apply, map_sub]
  ring

/-- **Mollification of the tested self-similar equation.** Let `g`, `P` and `N₁, …, Nₙ` be
locally integrable on `ℝⁿ`, let `F` be a function, and suppose that for every test function
`ψ`

`∫ (g ψ + ½ g (x·∇ψ) - g Δψ - Σⱼ Nⱼ ∂ⱼψ) = ∫ F ψ + ∫ P ∂ᵢψ`,

which is the weak form of `(1 - n/2) g - ½ x·∇g - Δg + Σⱼ ∂ⱼNⱼ + ∂ᵢP = F`. Then for every
smooth compactly supported kernel `ρ` the mollifications satisfy at every point

`(1 - n/2) (g ∗ ρ) - ½ x·∇(g ∗ ρ) - ½ [ρ∗, x·∇]g - Δ(g ∗ ρ) + Σⱼ ∂ⱼ(Nⱼ ∗ ρ) + ∂ᵢ(P ∗ ρ)
  = F ∗ ρ`. -/
theorem mollified_similarity_eq {g F P : ℝ^n → ℝ} {N : Fin n → ℝ^n → ℝ} (i : Fin n)
    (hg : LocallyIntegrable g volume) (hP : LocallyIntegrable P volume)
    (hN : ∀ j, LocallyIntegrable (N j) volume)
    (htest : ∀ ψ : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ y, (g y * ψ y + (1 / 2 : ℝ) * (g y * fderiv ℝ ψ y y) - g y * laplacian ψ y -
        ∑ j, N j y * ∂[j] ψ y) = (∫ y, F y * ψ y) + ∫ y, P y * ∂[i] ψ y)
    {ρ : ℝ^n → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) (x : ℝ^n) :
    (1 - n / 2 : ℝ) * (g ⋆[mul ℝ ℝ, volume] ρ) x -
        (1 / 2 : ℝ) * fderiv ℝ (g ⋆[mul ℝ ℝ, volume] ρ) x x -
        (1 / 2 : ℝ) * driftCommutator ρ g x - laplacian (g ⋆[mul ℝ ℝ, volume] ρ) x +
        (∑ j, ∂[j] (N j ⋆[mul ℝ ℝ, volume] ρ) x) + ∂[i] (P ⋆[mul ℝ ℝ, volume] ρ) x =
      (F ⋆[mul ℝ ℝ, volume] ρ) x := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have hρ2 : ContDiff ℝ 2 ρ := hρ.of_le (by simp)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ ρ (x - y)) := hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y ↦ ρ (x - y)) :=
    hρc.comp_homeomorph (Homeomorph.subLeft x)
  have h := htest _ hψ hψc
  have hD : ∀ y h, fderiv ℝ (fun y ↦ ρ (x - y)) y h = -fderiv ℝ ρ (x - y) h := fun y h ↦ by
    have hc : HasFDerivAt (fun y : ℝ^n ↦ x - y) (-ContinuousLinearMap.id ℝ (ℝ^n)) y :=
      (hasFDerivAt_id y).const_sub x
    have hfd : HasFDerivAt (fun y ↦ ρ (x - y))
        ((fderiv ℝ ρ (x - y)).comp (-ContinuousLinearMap.id ℝ (ℝ^n))) y :=
      (hρ.differentiable (by simp) (x - y)).hasFDerivAt.comp y hc
    rw [hfd.fderiv]
    simp
  have hpd : ∀ (j : Fin n) y, ∂[j] (fun y ↦ ρ (x - y)) y = -∂[j] ρ (x - y) := fun j y ↦ hD y _
  simp only [hD, hpd, LaplacianEquation.laplacian_comp_const_sub hρ] at h
  -- The integrable pieces.
  have iA : Integrable fun y ↦ g y * ρ (x - y) :=
    integrable_mul_comp_const_sub hg hρ.continuous hρc x
  have iB := integrable_mul_fderiv_comp_const_sub_apply_self hg hρc hρ1 x
  have iC : Integrable fun y ↦ g y * laplacian ρ (x - y) :=
    integrable_mul_comp_const_sub hg (PDE.contDiff_laplacian_coord hρ).continuous
      hρc.coordinate_laplacian x
  have iD : ∀ j, Integrable fun y ↦ N j y * ∂[j] ρ (x - y) := fun j ↦
    integrable_mul_comp_const_sub (hN j) (hρ1.continuous_partialDeriv j) (hρc.partialDeriv j) x
  have iS : Integrable fun y ↦ ∑ j, N j y * ∂[j] ρ (x - y) :=
    integrable_finsetSum _ fun j _ ↦ iD j
  have i1 : Integrable fun y ↦ g y * ρ (x - y) -
      (1 / 2 : ℝ) * (g y * fderiv ℝ ρ (x - y) y) := iA.sub (iB.const_mul _)
  have i2 : Integrable fun y ↦ g y * ρ (x - y) -
      (1 / 2 : ℝ) * (g y * fderiv ℝ ρ (x - y) y) - g y * laplacian ρ (x - y) := i1.sub iC
  have e : ∀ y, g y * ρ (x - y) + (1 / 2 : ℝ) * (g y * -fderiv ℝ ρ (x - y) y) -
      g y * laplacian ρ (x - y) - ∑ j, N j y * -∂[j] ρ (x - y) =
      g y * ρ (x - y) - (1 / 2 : ℝ) * (g y * fderiv ℝ ρ (x - y) y) -
        g y * laplacian ρ (x - y) + ∑ j, N j y * ∂[j] ρ (x - y) := fun y ↦ by
    simp only [mul_neg, Finset.sum_neg_distrib]
    ring
  rw [integral_congr_ae (.of_forall e), integral_add i2 iS, integral_sub i1 iC,
    integral_sub iA (iB.const_mul _), integral_const_mul,
    integral_finsetSum _ fun j _ ↦ iD j] at h
  -- Each integral is a mollification or a derivative of one.
  have eA : ∫ y, g y * ρ (x - y) = (g ⋆[mul ℝ ℝ, volume] ρ) x := rfl
  have eB := integral_mul_fderiv_comp_const_sub_apply_self hg hρc hρ1 x
  have eC : ∫ y, g y * laplacian ρ (x - y) = laplacian (g ⋆[mul ℝ ℝ, volume] ρ) x :=
    (PDE.laplacian_convolution_right hg hρc hρ2 x).symm
  have eD : ∀ j, ∫ y, N j y * ∂[j] ρ (x - y) = ∂[j] (N j ⋆[mul ℝ ℝ, volume] ρ) x := fun j ↦
    (convolution_partialDeriv_right (N j) ρ (hN j) hρc hρ1 j x).symm
  have eF : ∫ y, F y * ρ (x - y) = (F ⋆[mul ℝ ℝ, volume] ρ) x := rfl
  have eP : ∫ y, P y * -∂[i] ρ (x - y) = -∂[i] (P ⋆[mul ℝ ℝ, volume] ρ) x := by
    have h1 : ∫ y, P y * ∂[i] ρ (x - y) = ∂[i] (P ⋆[mul ℝ ℝ, volume] ρ) x :=
      (convolution_partialDeriv_right P ρ hP hρc hρ1 i x).symm
    rw [← h1, ← integral_neg]
    exact integral_congr_ae (.of_forall fun y ↦ mul_neg _ _)
  simp only [eD] at h
  rw [eA, eB, eC, eF, eP] at h
  rw [driftCommutator_eq hg hρc hρ1 x]
  linear_combination h

end PDE.Analysis
