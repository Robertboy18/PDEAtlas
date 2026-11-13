/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
import PDE.FDeriv.Calculus
import CAS.ExactTactic

/-!
# Local product rule for the coordinate Laplacian

Only `C²` regularity near the evaluation point is needed. The proof first
differentiates the coordinate product rule on a neighborhood and then sums the
diagonal second derivatives. These identities apply to local cutoffs without
requiring a globally regular extension of either factor.
-/

@[expose] public section

open PDE (laplacian)

open Filter
open scoped Topology

variable {n : ℕ}

namespace PDE

/-- The second mixed coordinate derivative of a product at a `C²` point. -/
theorem secondPartialDeriv_mul (i j : Fin n)
    {f g : ℝ^n → ℝ} {x : ℝ^n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (∂[i] (fun y ↦ (∂[j] (fun z ↦ f z * g z)) y)) x =
      (∂[i] (fun y ↦ (∂[j] f) y)) x * g x +
        (∂[j] f) x * (∂[i] g) x +
        (∂[i] f) x * (∂[j] g) x +
        f x * (∂[i] (fun y ↦ (∂[j] g) y)) x := by
  have hfirst :
      (fun y ↦ (∂[j] (fun z ↦ f z * g z)) y) =ᶠ[𝓝 x]
        fun y ↦ (∂[j] f) y * g y + f y * (∂[j] g) y := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)]
      with y hfy hgy
    exact partialDeriv_mul (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  have hdf := hf.differentiableAt (by norm_num)
  have hdg := hg.differentiableAt (by norm_num)
  have hdjf := (contDiffAt_partialDeriv 1 hf j).differentiableAt (by norm_num)
  have hdjg := (contDiffAt_partialDeriv 1 hg j).differentiableAt (by norm_num)
  rw [partialDeriv_congr_nhds i hfirst,
    partialDeriv_add (hdjf.fun_mul hdg) (hdf.fun_mul hdjg),
    partialDeriv_mul hdjf hdg, partialDeriv_mul hdf hdjg]
  cas

/-- The local product formula `Δ(fg)=gΔf+2∑ᵢ∂ᵢf∂ᵢg+fΔg`
for LeanPDE's native coordinate Laplacian. -/
theorem laplacian_mul {f g : ℝ^n → ℝ} {x : ℝ^n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    laplacian (fun y ↦ f y * g y) x =
      laplacian f x * g x +
        2 * (∑ i : Fin n, (∂[i] f) x * (∂[i] g) x) +
        f x * laplacian g x := by
  have hdiag (i : Fin n) :
      (∂[i] (fun y ↦ (∂[i] (fun z ↦ f z * g z)) y)) x =
        (∂[i] (fun y ↦ (∂[i] f) y)) x * g x +
          2 * ((∂[i] f) x * (∂[i] g) x) +
          f x * (∂[i] (fun y ↦ (∂[i] g) y)) x := by
    rw [secondPartialDeriv_mul i i hf hg]
    cas
  simp only [laplacian, hdiag, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum]

end PDE
