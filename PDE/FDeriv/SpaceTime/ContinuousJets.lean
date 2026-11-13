/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators

/-!
# Coordinate jets from continuous spatial derivative fields

Given fields `Dx`, `Dxx` that are the first and second spatial Fréchet derivatives
of every time slice, the coordinate derivatives of the slices are their values on
basis vectors. Joint continuity of `Dx`, `Dxx` then gives joint continuity of those
coordinate jets on the same time set.
No time derivative, mixed derivative, or extension across a temporal endpoint
is required.
-/

@[expose] public section

open PDE (partialDeriv laplacian)

open Filter Set
open scoped Topology

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- If `Dxx` is the spatial derivative of the spatial derivative field `Dx`, the mixed
coordinate derivatives of each slice are the values of `Dxx` on basis vectors. The time set
is arbitrary. -/
theorem secondPartialDeriv_spatial_eq_of_hasFDerivAt
    {Ω : Set (ℝ^n)} {I : Set ℝ} {u : ℝ^n → ℝ → F}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] F}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] F}
    (hΩ : IsOpen Ω)
    (hspace : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (hhessian : ∀ p ∈ Ω ×ˢ I,
      HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1)
    {p : ℝ^n × ℝ} (hp : p ∈ Ω ×ˢ I) (i j : Fin n) :
    (∂[i] (∂[j] (fun x ↦ u x p.2))) p.1 =
      Dxx p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have heq :
      (∂[j] (fun x ↦ u x p.2)) =ᶠ[𝓝 p.1]
        fun x ↦ Dx (x, p.2) (EuclideanSpace.single j 1) := by
    filter_upwards [hΩ.mem_nhds hp.1] with x hx
    simp only [partialDeriv, (hspace (x, p.2) ⟨hx, hp.2⟩).fderiv]
  change fderiv ℝ (∂[j] (fun x ↦ u x p.2)) p.1
    (EuclideanSpace.single i 1) = _
  rw [heq.fderiv_eq]
  have hd := (hhessian p hp).clm_apply
    (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ)) p.1)
  rw [hd.fderiv]
  simp

/-- A jointly continuous first spatial derivative field gives continuous
coordinate derivatives on the same domain, including its temporal endpoints. -/
theorem continuousOn_partialDeriv_spatial_of_hasFDerivAt
    {Ω : Set (ℝ^n)} {I : Set ℝ} {u : ℝ^n → ℝ → F}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] F}
    (hDx : ContinuousOn Dx (Ω ×ˢ I))
    (hspace : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (i : Fin n) :
    ContinuousOn (fun p : ℝ^n × ℝ ↦
      (∂[i] (fun x ↦ u x p.2)) p.1) (Ω ×ˢ I) := by
  apply (hDx.clm_apply (continuousOn_const (c := EuclideanSpace.single i (1 : ℝ)))).congr
  intro p hp
  simp only [partialDeriv, (hspace p hp).fderiv]

/-- A jointly continuous spatial Hessian field gives jointly continuous mixed
coordinate derivatives, with no mixed spatial-time regularity assumption. -/
theorem continuousOn_secondPartialDeriv_spatial_of_hasFDerivAt
    {Ω : Set (ℝ^n)} {I : Set ℝ} {u : ℝ^n → ℝ → F}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] F}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] F}
    (hΩ : IsOpen Ω) (hDxx : ContinuousOn Dxx (Ω ×ˢ I))
    (hspace : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (hhessian : ∀ p ∈ Ω ×ˢ I,
      HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1)
    (i j : Fin n) :
    ContinuousOn (fun p : ℝ^n × ℝ ↦
      (∂[i] (∂[j] (fun x ↦ u x p.2))) p.1) (Ω ×ˢ I) := by
  apply ((hDxx.clm_apply
    (continuousOn_const (c := EuclideanSpace.single i (1 : ℝ)))).clm_apply
    (continuousOn_const (c := EuclideanSpace.single j (1 : ℝ)))).congr
  intro p hp
  exact secondPartialDeriv_spatial_eq_of_hasFDerivAt hΩ hspace hhessian hp i j

/-- The coordinate Laplacian of the time slices is jointly continuous when the spatial
Hessian field is jointly continuous. The time set is arbitrary. -/
theorem continuousOn_laplacian_spatial_of_hasFDerivAt
    {Ω : Set (ℝ^n)} {I : Set ℝ} {u : ℝ^n → ℝ → ℝ}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ}
    (hΩ : IsOpen Ω) (hDxx : ContinuousOn Dxx (Ω ×ˢ I))
    (hspace : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (hhessian : ∀ p ∈ Ω ×ˢ I,
      HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1) :
    ContinuousOn (fun p : ℝ^n × ℝ ↦ laplacian (fun x ↦ u x p.2) p.1)
      (Ω ×ˢ I) := by
  unfold laplacian
  apply continuousOn_finsetSum
  intro i _
  exact continuousOn_secondPartialDeriv_spatial_of_hasFDerivAt hΩ hDxx hspace hhessian i i

end PDE
