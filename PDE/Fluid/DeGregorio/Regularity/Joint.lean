/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.Parametric.Smooth
public import PDE.Fluid.DeGregorio.Uniqueness.Classical
import PDE.Analysis.Calculus.MixedDerivative

/-!
# Joint smoothness of De Gregorio solutions

Let `ω` solve `ω_t = c ω - u ω_x`, with `c = H ω` and `u (x) = ∫₀ˣ c`, on `ℝ × (0, T)`. If `ω` is
spatially smooth on `[0, T]` (smooth slices and jointly continuous spatial derivatives of every
order) and vanishes outside one bounded interval, then `ω` is `C^∞` on `ℝ × [0, T]`, with
one-sided time derivatives at the endpoints.

The equation expresses `∂ₜ ∂ₓᵏ ω` as `∂ₓᵏ (c ω - u ω_x)` (mixed derivatives commute on the
closed slab), which is built from `ω`, its spatial derivatives, its Hilbert transform and the
primitive of that. Each of these operations preserves the number of time derivatives
(`IsTimeSmooth`), so induction on that number gives every time derivative.

For a classical solution on `[0, T)` (`IsClassicalSolutionFrom`) with smooth slices and jointly
continuous spatial derivatives, applying this on every `[0, T']` with `T' < T` gives `C^∞`
regularity on `ℝ × [0, T)`.

## Main results

* `contDiffOn_of_isSpatiallySmooth`: joint smoothness on a closed slab.
* `IsClassicalSolutionFrom.contDiffOn_fields`: joint smoothness of the vorticity and the velocity
  on `ℝ × [0, T)`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology ContDiff

namespace DeGregorio

/-- A solution of `ω_t = (H ω) ω - u ω_x`, `u = ∫₀ˣ H ω`, on `ℝ × (0, T)` which is spatially smooth
on `[0, T]` and vanishes outside one bounded interval has every number of time derivatives. -/
theorem isTimeSmooth_of_isSpatiallySmooth {T : ℝ} (hT : 0 < T) {v : ℝ → ℝ → ℝ}
    (hs : IsSpatiallySmooth T v) (hb : HasBoundedSupport T v)
    (heq : ∀ x, ∀ t ∈ Ioo 0 T, HasDerivAt (v x)
      (hilbertPVX v x t * v x t +
        (-1) * (primitiveX (hilbertPVX v) x t * derivX v x t)) t) (n : ℕ) :
    IsTimeSmooth T n v := by
  let r₀ : ℝ → ℝ → ℝ := fun x t ↦ hilbertPVX v x t * v x t +
    (-1) * (primitiveX (hilbertPVX v) x t * derivX v x t)
  let w : ℕ → ℝ → ℝ → ℝ := fun k ↦ derivX^[k] v
  let r : ℕ → ℝ → ℝ → ℝ := fun k ↦ derivX^[k] r₀
  have hws (k : ℕ) : IsSpatiallySmooth T (w k) := by
    induction k with
    | zero => exact hs
    | succ k ih =>
      simp only [w, Function.iterate_succ_apply']
      exact ih.derivX
  have hc := hs.hilbertPVX hb
  have hr₀s : IsSpatiallySmooth T r₀ :=
    (hc.mul hs).add ((IsSpatiallySmooth.const T (-1)).mul (hc.primitiveX.mul hs.derivX))
  have hrs (k : ℕ) : IsSpatiallySmooth T (r k) := by
    induction k with
    | zero => exact hr₀s
    | succ k ih =>
      simp only [r, Function.iterate_succ_apply']
      exact ih.derivX
  -- The time derivatives of the spatial derivatives.
  have hrel (k : ℕ) : ∀ x, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (w k x) (r k x t) (Icc 0 T) t := by
    induction k with
    | zero =>
      intro x
      exact hasDerivWithinAt_Icc_of_interior (hs.continuousOn_time x)
        (hr₀s.continuousOn_time x) (heq x)
    | succ k ih =>
      intro x t ht
      have hwk := hws k
      have hrk := hrs k
      have h := hasDerivWithinAt_spatial_deriv_of_continuous_transport hT
        (g := w k) (r := r k) (d := derivX (r k))
        (by simpa only [Function.iterate_zero, id] using hwk.continuous 0)
        (by simpa only [Function.iterate_zero, id] using hrk.continuous 0)
        (hrk.continuous 1)
        (fun t ht ↦ (hwk.contDiff t ht).differentiable (by simp))
        (fun x t ht ↦ ((hrk.contDiff t ht).differentiable (by simp) x).hasDerivAt)
        (fun x t ht ↦ (ih x t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
        x ht
      simp only [w, r, Function.iterate_succ_apply']
      exact h
  -- Every number of time derivatives.
  have hclaim (n : ℕ) : ∀ k, IsTimeSmooth T n (w k) := by
    induction n with
    | zero => exact hws
    | succ n ih =>
      intro k
      have hv : IsTimeSmooth T n v := ih 0
      have hv₁ : IsTimeSmooth T n (derivX v) := ih 1
      have hcn := IsTimeSmooth.hilbertPVX hT hv hb
      have hr₀n : IsTimeSmooth T n r₀ :=
        (hcn.mul hv).add ((IsTimeSmooth.const (-1) n).mul
          ((IsTimeSmooth.primitiveX hT hcn).mul hv₁))
      have hrn : IsTimeSmooth T n (r k) := by
        clear hrel
        induction k with
        | zero => exact hr₀n
        | succ k ihk =>
          simp only [r, Function.iterate_succ_apply']
          exact IsTimeSmooth.derivX hT ihk
      exact ⟨hws k, r k, hrn, hrel k⟩
  exact hclaim n 0

/-- Under the hypotheses of `isTimeSmooth_of_isSpatiallySmooth`, the vorticity and the velocity
`u = ∫₀ˣ H ω` are `C^∞` on `ℝ × [0, T]`. -/
theorem contDiffOn_of_isSpatiallySmooth {T : ℝ} (hT : 0 < T) {v : ℝ → ℝ → ℝ}
    (hs : IsSpatiallySmooth T v) (hb : HasBoundedSupport T v)
    (heq : ∀ x, ∀ t ∈ Ioo 0 T, HasDerivAt (v x)
      (hilbertPVX v x t * v x t +
        (-1) * (primitiveX (hilbertPVX v) x t * derivX v x t)) t) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ v p.1 p.2) (univ ×ˢ Icc 0 T) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ primitiveX (hilbertPVX v) p.1 p.2)
        (univ ×ˢ Icc 0 T) := by
  have h := isTimeSmooth_of_isSpatiallySmooth hT hs hb heq
  refine ⟨contDiffOn_infty.mpr fun n ↦ IsTimeSmooth.contDiffOn hT (h n),
    contDiffOn_infty.mpr fun n ↦ IsTimeSmooth.contDiffOn hT ?_⟩
  exact IsTimeSmooth.primitiveX hT (IsTimeSmooth.hilbertPVX hT (h n) hb)

namespace IsClassicalSolutionFrom

variable {w₀ : ℝ → ℝ} {T : ℝ} {fields : Fields}

/-- At positive times the equation reads `∂ₜ ω = (H ω) ω - u ω_x` with `u = ∫₀ˣ H ω`. -/
theorem hasDerivAt_vorticity_time (h : IsClassicalSolutionFrom w₀ T fields) {t : ℝ}
    (ht : t ∈ Ioo 0 T) (x : ℝ) :
    HasDerivAt (fields.vorticity x)
      (hilbertPVX fields.vorticity x t * fields.vorticity x t +
        (-1) * (primitiveX (hilbertPVX fields.vorticity) x t *
          derivX fields.vorticity x t)) t := by
  have htI : t ∈ Ico 0 T := Ioo_subset_Ico_self ht
  have hd := ((h.isClassicalSolutionOn subset_rfl).regularity.vorticity_time_differentiableAt
    (x := x) ht).hasDerivAt
  have htr := h.transport (x := x) ht
  have hu : (fun y ↦ fields.velocity y t) = fun y ↦
      primitiveX (hilbertPVX fields.vorticity) y t := h.velocity_eq htI
  have hux : deriv (fun y ↦ fields.velocity y t) x = hilbertPVX fields.vorticity x t := by
    rw [hu]
    exact (hasDerivAt_hilbertPVVelocity_of_contDiff_one_compactSupport
      (h.contDiff_one_vorticity htI) (h.hasCompactSupport_vorticity htI) x).deriv
  have hux0 : fields.velocity x t = primitiveX (hilbertPVX fields.vorticity) x t :=
    congrFun hu x
  rw [hux, hux0, one_mul] at htr
  convert hd using 1
  simp only [derivX]
  linarith

/-- Joint smoothness. A classical solution on `[0, T)` with `C^∞` vorticity slices whose spatial
derivatives of every order are jointly continuous on `ℝ × [0, T)` has `C^∞` vorticity and
velocity on `ℝ × [0, T)`, with one-sided time derivatives at `t = 0`. -/
theorem contDiffOn_fields (h : IsClassicalSolutionFrom w₀ T fields)
    (hsmooth : ∀ t ∈ Ico 0 T, ContDiff ℝ ∞ (fun x ↦ fields.vorticity x t))
    (hcont : ∀ k : ℕ, ContinuousOn (fun q : ℝ × ℝ ↦
      deriv^[k] (fun y ↦ fields.vorticity y q.2) q.1) (univ ×ˢ Ico 0 T)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ fields.vorticity p.1 p.2) (univ ×ˢ Ico 0 T) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ fields.velocity p.1 p.2) (univ ×ˢ Ico 0 T) := by
  have hvel : ∀ p ∈ (univ : Set ℝ) ×ˢ Ico 0 T, fields.velocity p.1 p.2 =
      primitiveX (hilbertPVX fields.vorticity) p.1 p.2 :=
    fun p hp ↦ congrFun (h.velocity_eq hp.2) p.1
  have hloc : ∀ p ∈ (univ : Set ℝ) ×ˢ Ico 0 T, ∃ u, IsOpen u ∧ p ∈ u ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ fields.vorticity p.1 p.2) ((univ ×ˢ Ico 0 T) ∩ u) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ primitiveX (hilbertPVX fields.vorticity) p.1 p.2)
        ((univ ×ˢ Ico 0 T) ∩ u) := by
    intro p hp
    set T' := (p.2 + T) / 2 with hT'
    have hpT' : p.2 < T' := by rw [hT']; linarith [hp.2.2]
    have hT'T : T' < T := by rw [hT']; linarith [hp.2.2]
    have hT'0 : 0 < T' := lt_of_le_of_lt hp.2.1 hpT'
    refine ⟨univ ×ˢ Iio T', isOpen_univ.prod isOpen_Iio, ⟨mem_univ _, hpT'⟩, ?_⟩
    have hsub : (univ : Set ℝ) ×ˢ Icc 0 T' ⊆ univ ×ˢ Ico 0 T :=
      fun q hq ↦ ⟨mem_univ _, hq.2.1, hq.2.2.trans_lt hT'T⟩
    have hs : IsSpatiallySmooth T' fields.vorticity :=
      { contDiff := fun t ht ↦ hsmooth t ⟨ht.1, ht.2.trans_lt hT'T⟩
        continuous := fun k ↦ ((hcont k).mono hsub).comp_continuous
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
          (fun z ↦ ⟨mem_univ _, z.2.property⟩) }
    obtain ⟨L, hL⟩ := h.support T' hT'T
    have hslab := contDiffOn_of_isSpatiallySmooth hT'0 hs ⟨L, hL⟩
      (fun x t ht ↦ h.hasDerivAt_vorticity_time ⟨ht.1, ht.2.trans hT'T⟩ x)
    have hsub' : (univ ×ˢ Ico 0 T) ∩ (univ ×ˢ Iio T') ⊆ (univ : Set ℝ) ×ˢ Icc 0 T' :=
      fun q hq ↦ ⟨mem_univ _, hq.1.2.1, hq.2.2.le⟩
    exact ⟨hslab.1.mono hsub', hslab.2.mono hsub'⟩
  refine ⟨contDiffOn_of_locally_contDiffOn fun p hp ↦ ?_,
    (contDiffOn_of_locally_contDiffOn fun p hp ↦ ?_).congr hvel⟩
  · obtain ⟨u, hu, hpu, h1, -⟩ := hloc p hp
    exact ⟨u, hu, hpu, h1⟩
  · obtain ⟨u, hu, hpu, -, h2⟩ := hloc p hp
    exact ⟨u, hu, hpu, h2⟩

end IsClassicalSolutionFrom

end DeGregorio
