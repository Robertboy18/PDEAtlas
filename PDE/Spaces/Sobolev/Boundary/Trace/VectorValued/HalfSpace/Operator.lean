/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Estimate
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Density

/-!
# The Banach-valued finite-exponent half-space trace

Boundary restriction is first defined on Sobolev elements admitting compact
ambient `C¹` representatives. The smooth trace estimate makes this restriction independent
of the representative. Compact smooth density then gives a bounded linear trace on the
whole graph, retaining literal boundary evaluation for every compact `C¹` representative.
-/

public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open GraphSpace SobolevSpace.Trace.HalfSpace

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private def compactC1Submodule (n : ℕ) (p : ℝ)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :
    Submodule ℝ
      W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F) where
  carrier := {U | ∃ f : ℝ^(n + 1) → F, ContDiff ℝ 1 f ∧ HasCompactSupport f ∧
    (U.val (baseIndex (n + 1) 1) : ℝ^(n + 1) → F) =ᵐ[volume.restrict ℝ^(n + 1)₊] f}
  zero_mem' := ⟨0, contDiff_const, HasCompactSupport.zero,
    Lp.coeFn_zero F (ENNReal.ofReal p) _⟩
  add_mem' := by
    rintro U V ⟨f, hf, hfc, hU⟩ ⟨g, hg, hgc, hV⟩
    refine ⟨f + g, hf.add hg, hfc.add hgc, ?_⟩
    exact (Lp.coeFn_add (U.val (baseIndex (n + 1) 1))
      (V.val (baseIndex (n + 1) 1))).trans (hU.add hV)
  smul_mem' := by
    rintro c U ⟨f, hf, hfc, hU⟩
    refine ⟨c • f, hf.const_smul c, hfc.smul_left (f := fun _ ↦ c), ?_⟩
    exact (Lp.coeFn_smul c (U.val (baseIndex (n + 1) 1))).trans (hU.const_smul c)

private theorem denseRange_compactC1Submodule :
    DenseRange (compactC1Submodule n p F).subtype := by
  have hd := dense_compact_smooth (n := n) (F := F) (p := ENNReal.ofReal p)
    ENNReal.ofReal_ne_top
  apply hd.mono
  rintro U ⟨f, hf, hfc, hU⟩
  exact ⟨⟨U, f, hf.of_le (by simp), hfc, hU⟩, rfl⟩

omit [Fact (1 ≤ ENNReal.ofReal p)] [CompleteSpace F] in
private theorem smoothBoundaryLp_sub {f g : ℝ^(n + 1) → F}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    smoothBoundaryLp (p := ENNReal.ofReal p) (hf.sub hg).continuous (hfc.sub hgc) =
      smoothBoundaryLp hf.continuous hfc - smoothBoundaryLp hg.continuous hgc := by
  apply Lp.ext
  filter_upwards [smoothBoundaryLp_coeFn_ae (hf.sub hg).continuous (hfc.sub hgc),
    Lp.coeFn_sub (smoothBoundaryLp (p := ENNReal.ofReal p) hf.continuous hfc)
      (smoothBoundaryLp hg.continuous hgc),
    smoothBoundaryLp_coeFn_ae (p := ENNReal.ofReal p) hf.continuous hfc,
    smoothBoundaryLp_coeFn_ae (p := ENNReal.ofReal p) hg.continuous hgc] with y hsub hl hf' hg'
  rw [hsub, hl, Pi.sub_apply, hf', hg']
  rfl

private theorem smoothBoundaryLp_eq_of_base_ae (hp : 1 ≤ p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F))
    {f g : ℝ^(n + 1) → F} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hU : (U.val (baseIndex (n + 1) 1) : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] f)
    (hV : (U.val (baseIndex (n + 1) 1) : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] g) :
    smoothBoundaryLp (p := ENNReal.ofReal p) hf.continuous hfc =
      smoothBoundaryLp hg.continuous hgc := by
  have hzero :
      ((0 :
        W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)).val
        (baseIndex (n + 1) 1) : ℝ^(n + 1) → F) =ᵐ[volume.restrict ℝ^(n + 1)₊] f - g := by
    filter_upwards [Lp.coeFn_zero F (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊),
      hU, hV] with x hz hx hy
    change (0 : Lp F (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊)) x = f x - g x
    rw [hz, ← hx, ← hy, sub_self]
    rfl
  have h := norm_smoothBoundaryLp_le hp 0 (hf.sub hg) (hfc.sub hgc) hzero
  rw [smoothBoundaryLp_sub hf hg hfc hgc, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

private def compactC1Boundary (U : compactC1Submodule n p F) :
    Lp F (ENNReal.ofReal p) (volume : Measure (ℝ^n)) :=
  smoothBoundaryLp U.property.choose_spec.1.continuous U.property.choose_spec.2.1

private theorem compactC1Boundary_eq (hp : 1 ≤ p) (U : compactC1Submodule n p F)
    {f : ℝ^(n + 1) → F} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hU : (U.val.val (baseIndex (n + 1) 1) : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] f) :
    compactC1Boundary U = smoothBoundaryLp hf.continuous hfc :=
  smoothBoundaryLp_eq_of_base_ae hp U.val U.property.choose_spec.1 hf
    U.property.choose_spec.2.1 hfc U.property.choose_spec.2.2 hU

private theorem compactC1Boundary_add (hp : 1 ≤ p)
    (U V : compactC1Submodule n p F) :
    compactC1Boundary (U + V) = compactC1Boundary U + compactC1Boundary V := by
  obtain ⟨f, hf, hfc, hU⟩ := U.property
  obtain ⟨g, hg, hgc, hV⟩ := V.property
  rw [compactC1Boundary_eq hp U hf hfc hU, compactC1Boundary_eq hp V hg hgc hV,
    compactC1Boundary_eq hp (U + V) (hf.add hg) (hfc.add hgc)
      ((Lp.coeFn_add (U.val.val (baseIndex (n + 1) 1))
        (V.val.val (baseIndex (n + 1) 1))).trans (hU.add hV))]
  apply Lp.ext
  filter_upwards [smoothBoundaryLp_coeFn_ae (hf.add hg).continuous (hfc.add hgc),
    Lp.coeFn_add (smoothBoundaryLp (p := ENNReal.ofReal p) hf.continuous hfc)
      (smoothBoundaryLp hg.continuous hgc),
    smoothBoundaryLp_coeFn_ae (p := ENNReal.ofReal p) hf.continuous hfc,
    smoothBoundaryLp_coeFn_ae (p := ENNReal.ofReal p) hg.continuous hgc] with y ha hl hf' hg'
  rw [ha, hl, Pi.add_apply, hf', hg']
  rfl

private theorem compactC1Boundary_smul (hp : 1 ≤ p)
    (c : ℝ) (U : compactC1Submodule n p F) :
    compactC1Boundary (c • U) = c • compactC1Boundary U := by
  obtain ⟨f, hf, hfc, hU⟩ := U.property
  rw [compactC1Boundary_eq hp U hf hfc hU,
    compactC1Boundary_eq hp (c • U) (hf.const_smul c) (hfc.smul_left (f := fun _ ↦ c))
      ((Lp.coeFn_smul c (U.val.val (baseIndex (n + 1) 1))).trans (hU.const_smul c))]
  apply Lp.ext
  filter_upwards [smoothBoundaryLp_coeFn_ae (hf.const_smul c).continuous
    (hfc.smul_left (f := fun _ ↦ c)),
    Lp.coeFn_smul c (smoothBoundaryLp (p := ENNReal.ofReal p) hf.continuous hfc),
    smoothBoundaryLp_coeFn_ae (p := ENNReal.ofReal p) hf.continuous hfc] with y ha hl hf'
  rw [ha, hl, Pi.smul_apply, hf']
  rfl

private def compactC1BoundaryLinear (hp : 1 ≤ p) :
    compactC1Submodule n p F →ₗ[ℝ] Lp F (ENNReal.ofReal p) (volume : Measure (ℝ^n)) where
  toFun := compactC1Boundary
  map_add' := compactC1Boundary_add hp
  map_smul' := compactC1Boundary_smul hp

private theorem norm_compactC1BoundaryLinear_le (hp : 1 ≤ p)
    (U : compactC1Submodule n p F) :
    ‖compactC1BoundaryLinear hp U‖ ≤ p ^ (1 / p) * ‖U.val‖ :=
  norm_smoothBoundaryLp_le hp U.val U.property.choose_spec.1
    U.property.choose_spec.2.1 U.property.choose_spec.2.2

/-- The bounded trace of a Banach-valued first-order Sobolev element on the upper
half-space, for every finite real exponent at least one. -/
def traceLp (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p) :
    W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F) →L[ℝ]
        Lp F (ENNReal.ofReal p) (volume : Measure (ℝ^n)) :=
  (compactC1BoundaryLinear hp).extendOfNorm (compactC1Submodule n p F).subtype

/-- The trace of any compact ambient `C¹` representative is its literal boundary
restriction. Agreement of the base coordinate on the half-space suffices. -/
theorem traceLp_c1 (hp : 1 ≤ p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F))
    {f : ℝ^(n + 1) → F} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hU : (U.val (baseIndex (n + 1) 1) : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] f) :
    traceLp n p hp U = smoothBoundaryLp hf.continuous hfc := by
  let V : compactC1Submodule n p F := ⟨U, f, hf, hfc, hU⟩
  exact (LinearMap.extendOfNorm_eq (f := compactC1BoundaryLinear hp)
    (e := (compactC1Submodule n p F).subtype) denseRange_compactC1Submodule
    ⟨p ^ (1 / p), norm_compactC1BoundaryLinear_le hp⟩ V).trans
      (compactC1Boundary_eq hp V hf hfc hU)

/-- Almost everywhere on the boundary, the trace of a compact ambient `C¹`
representative equals its value at normal coordinate zero. -/
theorem traceLp_coeFn_ae (hp : 1 ≤ p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F))
    {f : ℝ^(n + 1) → F} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hU : (U.val (baseIndex (n + 1) 1) : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] f) :
    (traceLp n p hp U : ℝ^n → F) =ᵐ[volume] fun y ↦ normalSlice f y 0 := by
  rw [traceLp_c1 hp U hf hfc hU]
  exact smoothBoundaryLp_coeFn_ae hf.continuous hfc

/-- The graph norm controls the boundary `Lp` norm with constant `p^(1/p)`.
In particular the trace at exponent one is a contraction. -/
theorem norm_traceLp_apply_le (hp : 1 ≤ p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    ‖traceLp n p hp U‖ ≤ p ^ (1 / p) * ‖U‖ :=
  LinearMap.norm_extendOfNorm_apply_le (f := compactC1BoundaryLinear hp)
    (e := (compactC1Submodule n p F).subtype) denseRange_compactC1Submodule _
    (norm_compactC1BoundaryLinear_le hp) U

/-- The operator norm of the finite-exponent half-space trace is at most `p^(1/p)`. -/
theorem norm_traceLp_le (hp : 1 ≤ p) :
    ‖traceLp (F := F) n p hp‖ ≤ p ^ (1 / p) :=
  (traceLp (F := F) n p hp).opNorm_le_bound (Real.rpow_nonneg (zero_le_one.trans hp) _)
    (fun U ↦ norm_traceLp_apply_le hp U)

end SobolevSpace.VectorValued.Trace.HalfSpace
