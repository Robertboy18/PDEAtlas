/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.BallCorrection
public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.Closed
public import PDE.Fluid.NavierStokes.Stationary.DilationDrift
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.CompactSupport
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.ExtensionByZero
public import PDE.Spaces.Sobolev.Calculus.Pullback.Dilation.HigherOrder
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
public import PDE.Analysis.MeasureTheory.Lp.Composition.Dilation

/-!
# The truncated space of Remark 6 is the set of zero extensions

Hou, Wang and Yang define the truncated space `H¹_R` of their Remark 6 as the closure in
`H¹(ℝ³)` of the fields of `H₁` with compact support in the open ball `B_R(0)`, where `H₁` is the
divergence-free part of `H¹(ℝ³)³` in a symmetry class. The ball problems of this library are
posed instead on the divergence-free zero-boundary fields of the ball, which enter the whole
space through their zero extensions. This module shows that the two sets agree in every closed
subspace that the dilations `x ↦ f (s x)`, `s > 1`, map into itself, also under one more linear
constraint `ℓ f = 0`. Only balls centred at the origin are covered: the dilations need a
domain that is star-shaped about the origin.

## Main results

* `closure_isSupportedInBall_eq`: let `ρ > 0`, let `S` be a closed subspace that the dilations
  with `s > 1` map into itself and `ℓ` a continuous functional. The closure of the divergence-free
  fields of `S` with `ℓ = 0` and compact support in the open ball is the set of the zero
  extensions in `S` with `ℓ = 0` of the divergence-free zero-boundary fields of the ball.
* `closure_isSupportedInBall_evenSectorH1`, `closure_isSupportedInBall_oddSectorH1`: the same in
  the even and in the odd axisymmetric class, for every `ρ > 0` and every `ℓ`.
* `exists_zeroExtendH10_eq_of_tsupport_subset`: in every dimension and on every open set, an
  `H¹` function with compact support in the set is a zero extension.
  `exists_zeroExtendBall_eq_of_isSupportedInBall` is the form for fields on a ball.
* `divergence_eq_zero_of_divergenceCLM_zeroExtendBall`: a zero-boundary field of the ball is
  divergence-free if its zero extension is, the converse of `divergenceCLM_zeroExtendBall`.
* `isSupportedInBall_dilationH1_zeroExtendBall`: for `ρ > 0` and `s > 1` the dilation of a zero
  extension has compact support in the open ball.
* `divergenceCLM_dilationH1_eq_zero`, `dilationH1_mem_evenSectorH1`, `dilationH1_mem_oddSectorH1`:
  for `s ≠ 0` a dilation keeps a zero divergence and the two symmetry classes.
* `tendsto_dilationH1Half_one`: the dilations tend to the identity in `H¹` as `s → 1`.
* `mem_closure_inter_ker`: in a real normed space, if `ℓ f = 0` and `f` is in the closure of a
  subspace `A`, then `f` is in the closure of `A ∩ ker ℓ`.

## How it works

Let `f` in `H¹(ℝ³)` have compact support in the open ball. Its restriction to the ball is in
`H¹₀`, by mollification (`restrict_mem_H10_of_tsupport_subset`). The zero extension of the
restriction has the values of `f` almost everywhere, and a Sobolev function is determined by its
values, so `f` is a zero extension. The zero extension keeps the norm, and its divergence is the
zero extension of the divergence. So the zero extensions of the divergence-free fields of the
ball form a closed set (`isClosed_range_zeroExtendBall`), and this set contains the closure of
Remark 6.

For the other inclusion let `f` be the zero extension of a divergence-free field of the ball.
For `s > 1` the dilation `x ↦ f (s x)` vanishes outside the closed ball of radius `ρ / s`, a
compact subset of the open ball. It is divergence-free, it stays in the symmetry class because
the rotations and the reflection are linear, and it converges to `f` in `H¹` as `s → 1`. A linear
constraint `ℓ f = 0` is restored by subtracting a multiple of one fixed field of the subspace on
which `ℓ` does not vanish (`mem_closure_inter_ker`).

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Remark 6.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace NavierStokes.Symmetry
open scoped ENNReal Topology Sobolev SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))
local notation "Vb" ρ => IncompressibleFlow.SolenoidalSpace
  (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))

variable {ρ : ℝ}

/-! ### A compactly supported function is a zero extension -/

/-- **A function that vanishes outside `Ω` is the zero extension of its restriction.** Let
`w ∈ H¹(ℝⁿ)` vanish almost everywhere outside a measurable set `Ω`, and let `v ∈ H¹₀(Ω)` be the
restriction of `w` to `Ω`. Then the zero extension of `v` is `w`. -/
theorem zeroExtendH10_eq_of_restrictCLM_eq {n : ℕ} {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    {w : H¹(ℝ^n)} {v : H¹₀(Ω)}
    (hv : (v : H¹(Ω)) = restrictCLM (k := 1) (p := 2) hΩ (subset_univ Ω) w)
    (hw : ∀ᵐ x ∂(volume : Measure (ℝ^n)), x ∉ Ω →
      (wkpBaseCoordinateCLM w : ℝ^n → ℝ) x = 0) :
    ZeroTrace.zeroExtendH10 hΩ v = w := by
  have hext := ZeroTrace.zeroExtendH10_coordinate_apply_ae hΩ v (baseIndex n 1)
  have hres : ∀ᵐ x ∂(volume : Measure (ℝ^n)), x ∈ Ω →
      (baseCoordCLM v : ℝ^n → ℝ) x = (wkpBaseCoordinateCLM w : ℝ^n → ℝ) x := by
    have h := restrictCLM_apply_ae (k := 1) (p := 2) hΩ (subset_univ Ω) w (baseIndex n 1)
    rw [← hv] at h
    exact (ae_restrict_iff' hΩ).mp h
  apply wkpBaseCoordinateCLM_injective (n := n) (p := 2) isOpen_univ
  apply Lp.ext
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [hext, hres, hw] with x hx hr h0
  by_cases hxΩ : x ∈ Ω
  · exact (hx.trans (Set.indicator_of_mem hxΩ _)).trans (hr hxΩ)
  · exact (hx.trans (Set.indicator_of_notMem hxΩ _)).trans (h0 hxΩ).symm

/-- **A compactly supported `H¹` function is a zero extension.** Let `w ∈ H¹(ℝⁿ)` agree almost
everywhere with a function `g` whose topological support is compact and lies in an open set
`Ω`. Then `w` is the zero extension of a function of `H¹₀(Ω)`. -/
theorem exists_zeroExtendH10_eq_of_tsupport_subset {n : ℕ} {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (w : H¹(ℝ^n)) {g : ℝ^n → ℝ} (hg : (wkpBaseCoordinateCLM w : ℝ^n → ℝ) =ᵐ[volume] g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ω) :
    ∃ v : H¹₀(Ω), ZeroTrace.zeroExtendH10 hΩ.measurableSet v = w := by
  have hmem := restrict_mem_H10_of_tsupport_subset hΩ w g hg hgc hgs
  refine ⟨⟨restrictCLM (k := 1) (p := 2) hΩ.measurableSet (subset_univ Ω) w, hmem⟩,
    zeroExtendH10_eq_of_restrictCLM_eq hΩ.measurableSet rfl ?_⟩
  filter_upwards [hg] with x hx hxΩ
  rw [hx]
  exact image_eq_zero_of_notMem_tsupport fun h ↦ hxΩ (hgs h)

/-! ### Fields with compact support in the open ball -/

/-- A field `f` of `H¹(ℝ³)³` has compact support in the open ball `B(0, ρ)`: its representative
agrees almost everywhere with a function whose topological support is compact and lies in the
ball. -/
def IsSupportedInBall (ρ : ℝ) (f : H) : Prop :=
  ∃ g : ℝ^3 → ℝ^3, Stationary.representative f =ᵐ[volume] g ∧ HasCompactSupport g ∧
    tsupport g ⊆ Metric.ball (0 : ℝ^3) ρ

/-- The zero field has compact support in the open ball `B(0, ρ)`, for every real `ρ`. -/
theorem isSupportedInBall_zero (ρ : ℝ) : IsSupportedInBall ρ (0 : H) :=
  ⟨0, Stationary.representative_zero_ae, HasCompactSupport.zero,
    by simp only [tsupport_zero, Set.empty_subset]⟩

/-- The sum of two fields with compact support in the open ball `B(0, ρ)` has compact support
in this ball. -/
theorem IsSupportedInBall.add {f₁ f₂ : H} (h₁ : IsSupportedInBall ρ f₁)
    (h₂ : IsSupportedInBall ρ f₂) : IsSupportedInBall ρ (f₁ + f₂) := by
  obtain ⟨g₁, hg₁, hc₁, hs₁⟩ := h₁
  obtain ⟨g₂, hg₂, hc₂, hs₂⟩ := h₂
  exact ⟨g₁ + g₂, (Stationary.representative_add_ae f₁ f₂).trans (hg₁.add hg₂), hc₁.add hc₂,
    (tsupport_add g₁ g₂).trans (Set.union_subset hs₁ hs₂)⟩

/-- A multiple of a field with compact support in the open ball `B(0, ρ)` has compact support
in this ball. -/
theorem IsSupportedInBall.smul {f : H} (c : ℝ) (h : IsSupportedInBall ρ f) :
    IsSupportedInBall ρ (c • f) := by
  obtain ⟨g, hg, hgc, hgs⟩ := h
  refine ⟨fun x ↦ c • g x, ?_, hgc.comp_left (g := fun v : ℝ^3 ↦ c • v) (smul_zero c),
    (tsupport_comp_subset (g := fun v : ℝ^3 ↦ c • v) (smul_zero c) g).trans hgs⟩
  filter_upwards [Stationary.representative_smul_ae c f, hg] with x hx hgx
  rw [hx, Pi.smul_apply, hgx]

/-- **A compactly supported field is a zero extension.** A field of `H¹(ℝ³)³` with compact
support in the open ball `B(0, ρ)` is the zero extension of a zero-boundary field of the
ball. -/
theorem exists_zeroExtendBall_eq_of_isSupportedInBall {f : H} (hf : IsSupportedInBall ρ f) :
    ∃ u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3), zeroExtendBall ρ u = f := by
  obtain ⟨g, hg, hgc, hgs⟩ := hf
  have hcomp (i : Fin 3) : ∃ v : H¹₀(Metric.ball (0 : ℝ^3) ρ),
      ZeroTrace.zeroExtendH10 measurableSet_ball v = f i := by
    refine exists_zeroExtendH10_eq_of_tsupport_subset Metric.isOpen_ball (f i)
      (g := fun x ↦ g x i) ?_ (Stationary.hasCompactSupport_component hgc i)
      ((tsupport_comp_subset (g := fun v : ℝ^3 ↦ v i) rfl g).trans hgs)
    filter_upwards [hg] with x hx
    rw [← hx, Stationary.representative_apply, Stationary.massCLM_apply]
  choose v hv using hcomp
  exact ⟨WithLp.toLp 2 v, PiLp.ext fun i ↦ hv i⟩

/-- **Converse of `divergenceCLM_zeroExtendBall`.** If the zero extension of a zero-boundary
field `u` of the ball `B(0, ρ)` has zero weak divergence on `ℝ³`, then `u` has zero weak
divergence on the ball. -/
theorem divergence_eq_zero_of_divergenceCLM_zeroExtendBall
    {u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)}
    (h : Stationary.divergenceCLM (zeroExtendBall ρ u) = 0) :
    ZeroBoundaryVectorSpace.divergence u = 0 := by
  have hsum : Stationary.divergenceCLM (zeroExtendBall ρ u) =
      Extension.Lp.zeroExtendLp measurableSet_ball (∑ j, derivCoordCLM j (u j)) := by
    rw [Stationary.divergenceCLM_apply, map_sum]
    rfl
  have hnorm := Extension.Lp.norm_zeroExtendLp measurableSet_ball
    (∑ j, derivCoordCLM j (u j))
  rw [← hsum, h, norm_zero] at hnorm
  exact (ZeroBoundaryVectorSpace.divergence_apply u).trans (norm_eq_zero.mp hnorm.symm)

/-! ### Dilations -/

/-- The representative of the dilated field `dilationH1 3 s hs f` is `x ↦ f (s x)` almost
everywhere, where `f` stands for its representative. -/
theorem representative_dilationH1_ae {s : ℝ} (hs : s ≠ 0) (f : H) :
    Stationary.representative (Stationary.dilationH1 3 s hs f) =ᵐ[volume]
      fun x ↦ Stationary.representative f (s • x) := by
  have h (i : Fin 3) :
      (Stationary.massCLM (Stationary.dilationH1 3 s hs f) i : ℝ^3 → ℝ) =ᵐ[volume]
        fun x ↦ (Stationary.massCLM f i : ℝ^3 → ℝ) (s • x) := by
    have hi := dilationWkpCLM_base_ae (n := 3) (k := 1) (p := 2) (by norm_num) s hs (f i)
    simp only [domainMeasure, Measure.restrict_univ] at hi
    exact hi
  filter_upwards [ae_all_iff.mpr h] with x hx
  ext i
  exact hx i

/-- **The dilations of a zero extension have compact support in the open ball.** Let `ρ > 0`
and `s > 1`, and let `W` be the zero extension of a zero-boundary field of the ball `B(0, ρ)`.
The dilation `x ↦ W (s x)` vanishes outside the closed ball of radius `ρ / s`, so it has
compact support in the open ball `B(0, ρ)`. -/
theorem isSupportedInBall_dilationH1_zeroExtendBall {s : ℝ} (hρ : 0 < ρ) (hs : 1 < s)
    (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) :
    IsSupportedInBall ρ
      (Stationary.dilationH1 3 s (zero_lt_one.trans hs).ne' (zeroExtendBall ρ u)) := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hzero : ∀ x : ℝ^3, x ∉ Metric.closedBall (0 : ℝ^3) (ρ / s) →
      ballField ρ u (s • x) = 0 := by
    intro x hx
    have hsx : s • x ∉ Metric.ball (0 : ℝ^3) ρ := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      intro hmem
      apply hx
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (le_div_iff₀' hs0).mpr hmem.le
    rw [ballField, Set.indicator_of_notMem hsx]
  refine ⟨fun x ↦ ballField ρ u (s • x), ?_,
    HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^3) (ρ / s)) hzero,
    (closure_minimal (Function.support_subset_iff'.mpr hzero) Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball (div_lt_self hρ hs))⟩
  filter_upwards [representative_dilationH1_ae (zero_lt_one.trans hs).ne' (zeroExtendBall ρ u),
    (Measure.quasiMeasurePreserving_smul (volume : Measure (ℝ^3)) hs0.ne').ae_eq_comp
      (representative_zeroExtendBall ρ u)] with x hx1 hx2
  exact hx1.trans hx2

/-- **Dilation keeps a zero divergence.** If `f ∈ H¹(ℝ³)³` has zero weak divergence, then so
has the dilation `x ↦ f (s x)`, for every `s ≠ 0`: the divergence of the dilation is `s` times
the dilation of the divergence. -/
theorem divergenceCLM_dilationH1_eq_zero {s : ℝ} (hs : s ≠ 0) {f : H}
    (hf : Stationary.divergenceCLM f = 0) :
    Stationary.divergenceCLM (Stationary.dilationH1 3 s hs f) = 0 := by
  have h : Stationary.divergenceCLM (Stationary.dilationH1 3 s hs f) =
      s • Lp.compSMul (domainMeasure 3 univ) 2 s hs (Stationary.divergenceCLM f) := by
    simp only [Stationary.divergenceCLM_apply, map_sum, Finset.smul_sum,
      Stationary.dilationH1_apply, dilationWkpCLM_coordinate, singleDerivIndex_toList,
      List.length_singleton, pow_one]
  rw [h, hf, map_zero, smul_zero]

/-- Even axisymmetry is kept by the dilations `u ↦ u (s ·)`, `s ≠ 0`. No continuity is asked:
the two identities are transported along `x ↦ s x`, which maps null sets to null sets, and the
rotations and the reflection commute with `x ↦ s x`. -/
theorem IsEvenAxisymmetric.comp_smul_of_ne_zero {u : ℝ^3 → ℝ^3} (hu : IsEvenAxisymmetric u)
    {s : ℝ} (hs : s ≠ 0) : IsEvenAxisymmetric (fun x ↦ u (s • x)) := by
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure (ℝ^3)) hs
  refine ⟨fun θ ↦ ?_, ?_⟩
  · filter_upwards [hq.ae_eq_comp (hu.1 θ)] with x hx
    simpa only [Function.comp_apply, map_smul] using hx
  · filter_upwards [hq.ae_eq_comp hu.2] with x hx
    simpa only [Function.comp_apply, map_smul] using hx

/-- Odd axisymmetry is kept by the dilations `u ↦ u (s ·)`, `s ≠ 0`. No continuity is asked:
the two identities are transported along `x ↦ s x`, which maps null sets to null sets, and the
rotations and the reflection commute with `x ↦ s x`. -/
theorem IsOddAxisymmetric.comp_smul_of_ne_zero {u : ℝ^3 → ℝ^3} (hu : IsOddAxisymmetric u)
    {s : ℝ} (hs : s ≠ 0) : IsOddAxisymmetric (fun x ↦ u (s • x)) := by
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure (ℝ^3)) hs
  refine ⟨fun θ ↦ ?_, ?_⟩
  · filter_upwards [hq.ae_eq_comp (hu.1 θ)] with x hx
    simpa only [Function.comp_apply, map_smul] using hx
  · filter_upwards [hq.ae_eq_comp hu.2] with x hx
    simpa only [Function.comp_apply, map_smul, Pi.neg_apply] using hx

/-- The dilation `x ↦ f (s x)`, `s ≠ 0`, of a field of the even whole-space sector is in the
even whole-space sector. -/
theorem dilationH1_mem_evenSectorH1 {s : ℝ} (hs : s ≠ 0) {f : H} (hf : f ∈ evenSectorH1) :
    Stationary.dilationH1 3 s hs f ∈ evenSectorH1 :=
  mem_evenSectorH1_iff.mpr (((mem_evenSectorH1_iff.mp hf).comp_smul_of_ne_zero hs).congr_ae
    (representative_dilationH1_ae hs f).symm)

/-- The dilation `x ↦ f (s x)`, `s ≠ 0`, of a field of the odd whole-space sector is in the
odd whole-space sector. -/
theorem dilationH1_mem_oddSectorH1 {s : ℝ} (hs : s ≠ 0) {f : H} (hf : f ∈ oddSectorH1) :
    Stationary.dilationH1 3 s hs f ∈ oddSectorH1 :=
  mem_oddSectorH1_iff.mpr (((mem_oddSectorH1_iff.mp hf).comp_smul_of_ne_zero hs).congr_ae
    (representative_dilationH1_ae hs f).symm)

/-- The dilation by the factor `1` is the identity on `H¹(ℝ³)³`. -/
theorem dilationH1_one (f : H) : Stationary.dilationH1 3 1 one_ne_zero f = f := by
  ext i : 1
  exact dilationWkpCLM_one (by norm_num) _

/-- **The dilations converge to the identity.** For every `f ∈ H¹(ℝ³)³` the dilations
`dilationH1Half 3 s f`, which are `x ↦ f (s x)` for `s ≥ 1 / 2`, converge to `f` in `H¹` as
`s → 1`. -/
theorem tendsto_dilationH1Half_one (f : H) :
    Filter.Tendsto (fun s : ℝ ↦ Stationary.dilationH1Half 3 s f) (𝓝 1) (𝓝 f) := by
  have h1 : Stationary.dilationH1Half 3 1 f = f := by
    rw [Stationary.dilationH1Half_eq (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact dilationH1_one f
  exact (Stationary.continuous_dilationH1Half_apply f).tendsto' 1 f h1

/-! ### The zero extensions form a closed set -/

/-- The zero extension of a zero-boundary field of the ball `B(0, ρ)` has the `H¹` norm of the
field. -/
theorem norm_zeroExtendBall (ρ : ℝ) (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) :
    ‖zeroExtendBall ρ u‖ = ‖u‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun i _ ↦
    congrArg (fun t : ℝ ↦ t ^ 2) (ZeroTrace.norm_zeroExtendH10 measurableSet_ball (u i))

/-- The zero extensions of the divergence-free zero-boundary fields of the ball `B(0, ρ)` form
a closed subset of `H¹(ℝ³)³`: the zero extension keeps the norm, and the divergence-free
fields of the ball form a complete space. -/
theorem isClosed_range_zeroExtendBall (ρ : ℝ) :
    IsClosed (Set.range fun u : Vb ρ ↦
      zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))) := by
  have : CompleteSpace (Vb ρ) := ContinuousLinearMap.completeSpace_ker
    (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))
  have hiso : Isometry fun u : Vb ρ ↦
      zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) :=
    AddMonoidHomClass.isometry_of_norm ((zeroExtendBall ρ).comp
      (ZeroBoundaryVectorSpace.divergence (n := 3)
        (Ω := Metric.ball (0 : ℝ^3) ρ)).ker.subtypeL) fun u ↦ norm_zeroExtendBall ρ u
  exact hiso.isClosedEmbedding.isClosed_range

/-- For a closed subspace `S` of `H¹(ℝ³)³` and a continuous linear functional `ℓ`, the fields
of `S` with `ℓ = 0` that are zero extensions of divergence-free zero-boundary fields of the
ball `B(0, ρ)` form a closed set. -/
theorem isClosed_setOf_exists_zeroExtendBall (ρ : ℝ) {S : Submodule ℝ H}
    (hS : IsClosed (S : Set H)) (ℓ : StrongDual ℝ H) :
    IsClosed {f : H | f ∈ S ∧ ℓ f = 0 ∧
      ∃ u : Vb ρ, zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) = f} := by
  have h1 : IsClosed {f : H | f ∈ S} := hS
  have h2 : IsClosed {f : H | ℓ f = 0} := isClosed_eq ℓ.continuous continuous_const
  have h3 : IsClosed {f : H | ∃ u : Vb ρ,
      zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) = f} :=
    isClosed_range_zeroExtendBall ρ
  exact h1.and (h2.and h3)

/-! ### Approximation -/

/-- **Approximation under a linear constraint.** Let `A` be a subspace of a real normed space
and `ℓ` a continuous linear functional. If `f` is in the closure of `A` and `ℓ f = 0`, then
`f` is in the closure of the set of the `g ∈ A` with `ℓ g = 0`. -/
theorem mem_closure_inter_ker {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Submodule ℝ E) (ℓ : StrongDual ℝ E) {f : E} (hf : f ∈ closure (A : Set E))
    (hℓ : ℓ f = 0) : f ∈ closure {g : E | g ∈ A ∧ ℓ g = 0} := by
  by_cases h : ∃ ψ ∈ A, ℓ ψ ≠ 0
  · obtain ⟨ψ, hψA, hψ⟩ := h
    have hcont : Continuous fun g : E ↦ g - (ℓ g / ℓ ψ) • ψ :=
      continuous_id.sub ((ℓ.continuous.div_const (ℓ ψ)).smul continuous_const)
    have hmaps : Set.MapsTo (fun g : E ↦ g - (ℓ g / ℓ ψ) • ψ) (A : Set E)
        {g : E | g ∈ A ∧ ℓ g = 0} := by
      intro g hg
      refine ⟨A.sub_mem hg (A.smul_mem _ hψA), ?_⟩
      change ℓ (g - (ℓ g / ℓ ψ) • ψ) = 0
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ, sub_self]
    have hfix : f - (ℓ f / ℓ ψ) • ψ = f := by
      rw [hℓ, zero_div, zero_smul, sub_zero]
    have h := map_mem_closure hcont hf hmaps
    change f - (ℓ f / ℓ ψ) • ψ ∈ _ at h
    rwa [hfix] at h
  · have hsub : (A : Set E) ⊆ {g : E | g ∈ A ∧ ℓ g = 0} := fun g hg ↦
      ⟨hg, Classical.byContradiction fun hne ↦ h ⟨g, hg, hne⟩⟩
    exact closure_mono hsub hf

/-- The divergence-free fields of a subspace `S` of `H¹(ℝ³)³` with compact support in the open
ball `B(0, ρ)`, as a subspace. -/
def supportedSolenoidal (ρ : ℝ) (S : Submodule ℝ H) : Submodule ℝ H where
  carrier := {f | f ∈ S ∧ Stationary.divergenceCLM f = 0 ∧ IsSupportedInBall ρ f}
  zero_mem' := ⟨S.zero_mem, map_zero _, isSupportedInBall_zero ρ⟩
  add_mem' := by
    rintro f g ⟨hf, hfd, hfs⟩ ⟨hg, hgd, hgs⟩
    exact ⟨S.add_mem hf hg, by rw [map_add, hfd, hgd, add_zero], hfs.add hgs⟩
  smul_mem' := by
    rintro c f ⟨hf, hfd, hfs⟩
    exact ⟨S.smul_mem c hf, by rw [map_smul, hfd, smul_zero], hfs.smul c⟩

/-- A field is in `supportedSolenoidal ρ S` exactly when it is in `S`, has zero weak divergence
and has compact support in the open ball `B(0, ρ)`. -/
theorem mem_supportedSolenoidal_iff {S : Submodule ℝ H} {f : H} :
    f ∈ supportedSolenoidal ρ S ↔
      f ∈ S ∧ Stationary.divergenceCLM f = 0 ∧ IsSupportedInBall ρ f :=
  Iff.rfl

/-- **Approximation by dilations.** Let the dilations `x ↦ f (s x)`, `s > 1`, map the subspace
`S` into itself. A divergence-free field `f` of `S` whose dilations with `s > 1` have compact
support in the open ball `B(0, ρ)` is in the closure of `supportedSolenoidal ρ S`. -/
theorem mem_closure_supportedSolenoidal (S : Submodule ℝ H)
    (hdil : ∀ (s : ℝ) (hs : 1 < s) (f : H), f ∈ S →
      Stationary.dilationH1 3 s (zero_lt_one.trans hs).ne' f ∈ S)
    {f : H} (hfS : f ∈ S) (hfdiv : Stationary.divergenceCLM f = 0)
    (hfsupp : ∀ (s : ℝ) (hs : 1 < s),
      IsSupportedInBall ρ (Stationary.dilationH1 3 s (zero_lt_one.trans hs).ne' f)) :
    f ∈ closure (supportedSolenoidal ρ S : Set H) := by
  have htend : Filter.Tendsto (fun s : ℝ ↦ Stationary.dilationH1Half 3 s f) (𝓝[>] 1) (𝓝 f) :=
    (tendsto_dilationH1Half_one f).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (1 : ℝ) < s := Set.mem_Ioi.mp hs
  rw [Stationary.dilationH1Half_eq (by linarith : (1 / 2 : ℝ) ≤ s)]
  exact mem_supportedSolenoidal_iff.mpr
    ⟨hdil s hs1 f hfS, divergenceCLM_dilationH1_eq_zero _ hfdiv, hfsupp s hs1⟩

/-! ### The closure of Remark 6 -/

/-- **The truncated space of Remark 6** (Hou, Wang and Yang, Remark 6). Let `ρ > 0`, let `S` be
a closed subspace of `H¹(ℝ³)³` that the dilations `x ↦ f (s x)`, `s > 1`, map into itself, and
let `ℓ` be a continuous linear functional. The closure in `H¹(ℝ³)³` of the
divergence-free fields of `S` with `ℓ = 0` and compact support in the open ball `B(0, ρ)` is
the set of the fields of `S` with `ℓ = 0` that are zero extensions of divergence-free
zero-boundary fields of the ball. -/
theorem closure_isSupportedInBall_eq (hρ : 0 < ρ) (S : Submodule ℝ H)
    (hS : IsClosed (S : Set H))
    (hdil : ∀ (s : ℝ) (hs : 1 < s) (f : H), f ∈ S →
      Stationary.dilationH1 3 s (zero_lt_one.trans hs).ne' f ∈ S)
    (ℓ : StrongDual ℝ H) :
    closure {f : H | f ∈ S ∧ ℓ f = 0 ∧ Stationary.divergenceCLM f = 0 ∧
        IsSupportedInBall ρ f} =
      {f : H | f ∈ S ∧ ℓ f = 0 ∧
        ∃ u : Vb ρ, zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) = f} := by
  refine Set.Subset.antisymm
    (closure_minimal ?_ (isClosed_setOf_exists_zeroExtendBall ρ hS ℓ)) ?_
  · rintro f ⟨hfS, hfℓ, hfdiv, hfsupp⟩
    obtain ⟨u, rfl⟩ := exists_zeroExtendBall_eq_of_isSupportedInBall hfsupp
    exact ⟨hfS, hfℓ, ⟨u, divergence_eq_zero_of_divergenceCLM_zeroExtendBall hfdiv⟩, rfl⟩
  · rintro f ⟨hfS, hfℓ, u, rfl⟩
    have hcl := mem_closure_supportedSolenoidal S hdil hfS
      (divergenceCLM_zeroExtendBall u.2)
      fun _ hs ↦ isSupportedInBall_dilationH1_zeroExtendBall hρ hs u
    refine closure_mono ?_ (mem_closure_inter_ker (supportedSolenoidal ρ S) ℓ hcl hfℓ)
    rintro g ⟨hgA, hgℓ⟩
    obtain ⟨hgS, hgdiv, hgsupp⟩ := mem_supportedSolenoidal_iff.mp hgA
    exact ⟨hgS, hgℓ, hgdiv, hgsupp⟩

/-- **The truncated space of Remark 6 in the even class.** For `ρ > 0` and a continuous linear
functional `ℓ`, the closure of the divergence-free even axisymmetric fields of `H¹(ℝ³)³` with
`ℓ = 0` and compact support in the open ball `B(0, ρ)` is the set of the even axisymmetric
fields with `ℓ = 0` that are zero extensions of divergence-free zero-boundary fields of the
ball. -/
theorem closure_isSupportedInBall_evenSectorH1 (hρ : 0 < ρ) (ℓ : StrongDual ℝ H) :
    closure {f : H | f ∈ evenSectorH1 ∧ ℓ f = 0 ∧ Stationary.divergenceCLM f = 0 ∧
        IsSupportedInBall ρ f} =
      {f : H | f ∈ evenSectorH1 ∧ ℓ f = 0 ∧
        ∃ u : Vb ρ, zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) = f} :=
  closure_isSupportedInBall_eq hρ evenSectorH1 evenSectorH1_isClosed
    (fun _ hs _ hf ↦ dilationH1_mem_evenSectorH1 (zero_lt_one.trans hs).ne' hf) ℓ

/-- **The truncated space of Remark 6 in the odd class.** For `ρ > 0` and a continuous linear
functional `ℓ`, the closure of the divergence-free odd axisymmetric fields of `H¹(ℝ³)³` with
`ℓ = 0` and compact support in the open ball `B(0, ρ)` is the set of the odd axisymmetric
fields with `ℓ = 0` that are zero extensions of divergence-free zero-boundary fields of the
ball. -/
theorem closure_isSupportedInBall_oddSectorH1 (hρ : 0 < ρ) (ℓ : StrongDual ℝ H) :
    closure {f : H | f ∈ oddSectorH1 ∧ ℓ f = 0 ∧ Stationary.divergenceCLM f = 0 ∧
        IsSupportedInBall ρ f} =
      {f : H | f ∈ oddSectorH1 ∧ ℓ f = 0 ∧
        ∃ u : Vb ρ, zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) = f} :=
  closure_isSupportedInBall_eq hρ oddSectorH1 oddSectorH1_isClosed
    (fun _ hs _ hf ↦ dilationH1_mem_oddSectorH1 (zero_lt_one.trans hs).ne' hf) ℓ

end NavierStokes.Nonuniqueness
