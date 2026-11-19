/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Trace.C1
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Trace.C1.Localization
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Trace.C1.Reconstruction

/-!
# The physical C¹ trace kernel is the supported smooth closure

For a real Banach codomain and every finite exponent at least one, vanishing physical
surface trace characterizes `W₀^{1,p}` on a domain with a finite C¹ extension atlas.
Here `W₀^{1,p}` is the Sobolev closure of smooth functions compactly supported
inside the domain.

We localize a trace-zero field to half-spaces, use their trace-kernel theorem, and return
the resulting zero-boundary classes through the charts. The atlas partition recovers
the original field from those boundary pieces and a compactly supported interior piece.
Only C¹ regularity of the charts is needed: the returned approximants need not themselves
be smooth, since compact interior support already places them in the supported smooth
closure. The argument includes exponent one, one-dimensional domains, and the empty domain.

For real-valued fields on a bounded open set with `C¹` boundary this is Evans §5.5, Theorem 2,
and the reduction to half-spaces is step 2 of Evans's proof.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 2 and its proof, pp. 273-275.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.C1

open GraphSpace

private theorem atlas_partition {n k : ℕ} [Fact (0 < n)] {Ω : Opens ℝ^n}
    [A : Boundary.C1ExtensionAtlas n (Ω : Set ℝ^n)]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (U : W^{k,p}(Ω; F)) :
    compactSmoothMultiplierCLM A.interiorCutoff A.interiorCutoff.contDiff
        A.interiorCutoff.hasCompactSupport U +
      ∑ i, compactSmoothMultiplierCLM (A.boundaryCutoff i)
        (A.boundaryCutoff i).contDiff (A.boundaryCutoff i).hasCompactSupport U = U := by
  let I := compactSmoothMultiplierCLM A.interiorCutoff A.interiorCutoff.contDiff
    A.interiorCutoff.hasCompactSupport U
  let B := fun i : Fin A.N ↦ compactSmoothMultiplierCLM (A.boundaryCutoff i)
    (A.boundaryCutoff i).contDiff (A.boundaryCutoff i).hasCompactSupport U
  apply baseCoordinateCLM_injective
  change coordinateCLM (baseIndex n k) (I + ∑ i, B i) = coordinateCLM (baseIndex n k) U
  rw [map_add, map_sum]
  apply Lp.ext
  have hI := compactSmoothMultiplierCLM_base_ae A.interiorCutoff
    A.interiorCutoff.contDiff A.interiorCutoff.hasCompactSupport U
  have hB := ae_all_iff.mpr fun i : Fin A.N ↦ compactSmoothMultiplierCLM_base_ae
    (A.boundaryCutoff i) (A.boundaryCutoff i).contDiff
    (A.boundaryCutoff i).hasCompactSupport U
  filter_upwards [Lp.coeFn_add (coordinateCLM (baseIndex n k) I)
    (∑ i, coordinateCLM (baseIndex n k) (B i)),
    Lp.coeFn_finsetSum (Finset.univ : Finset (Fin A.N))
      (fun i ↦ coordinateCLM (baseIndex n k) (B i)),
    hI, hB, ae_restrict_mem Ω.isOpen.measurableSet] with x hadd hsum hi hb hxΩ
  rw [hadd, Pi.add_apply, hsum]
  simp only [Finset.sum_apply]
  change I.val (baseIndex n k) x +
    ∑ i, (B i).val (baseIndex n k) x = U.val (baseIndex n k) x
  rw [hi, Finset.sum_congr rfl (fun i _ ↦ hb i),
    ← Finset.sum_smul, ← add_smul]
  change (A.interiorCutoff.toFun x + ∑ i, (A.boundaryCutoff i).toFun x) •
    U.val (baseIndex n k) x = U.val (baseIndex n k) x
  rw [A.cutoff_sum_eq_one x hxΩ, one_smul]

variable {m : ℕ} {Ω : Opens ℝ^(m + 1)}
  [hΩ : Boundary.C1ExtensionAtlas (m + 1) (Ω : Set ℝ^(m + 1))]
  {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- On a domain with a finite C¹ extension atlas, for a real Banach space `F` and real `p ≥ 1`,
a field `U ∈ W^{1,p}(Ω; F)` with zero physical surface trace lies in `W₀^{1,p}(Ω; F)`, the
closure of the smooth `F`-valued functions compactly supported inside `Ω`. -/
theorem mem_Wkp0_of_traceLp_eq_zero (hp : 1 ≤ p) (U : W^{1,ENNReal.ofReal p}(Ω; F))
    (hU : traceLp p hp U = 0) :
    U ∈ (wkp0SubmoduleOn (k := 1) (p := ENNReal.ofReal p)
      (Ω := Ω) (F := F)).toSubmodule := by
  let Z := (wkp0SubmoduleOn (k := 1) (p := ENNReal.ofReal p)
    (Ω := Ω) (F := F)).toSubmodule
  rw [← atlas_partition U]
  apply Z.add_mem
  · exact compactSmoothMultiplierCLM_mem_Wkp0 ENNReal.ofReal_ne_top
      hΩ.interiorCutoff hΩ.interiorCutoff_support U
  · apply Z.sum_mem
    intro i _
    exact compactSmoothMultiplierCLM_boundary_mem_Wkp0_of_localizedFlatten
      ENNReal.ofReal_ne_top i U (localizedFlatten_mem_Wkp0_of_traceLp_eq_zero hp i U hU)

/-- Banach-valued form of Evans §5.5, Theorem 2: on a domain with a finite C¹ extension atlas
and for real `p ≥ 1`, the physical surface trace of `U ∈ W^{1,p}(Ω; F)` vanishes if and only if
`U` lies in the closure of the interior test functions. -/
theorem traceLp_eq_zero_iff_mem_Wkp0 (hp : 1 ≤ p) (U : W^{1,ENNReal.ofReal p}(Ω; F)) :
    traceLp p hp U = 0 ↔
      U ∈ (wkp0SubmoduleOn (k := 1) (p := ENNReal.ofReal p)
        (Ω := Ω) (F := F)).toSubmodule :=
  ⟨mem_Wkp0_of_traceLp_eq_zero hp U, traceLp_eq_zero_of_mem_Wkp0 hp U⟩

/-- The physical Banach-valued trace kernel equals the closed test-function
submodule, with no additional approximation hypothesis. -/
theorem ker_traceLp_eq_wkp0SubmoduleOn (hp : 1 ≤ p) :
    (traceLp (F := F) (Ω := Ω) p hp).ker =
      (wkp0SubmoduleOn (k := 1) (p := ENNReal.ofReal p)
        (Ω := Ω) (F := F)).toSubmodule := by
  ext U
  exact traceLp_eq_zero_iff_mem_Wkp0 hp U

end SobolevSpace.VectorValued.Trace.C1
