/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal

/-!
# Interior and exterior approach along the intrinsic normal

Differentiability of the actual chart height, together with its nonzero conormal, places
small inward normal displacements inside the domain and outward ones outside its closure.
No orthogonality of the flattening map or assumed normal-approach condition is needed.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Filter Set
open scoped Topology InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n} [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- Small positive normal displacements approach from the genuine interior and exterior. -/
theorem eventually_normal_approach_mem (x : frontier Ω) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (x : ℝ^n) - t • outwardUnitNormal (Ω := Ω) x ∈ Ω ∧
      (x : ℝ^n) + t • outwardUnitNormal (Ω := Ω) x ∈ (closure Ω)ᶜ := by
  obtain ⟨i, hi⟩ := exists_chart_source_of_mem_frontier (Ω := Ω) x.property
  let f : ℝ^n → ℝ := fun y ↦ (hΩ.chart i y) (PDE.Common.lastIndex (n := n))
  let L : ℝ^n →L[ℝ] ℝ :=
    (EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
      (fderiv ℝ (fun y ↦ hΩ.chart i y) x)
  let c := chartConormal (Ω := Ω) i x
  let ν := outwardUnitNormal (Ω := Ω) x
  have hc : 0 < ‖c‖ := norm_pos_iff.mpr (chartConormal_ne_zero i hi)
  have hν : ‖ν‖ = 1 := norm_outwardUnitNormal x
  have hf : HasFDerivAt f L x := hasFDerivAt_chartLastCoordinate i x
  have hzero : f x = 0 := (chartLastCoordinate_eq_zero_iff i hi).mpr x.property
  have hdual : (InnerProductSpace.toDual ℝ (ℝ^n)) c = L :=
    (InnerProductSpace.toDual ℝ (ℝ^n)).apply_symm_apply L
  have hLν : L ν = -‖c‖ := by
    change L (outwardUnitNormal (Ω := Ω) x) = -‖c‖
    rw [outwardUnitNormal_eq_chart x i hi, chartOutwardUnitNormal]
    change L (-‖c‖⁻¹ • c) = -‖c‖
    rw [map_smul, ← hdual]
    change -‖c‖⁻¹ * inner ℝ c c = -‖c‖
    rw [real_inner_self_eq_norm_sq]
    field_simp
  have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hin : Tendsto (fun t : ℝ ↦ (x : ℝ^n) - t • ν) (𝓝[>] 0) (𝓝 (x : ℝ^n)) := by
    simpa using (tendsto_const_nhds (x := (x : ℝ^n))).sub (hid.smul_const ν)
  have hout : Tendsto (fun t : ℝ ↦ (x : ℝ^n) + t • ν) (𝓝[>] 0) (𝓝 (x : ℝ^n)) := by
    simpa using (tendsto_const_nhds (x := (x : ℝ^n))).add (hid.smul_const ν)
  have hsource := (hΩ.chart i).open_source.mem_nhds hi
  have herr := hf.isLittleO.bound (half_pos hc)
  filter_upwards [self_mem_nhdsWithin, hin.eventually hsource, hout.eventually hsource,
    hin.eventually herr, hout.eventually herr] with t ht hins houts hine houte
  have hinDisp : (x : ℝ^n) - t • ν - x = -(t • ν) := by abel
  have houtDisp : (x : ℝ^n) + t • ν - x = t • ν := by abel
  have htpos : 0 < t := ht
  rw [hzero, sub_zero, hinDisp] at hine
  rw [hzero, sub_zero, houtDisp] at houte
  simp only [map_neg, map_smul, hLν, smul_eq_mul, norm_neg, norm_smul, hν,
    mul_one, Real.norm_eq_abs, abs_of_pos htpos] at hine houte
  have hpos : 0 < f ((x : ℝ^n) - t • ν) := by
    nlinarith [(abs_le.mp hine).1, mul_pos hc htpos]
  have hneg : f ((x : ℝ^n) + t • ν) < 0 := by
    nlinarith [(abs_le.mp houte).2, mul_pos hc htpos]
  refine ⟨(chartLastCoordinate_pos_iff i hins).mp hpos, ?_⟩
  rw [mem_compl_iff, closure_eq_self_union_frontier, mem_union]
  rintro (hy | hy)
  · have h := (chartLastCoordinate_pos_iff i houts).mpr hy
    change 0 < f ((x : ℝ^n) + t • ν) at h
    linarith
  · have h := (chartLastCoordinate_eq_zero_iff i houts).mpr hy
    change f ((x : ℝ^n) + t • ν) = 0 at h
    linarith

end SobolevSpace.Trace.C1
