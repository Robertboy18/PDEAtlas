/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.ZeroTrace.HalfSpace
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Trace.HalfSpace

/-!
# The Banach-valued half-space trace kernel is the supported-smooth closure

For every finite real exponent at least one, the half-space trace vanishes exactly
on `W₀^{1,p}`. The converse uses the Sobolev zero extension constructed from the physical
trace-zero identity, then shifted mollification and compact cutoffs to approximate its
restriction by interior Banach-valued test functions.

The codomain is any real Banach space and the boundary dimension may be zero. For real-valued
fields this is the half-space statement (6) to which Evans reduces §5.5, Theorem 2; Evans proves
the converse with the estimate (9) and cutoffs in the normal variable instead of a zero
extension.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 2 and its proof, (6)-(9), pp. 273-275.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open GraphSpace

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- For a real Banach space `F` and real `p ≥ 1`, vanishing of the half-space trace of `U`
implies that `U` lies in the closure of the smooth `F`-valued functions compactly supported
inside the half-space. -/
theorem mem_Wkp0_of_traceLp_eq_zero (hp : 1 ≤ p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F))
    (hU : traceLp n p hp U = 0) :
    U ∈ (wkp0SubmoduleOn (k := 1) (p := ENNReal.ofReal p)
      (Ω := ⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩)
      (F := F)).toSubmodule := by
  let V : (traceLp (F := F) n p hp).ker := ⟨U, hU⟩
  have hzero : ∀ᵐ x ∂volume, x (Fin.last n) ≤ 0 →
      (zeroExtendCLM hp V).val (baseIndex (n + 1) 1) x = 0 := by
    filter_upwards [zeroExtendCLM_coordinate_apply_ae hp V (baseIndex (n + 1) 1)]
      with x hx hlast
    have hnot : x ∉ (ℝ^(n + 1)₊ : Set ℝ^(n + 1)) := not_lt_of_ge hlast
    exact hx.trans (Set.indicator_of_notMem hnot _)
  have hmem := VectorValued.HalfSpace.restrict_mem_Wkp0_of_zero_below
    ENNReal.ofReal_ne_top (zeroExtendCLM hp V) hzero
  simpa only [restrictCLM_zeroExtendCLM, V] using hmem

/-- For a real Banach space `F` and real `p ≥ 1`, the half-space trace of `U` vanishes if and
only if `U` lies in the supported-smooth closure `W₀^{1,p}`; this includes `p = 1` and a
zero-dimensional boundary. -/
theorem traceLp_eq_zero_iff_mem_Wkp0 (hp : 1 ≤ p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    traceLp n p hp U = 0 ↔
      U ∈ (wkp0SubmoduleOn (k := 1) (p := ENNReal.ofReal p)
        (Ω := ⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩)
        (F := F)).toSubmodule :=
  ⟨mem_Wkp0_of_traceLp_eq_zero hp U, traceLp_eq_zero_of_mem_Wkp0 hp U⟩

/-- Equality of the Banach-valued half-space trace kernel with `W₀^{1,p}`. -/
theorem ker_traceLp_eq_wkp0SubmoduleOn (hp : 1 ≤ p) :
    (traceLp (F := F) n p hp).ker =
      (wkp0SubmoduleOn (k := 1) (p := ENNReal.ofReal p)
        (Ω := ⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩)
        (F := F)).toSubmodule := by
  ext U
  exact traceLp_eq_zero_iff_mem_Wkp0 hp U

end SobolevSpace.VectorValued.Trace.HalfSpace
