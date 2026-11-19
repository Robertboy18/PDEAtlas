/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Flattening.Assembly
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.CompactSupport
import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.ClassicalRepresentative
import PDE.Spaces.Sobolev.Inequalities.Hardy.ChartLocal
public import PDE.Spaces.Sobolev.Variational.Spaces.H1

/-!
# Zero trace under boundary-chart flattening

The bounded chart map `Extension.C1.BoundaryPiece.flattenCLM` transports arbitrary `H¹` fields to
the upper half-space. We show that it also transports `H¹₀` fields to `H¹₀` (`flattenCLM_mem_H10`).
This is Evans's (60), `u' = 0` on `∂U' ∩ {yₙ = 0}` in the trace sense, in step 7 of the proof of
§6.3.2, Theorem 4, which Evans calls straightforward to check.

The proof uses the defining closure of `H¹₀`, rather than differentiating a Sobolev representative.
On the dense `C_c^∞(Ω)` core, the flattened field has a compactly supported `C¹` representative
strictly inside the upper half-space. Compact-support mollification puts that representative in
`H¹₀` on the upper half-space in `ℝ^n`. Continuity of `flattenCLM` and closedness of `H¹₀` then give
the result for every `H¹₀(Ω)` input.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 7 of the proof of Theorem 4, (58)-(60), p. 338.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open scoped Topology

variable {n : ℕ}

/-- A compactly supported global `C¹` representative whose topological
support lies in an open set represents an `H¹₀` element after restriction.

This finite-regularity version is useful after a `C¹` change of variables:
composition with a `C¹` chart need not preserve `C∞`, but it does preserve
the regularity needed for a global `H¹` field. -/
theorem mem_H10_of_contDiff_one_compactSupport
    {D : Set (ℝ^n)} (hD : IsOpen D)
    (U : H¹(D)) (f : ℝ^n → ℝ)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ D)
    (hUbase :
      (((((U : WkpAmbientOn n 1 2 D) (baseIndex n 1) :
          DerivLp n 2 D) : ℝ^n → ℝ)) =ᵐ[domainMeasure n D] f)) :
    U ∈ (h10SubmoduleOn (n := n) (Ω := D)).toSubmodule := by
  classical
  have hmem : ∀ a : DerivIndex n 1,
      MemLp (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x)
        2 (domainMeasure n (Set.univ : Set (ℝ^n))) := by
    intro a
    have hlen : a.toList.length ≤ 1 := a.toList_length_le
    have hreg : ContDiff ℝ (a.toList.length : ℕ∞) f :=
      hf.of_le (by exact_mod_cast hlen)
    have hcont : Continuous
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x) :=
      (PDE.contDiff_iteratedPartialDeriv_of_le
        (n := n) hreg a.toList le_rfl).continuous
    exact hcont.memLp_of_hasCompactSupport
      (SobolevSpace.hasCompactSupport_iteratedPartialDeriv
        (n := n) (f := f) hfc a.toList)
  let G : W^{1,2}((Set.univ : Set (ℝ^n))) :=
    mkWkpSpaceOnOfContDiffMemLpFinite
      (n := n) (k := 1) (p := (2 : ℝ≥0∞))
      (Ω := (Set.univ : Set (ℝ^n))) (f := f) hf hmem
  have hGbase :
      (((((G : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
          DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[volume] f) := by
    simpa [G, baseIndex_toList, iteratedPartialDeriv, domainMeasure] using
      (mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
        (n := n) (k := 1) (p := (2 : ℝ≥0∞))
        (Ω := (Set.univ : Set (ℝ^n))) (f := f) hf hmem
        (baseIndex n 1))
  let R : H¹(D) :=
    restrictCLM (n := n) (k := 1) (p := (2 : ℝ≥0∞))
      hD.measurableSet (subset_univ D) G
  have hRmem :
      R ∈ (h10SubmoduleOn (n := n) (Ω := D)).toSubmodule := by
    exact restrict_mem_H10_of_tsupport_subset hD G f hGbase hfc hfs
  have hUR : U = R := by
    apply WkpSpaceOn.ext_of_base_ae hD
    have hrestrict := restrictCLM_apply_ae
      (n := n) (k := 1) (p := (2 : ℝ≥0∞))
      hD.measurableSet (subset_univ D) G (baseIndex n 1)
    have hGlocal := MeasureTheory.ae_restrict_of_ae (s := D) hGbase
    have hGlocal' :
        (((((G : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
            DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[domainMeasure n D] f) := by
      rw [domainMeasure]
      exact hGlocal
    have hRbase :
        (((((R : WkpAmbientOn n 1 2 D) (baseIndex n 1) :
            DerivLp n 2 D) : ℝ^n → ℝ)) =ᵐ[domainMeasure n D] f) := by
      exact hrestrict.trans hGlocal'
    exact hUbase.trans hRbase.symm
  simpa [hUR] using hRmem

end SobolevSpace.GraphSpace

namespace SobolevSpace.Extension.C1.BoundaryPiece

open MeasureTheory Set Function ENNReal
open scoped Topology
open SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

private theorem flattenCLM_core_mem_H10
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (φ : TestFunctionOn n Ω) :
    flattenCLM (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) i
        (testFunctionToH1 (n := n) (Ω := Ω) φ) ∈
      (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).toSubmodule := by
  let U := testFunctionToH1
    (n := n) (Ω := Ω) φ
  let F := flattenCLM
    (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) i U
  let q := SobolevSpace.Hardy.flattenedBoundaryPiece (hΩ := hΩ) i φ
  have hUbase :
      (((((U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) :
          DerivLp n 2 Ω) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω] φ.1.toFun) := by
    simpa [U, testFunctionToH1, baseIndex_toList, iteratedPartialDeriv] using
      (mkWkpSpaceOnOfContDiff_apply_ae
        (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Ω)
        (f := φ.1.toFun) φ.1.contDiff
        φ.1.hasCompactSupport (baseIndex n 1))
  have hFbase :
      (((((F : WkpAmbientOn n 1 2 (HalfSpace.upper n)) (baseIndex n 1) :
          DerivLp n 2 (HalfSpace.upper n)) : ℝ^n → ℝ)) =ᵐ[
        domainMeasure n (HalfSpace.upper n)] q) := by
    change
      (((((flattenCLM (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) i U :
          W^{1,2}(HalfSpace.upper n)) :
            WkpAmbientOn n 1 2 (HalfSpace.upper n)) (baseIndex n 1) :
              DerivLp n 2 (HalfSpace.upper n)) : ℝ^n → ℝ)) =ᵐ[
        domainMeasure n (HalfSpace.upper n)] q
    have hbase := flattenCLM_base_eq_classical_ae
      (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) i U φ.1.toFun hUbase
    change
      (((((flattenCLM (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) i U :
          W^{1,2}(HalfSpace.upper n)) :
            WkpAmbientOn n 1 2 (HalfSpace.upper n)) (baseIndex n 1) :
              DerivLp n 2 (HalfSpace.upper n)) : ℝ^n → ℝ)) =ᵐ[
        domainMeasure n (HalfSpace.upper n)] q at hbase
    exact hbase
  exact mem_H10_of_contDiff_one_compactSupport
    (HalfSpace.isOpen_upper (n := n)) F q
    (SobolevSpace.Hardy.flattenedBoundaryPiece_contDiff (hΩ := hΩ) i φ)
    (SobolevSpace.Hardy.flattenedBoundaryPiece_hasCompactSupport (hΩ := hΩ) i φ)
    (SobolevSpace.Hardy.flattenedBoundaryPiece_tsupport_subset_upper (hΩ := hΩ) i φ)
    hFbase

/-- Flattening a localized boundary piece preserves the zero trace condition:
every `H¹₀(Ω)` field is sent by the bounded chart-flattening map to
`H¹₀` on the upper half-space.

This is Evans's (60), which precedes the flat-boundary difference-quotient
argument in §6.3.2. -/
theorem flattenCLM_mem_H10
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (u : H¹₀(Ω)) :
    flattenCLM (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) i
        (u : H¹(Ω)) ∈
      (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).toSubmodule := by
  let T := flattenCLM (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) i
  let C : Set (H¹(Ω)) :=
    (ccSmoothSubmoduleOn (n := n) (Ω := Ω) :
      Submodule ℝ (H¹(Ω)))
  let Z : Set (H¹(HalfSpace.upper n)) :=
    (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).toSubmodule
  have hmaps : Set.MapsTo T C Z := by
    rintro v ⟨φ, rfl⟩
    exact flattenCLM_core_mem_H10 hΩ i φ
  have hu : (u : H¹(Ω)) ∈ closure C := by
    exact H10SpaceOn.mem_closure_CcSmooth
      (n := n) (Ω := Ω) u
  have hTu : T (u : H¹(Ω)) ∈ closure Z :=
    hmaps.closure T.continuous hu
  have hZclosed : IsClosed Z :=
    (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).isClosed'
  rw [hZclosed.closure_eq] at hTu
  exact hTu

/-- The flattened zero-trace field, as an element of upper-half-space
`H¹₀`. -/
noncomputable def flattenH10
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N) :
    H¹₀(Ω) →L[ℝ]
      H¹₀(HalfSpace.upper n) :=
  ContinuousLinearMap.codRestrict
    ((flattenCLM (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) i).comp
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule.subtypeL)
    (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).toSubmodule
    (flattenCLM_mem_H10 hΩ i)

/-- Forgetting the zero-trace constraint identifies `flattenH10` with the `H¹` chart map. -/
@[simp] theorem flattenH10_coe
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (u : H¹₀(Ω)) :
    ((flattenH10 hΩ i u :
      H¹₀(HalfSpace.upper n)) :
      H¹(HalfSpace.upper n)) =
      flattenCLM (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) i
        (u : H¹(Ω)) :=
  rfl

end SobolevSpace.Extension.C1.BoundaryPiece
