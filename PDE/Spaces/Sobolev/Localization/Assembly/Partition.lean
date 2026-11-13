/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation
import PDE.Spaces.Sobolev.GraphSpace.FiniteSums

/-!
# Global assembly of localized Sobolev pieces

The proof of boundary `H²` regularity in Evans §6.3.2, Theorem 4, ends by covering `∂U` with
finitely many sets on which the boundary estimate holds and summing these estimates with the
interior estimate. We carry out this step with a finite partition of unity: one interior piece
and finitely many boundary-chart pieces are proved to have the required Sobolev order, and their
sum represents the original function because the partition functions add to one. The step uses
no PDE and is uniform in the Sobolev order.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, proof of Theorem 4, step 10, p. 340.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function
open scoped ENNReal

variable {n m : ℕ} {Ω : Set (ℝ^n)}

/-- The canonical finite sum of one interior Sobolev piece and a family of
boundary-chart pieces. -/
noncomputable def partitionAssembly {N : ℕ}
    (W₀ : W^{m,2}(Ω))
    (Wᵢ : Fin N → W^{m,2}(Ω)) :
    W^{m,2}(Ω) :=
  W₀ + ∑ i, Wᵢ i

/-- If the pieces in `partitionAssembly` represent the products of a function
with the interior and boundary cutoffs of a `Boundary.C1ExtensionAtlas`, then
the base coordinate of the assembly represents the original function. -/
theorem partitionAssembly_base_ae
    [Fact (0 < n)]
    (hΩ : SobolevSpace.Boundary.C1ExtensionAtlas n Ω)
    (u : ℝ^n → ℝ)
    (W₀ : W^{m,2}(Ω))
    (Wᵢ : Fin hΩ.N → W^{m,2}(Ω))
    (hW₀ :
      (((W₀ : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω) :
          ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] fun x ↦ hΩ.interiorCutoff.toFun x * u x)
    (hWᵢ : ∀ i,
      (((Wᵢ i : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω) :
          ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] fun x ↦ (hΩ.boundaryCutoff i).toFun x * u x) :
    (((partitionAssembly W₀ Wᵢ : WkpAmbientOn n m 2 Ω)
        (baseIndex n m) : DerivLp n 2 Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] u := by
  classical
  let B : W^{m,2}(Ω) := ∑ i, Wᵢ i
  have hB :
      (((B : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω) :
          ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω]
          fun x ↦ ∑ i, (((Wᵢ i : WkpAmbientOn n m 2 Ω) (baseIndex n m) :
            DerivLp n 2 Ω) : ℝ^n → ℝ) x := by
    simpa [B] using
      (coeFn_finsetSum_coordinate (n := n) (k := m) (p := (2 : ℝ≥0∞))
        (Ω := Ω) Finset.univ Wᵢ (baseIndex n m))
  have hpieces : ∀ᵐ x ∂ domainMeasure n Ω, ∀ i : Fin hΩ.N,
      (((Wᵢ i : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω) :
          ℝ^n → ℝ) x = (hΩ.boundaryCutoff i).toFun x * u x :=
    ae_all_iff.2 hWᵢ
  have hmem : ∀ᵐ x ∂ domainMeasure n Ω, x ∈ Ω := by
    simpa [domainMeasure] using
      (ae_restrict_mem hΩ.isOpen.measurableSet :
        ∀ᵐ x ∂ (volume : Measure (ℝ^n)).restrict Ω, x ∈ Ω)
  have hAssembly :
      (((partitionAssembly W₀ Wᵢ : WkpAmbientOn n m 2 Ω)
          (baseIndex n m) : DerivLp n 2 Ω) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω]
          fun x ↦
            (((W₀ : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω) :
              ℝ^n → ℝ) x +
            (((B : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω) :
              ℝ^n → ℝ) x := by
    filter_upwards [MeasureTheory.Lp.coeFn_add
      (((W₀ : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω))
      (((B : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω))] with x hx
    exact hx
  filter_upwards [hAssembly, hW₀, hB, hpieces, hmem] with
      x hxAssembly hx₀ hxB hxpieces hxΩ
  rw [hxAssembly, hx₀, hxB]
  rw [Finset.sum_congr rfl (fun i _ ↦ hxpieces i)]
  rw [← Finset.sum_mul, ← add_mul, hΩ.cutoff_sum_eq_one x hxΩ]
  simp

/-- The graph norm of `partitionAssembly` is bounded by the sum of the norms
of its pieces. -/
theorem norm_partitionAssembly_le {N : ℕ}
    (W₀ : W^{m,2}(Ω))
    (Wᵢ : Fin N → W^{m,2}(Ω)) :
    ‖partitionAssembly W₀ Wᵢ‖ ≤ ‖W₀‖ + ∑ i, ‖Wᵢ i‖ := by
  calc
    ‖partitionAssembly W₀ Wᵢ‖ ≤ ‖W₀‖ + ‖∑ i, Wᵢ i‖ := by
      simpa [partitionAssembly] using norm_add_le W₀ (∑ i, Wᵢ i)
    _ ≤ ‖W₀‖ + ∑ i, ‖Wᵢ i‖ := by
      gcongr
      exact norm_sum_le (Finset.univ : Finset (Fin N)) Wᵢ

end SobolevSpace.GraphSpace
