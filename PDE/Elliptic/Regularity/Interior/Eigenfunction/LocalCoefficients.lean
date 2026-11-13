/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.ClassicalEigenfunction
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData
import PDE.Analysis.MeasureTheory.LocalRepresentative
import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Interior

/-!
# Interior eigenfunction regularity from coefficients on the domain

Coefficient localization constructs the bounded globally Lipschitz elliptic matrix needed
by the eigenfunction bootstrap. The state remains an arbitrary weak eigenfunction;
no higher derivatives of the state, ambient coefficient extension, or boundary atlas are inputs.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

namespace BoundaryRegularity

/-- Bounded weak coefficient derivatives on the domain give higher interior regularity of
an eigenfunction. Its forcing gains derivatives in the eigenfunction bootstrap. -/
theorem exists_eigenfunction_interiorRegularity_of_aeUniformlyElliptic
    (m : ℕ) (hOpen : IsOpen Ω)
    (A : Fin n → Fin n → W^{m + 1,∞}(Ω))
    {alpha : ℝ}
    (hElliptic : AEUniformlyElliptic
      (fun i j ↦ wkpBaseCoordinateCLM (A i j)) alpha)
    (lambda : ℝ) (u : H¹(Ω))
    (hu : IsInteriorWeakDivergenceSolution
      (fun i j ↦ wkpBaseCoordinateCLM (A i j)) (lambda • wkpBaseCoordinateCLM u) u)
    (K : Set (ℝ^n)) (hKcompact : IsCompact K) (hKOmega : K ⊆ Ω) :
    ∃ V : Set (ℝ^n), IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      ∃ W : W^{m + 2,2}(V),
        (wkpBaseCoordinateCLM W : ℝ^n → ℝ)
          =ᵐ[domainMeasure n V] (wkpBaseCoordinateCLM u : ℝ^n → ℝ) := by
  let A1 (i j : Fin n) : W^{1,∞}(Ω) :=
    lowerOrderCLM (n := n) (k := 1) (m := m + 1) (p := ∞) (by omega) (A i j)
  have hA1 : AEUniformlyElliptic
      (fun i j ↦ (A1 i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) alpha := by
    simpa [A1, wkpBaseCoordinateCLM, wkpCoordinateCLM] using hElliptic
  obtain ⟨N, hNopen, hKN, hNΩ, B, b, C, hb, hBrep, hB, hBA⟩ :=
    exists_global_elliptic_extension_of_w1Top hOpen A1 hA1 K hKcompact hKOmega
  let AN (i j : Fin n) : W^{m + 1,∞}(N) :=
    restrictCLM hNopen.measurableSet hNΩ (A i j)
  let uN : H¹(N) := restrictCLM hNopen.measurableSet hNΩ u
  have hAN (i j : Fin n) :
      (wkpBaseCoordinateCLM (n := n) (m := m + 1) (p := ∞) (Ω := N) (AN i j) :
        ℝ^n → ℝ) =ᵐ[domainMeasure n N]
          (restrictDerivLp (n := n) (p := ∞) (subset_univ N) (B i j) : ℝ^n → ℝ) := by
    have hrestrict := restrictCLM_apply_ae
      (n := n) (k := m + 1) (p := ∞) hNopen.measurableSet hNΩ (A i j)
      (baseIndex n (m + 1))
    have hBA' :
        (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n N]
          ⇑((A i j : WkpAmbientOn n (m + 1) ∞ Ω) (baseIndex n (m + 1))) := by
      simpa [A1, baseRepresentative] using hBA i j
    have hBN := restrictDerivLp_apply_ae
      (n := n) (p := ∞) (subset_univ N) (B i j)
    filter_upwards [hrestrict, hBA', hBN] with x hxA hxBA hxB
    change ((AN i j : WkpAmbientOn n (m + 1) ∞ N) (baseIndex n (m + 1)) :
      DerivLp n ∞ N) x = _
    exact hxA.trans (hxBA.symm.trans hxB.symm)
  have huN : IsInteriorWeakDivergenceSolution
      (fun i j ↦ wkpBaseCoordinateCLM
        (n := n) (m := m + 1) (p := ∞) (Ω := N) (AN i j))
      (lambda • wkpBaseCoordinateCLM uN) uN := by
    simpa [AN, uN, wkpBaseCoordinateCLM, wkpCoordinateCLM,
      restrictCLM_apply_coe, restrictAmbient_apply, map_smul] using hu.restrict hNopen hNΩ
  have hcoeff : (fun i j ↦ wkpBaseCoordinateCLM (AN i j)) =
      (fun i j ↦ restrictDerivLp (n := n) (p := ∞) (subset_univ N) (B i j)) := by
    funext i j
    exact Lp.ext (hAN i j)
  rw [hcoeff] at huN
  obtain ⟨V, hVopen, hKV, hVN, W, hW⟩ :=
    exists_eigenfunction_interiorRegularity_open_neighborhood_of_compact
      m hNopen B b C hb hBrep hB AN hAN lambda uN huN K hKcompact hKN
  refine ⟨V, hVopen, hKV, hVN.trans hNΩ, W, hW.trans ?_⟩
  exact (ae_mono (domainMeasure_le hVN))
    (restrictCLM_apply_ae (n := n) (k := 1) (p := 2)
      hNopen.measurableSet hNΩ u (baseIndex n 1))

end BoundaryRegularity

/-- A prescribed finite classical order follows from the domain's bounded weak coefficient
derivatives. The coefficient extension and the eigenfunction derivatives are constructed. -/
theorem IsInteriorWeakDivergenceSolution.exists_contDiffAt_eigenfunction_of_local_coefficients
    (hn : 0 < n) (k m : ℕ) (hm : k + 1 + n / 2 ≤ m + 2)
    (A : Fin n → Fin n → W^{m + 1,∞}(Ω))
    {alpha : ℝ} (hA : AEUniformlyElliptic (fun i j ↦ wkpBaseCoordinateCLM (A i j)) alpha)
    {lambda : ℝ} {u : H¹(Ω)}
    (hu : IsInteriorWeakDivergenceSolution
      (fun i j ↦ wkpBaseCoordinateCLM (A i j)) (lambda • wkpBaseCoordinateCLM u) u) :
    ∃ f : ℝ^n → ℝ, (∀ x ∈ Ω, ContDiffAt ℝ k f x) ∧
      f =ᵐ[domainMeasure n Ω] (wkpBaseCoordinateCLM u : ℝ^n → ℝ) := by
  apply MeasureTheory.exists_contDiffAt_ae_eq_of_locally (μ := volume)
  intro x hx
  obtain ⟨V, hV, hxV, hVΩ, W, hW⟩ :=
    BoundaryRegularity.exists_eigenfunction_interiorRegularity_of_aeUniformlyElliptic
      m hu.isOpen A hA lambda u hu {x} isCompact_singleton (by simpa using hx)
  obtain ⟨f, hreg, hrep⟩ := exists_contDiffAt_representative_of_order (k := k) hn hV W hm
  exact ⟨V, hV, hxV (by simp), hVΩ, f,
    (fun y hy ↦ (hreg y hy).contDiffWithinAt), hrep.trans hW⟩

/-- Classical closure derivatives supply any finite interior order allowed by the
Sobolev bootstrap and embedding. No coefficient extension is an input. -/
theorem IsInteriorWeakDivergenceSolution.exists_contDiffAt_eigenfunction_of_contDiffUpToBoundary
    (hn : 0 < n) (k m : ℕ) (hm : k + 1 + n / 2 ≤ m + 2)
    (hbounded : Bornology.IsBounded Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary (m + 1) (a i j) Ω)
    (hrep : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    {alpha : ℝ} (hA : AEUniformlyElliptic A alpha)
    {lambda : ℝ} {u : H¹(Ω)}
    (hu : IsInteriorWeakDivergenceSolution A (lambda • wkpBaseCoordinateCLM u) u) :
    ∃ f : ℝ^n → ℝ, (∀ x ∈ Ω, ContDiffAt ℝ k f x) ∧
      f =ᵐ[domainMeasure n Ω] (wkpBaseCoordinateCLM u : ℝ^n → ℝ) := by
  let B (i j : Fin n) : W^{m + 1,∞}(Ω) :=
    (ha i j).toWkpSpaceOn hu.isOpen hbounded ∞
  have hB : (fun i j ↦ wkpBaseCoordinateCLM (B i j)) = A := by
    funext i j
    exact Lp.ext (((ha i j).toWkpSpaceOn_base_ae hu.isOpen hbounded ∞).trans (hrep i j).symm)
  have huB : IsInteriorWeakDivergenceSolution
      (fun i j ↦ wkpBaseCoordinateCLM (B i j)) (lambda • wkpBaseCoordinateCLM u) u := by
    rw [hB]
    exact hu
  exact huB.exists_contDiffAt_eigenfunction_of_local_coefficients hn k m hm B
    (by rw [hB]; exact hA)

/-- Classical closure data give a classical interior representative of every weak
eigenfunction. The domain is bounded and open; its boundary need not admit any graph atlas. -/
theorem IsInteriorWeakDivergenceSolution.exists_classical_eigenfunction_of_contDiffUpToBoundary
    (hn : 0 < n) (hbounded : Bornology.IsBounded Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary (n + 2) (a i j) Ω)
    (hrep : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    {alpha : ℝ} (hA : AEUniformlyElliptic A alpha)
    {lambda : ℝ} {u : H¹(Ω)}
    (hu : IsInteriorWeakDivergenceSolution A (lambda • wkpBaseCoordinateCLM u) u) :
    ∃ f : ℝ^n → ℝ,
      (wkpBaseCoordinateCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 f x) ∧
      ∀ x ∈ Ω, EllipticMaximum.matrixOperator (fun y i j ↦ a i j y)
        (fun y ↦ WithLp.toLp 2 (fun j ↦ -(∑ i, (∂[i] (a i j)) y)))
        (fun _ ↦ 0) f x = lambda * f x := by
  obtain ⟨f, hreg, hf⟩ :=
    hu.exists_contDiffAt_eigenfunction_of_contDiffUpToBoundary hn 2 (n + 1)
      (by omega) hbounded A a ha hrep hA
  have hforce : ((lambda • wkpBaseCoordinateCLM u : DerivLp n 2 Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ lambda * f x := by
    filter_upwards [Lp.coeFn_smul lambda (wkpBaseCoordinateCLM u), hf] with x hsm hr
    rw [hsm]
    simp only [Pi.smul_apply, smul_eq_mul, hr]
  have haC1 (i j : Fin n) (x : ℝ^n) (hx : x ∈ Ω) :
      ContDiffAt ℝ 1 (a i j) x :=
    ((ha i j).contDiffOn.contDiffAt (hu.isOpen.mem_nhds hx)).of_le (by norm_cast; omega)
  have hequation := hu.neg_sum_partialDeriv_flux_eq_of_representatives
    a hrep haC1 hf.symm hreg hforce
    ((show ContinuousOn f Ω from
      fun x hx ↦ (hreg x hx).continuousAt.continuousWithinAt).const_mul lambda)
  refine ⟨f, hf.symm, hreg, ?_⟩
  intro x hx
  rw [EllipticMaximum.matrixOperator_eq_neg_sum_partialDeriv_flux
    a (fun i j ↦ haC1 i j x hx) (hreg x hx)]
  exact hequation x hx

/-- Smooth closure coefficients give one smooth interior representative of every weak
eigenfunction. Continuity identifies the representatives obtained at each finite order. -/
theorem IsInteriorWeakDivergenceSolution.exists_smooth_eigenfunction_of_contDiffUpToBoundary
    (hn : 0 < n) (hbounded : Bornology.IsBounded Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (ha : ∀ k : ℕ, ∀ i j, ContDiffUpToBoundary k (a i j) Ω)
    (hrep : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    {alpha : ℝ} (hA : AEUniformlyElliptic A alpha)
    {lambda : ℝ} {u : H¹(Ω)}
    (hu : IsInteriorWeakDivergenceSolution A (lambda • wkpBaseCoordinateCLM u) u) :
    ∃ f : ℝ^n → ℝ, (∀ x ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) f x) ∧
      f =ᵐ[domainMeasure n Ω] (wkpBaseCoordinateCLM u : ℝ^n → ℝ) := by
  have hfinite (k : ℕ) : ∃ f : ℝ^n → ℝ, ContDiffOn ℝ k f Ω ∧
      f =ᵐ[domainMeasure n Ω] (wkpBaseCoordinateCLM u : ℝ^n → ℝ) := by
    obtain ⟨f, hreg, hf⟩ :=
      hu.exists_contDiffAt_eigenfunction_of_contDiffUpToBoundary hn k (k + n / 2)
        (by omega) hbounded A a (ha _) hrep hA
    exact ⟨f, fun x hx ↦ (hreg x hx).contDiffWithinAt, hf⟩
  obtain ⟨f, hreg, hf⟩ := MeasureTheory.exists_contDiffOn_ae_eq_of_forall_nat
    (𝕜 := ℝ) (μ := volume) hu.isOpen (Subset.refl Ω) subset_closure hfinite
  exact ⟨f, fun x hx ↦ hreg.contDiffAt (hu.isOpen.mem_nhds hx), hf⟩

end SobolevSpace.GraphSpace
