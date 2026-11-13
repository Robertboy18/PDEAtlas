/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jet.Composition
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Differentiating diagonal transport

The spatial slope of a C² solution satisfies its differentiated equation along
an actual characteristic. Schwarz symmetry supplies the mixed derivative
identity. The differentiated equation is derived from the original PDE.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace PDE.Analysis.Transport

variable {ι : Type*} [Fintype ι]
  {v : ℝ × ℝ → ι → ℝ} {B : ι → (ι → ℝ) → ℝ}
  {s : Set (ℝ × ℝ)}

/-- Differentiation in the spatial direction of the actual transport residual
gives the quadratic slope identity. -/
theorem second_jet_transport
    (hv : ContinuousSecondJetOn v s) (hs : IsOpen s)
    (hB : ∀ i, Differentiable ℝ (B i))
    (hpde : ∀ p ∈ s, ∀ i, fderiv ℝ v p (1, B i (v p)) i = 0)
    {p : ℝ × ℝ} (hp : p ∈ s) (i : ι) :
    hv.second p (1, B i (v p)) (0, 1) i =
      -(fderiv ℝ (B i) (v p) (hv.first p (0, 1))) * hv.first p (0, 1) i := by
  have hdir := (hasFDerivAt_const (1 : ℝ) p).prodMk
    ((hB i (v p)).hasFDerivAt.comp p (hv.hasFDerivAt hs hp))
  have hd := hasFDerivAt_pi'.mp
    ((hv.hasFDerivAt_first hs hp).clm_apply hdir) i
  have heq : (fun q ↦ hv.first q (1, B i (v q)) i) =ᶠ[𝓝 p] (fun _ ↦ 0) := by
    filter_upwards [hs.mem_nhds hp] with q hq
    rw [hv.first_eq hq]
    exact hpde q hq i
  have hzero := (hd.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_const 0 p)
  have hz := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ ↦ L (0, 1)) hzero
  change hv.first p (0, fderiv ℝ (B i) (v p) (hv.first p (0, 1))) i +
    hv.second p (0, 1) (1, B i (v p)) i = 0 at hz
  have hvec : ((0 : ℝ), fderiv ℝ (B i) (v p) (hv.first p (0, 1))) =
      (fderiv ℝ (B i) (v p) (hv.first p (0, 1))) • ((0, 1) : ℝ × ℝ) := by
    simp
  rw [hvec, map_smul] at hz
  have hsym := congrArg (fun z : ι → ℝ ↦ z i)
    (hv.second_apply_comm hs hp (0, 1) (1, B i (v p)))
  simp only [Pi.smul_apply, smul_eq_mul] at hz
  linarith

/-- The actual spatial slope obeys the differentiated transport ODE along a
characteristic. The continuous first-jet trace is used at time endpoints;
this derivative assertion is local at an interior point. -/
theorem hasDerivAt_spatial_slope_along_characteristic
    (hv : ContinuousSecondJetOn v s) (hs : IsOpen s)
    (hB : ∀ i, Differentiable ℝ (B i))
    (hpde : ∀ p ∈ s, ∀ i, fderiv ℝ v p (1, B i (v p)) i = 0)
    {α : ℝ → ℝ} {t : ℝ} (ht : (t, α t) ∈ s) (i : ι)
    (hα : HasDerivAt α (B i (v (t, α t))) t) :
    HasDerivAt (fun r ↦ hv.first (r, α r) (0, 1) i)
      (-(fderiv ℝ (B i) (v (t, α t)) (hv.first (t, α t) (0, 1))) *
        hv.first (t, α t) (0, 1) i) t := by
  have hpath := (hasDerivAt_id t).prodMk hα
  have hd := ((hv.hasFDerivAt_first hs ht).clm_apply
    (hasFDerivAt_const (0, 1) (t, α t))).comp_hasDerivAt t hpath
  have hi := hasDerivAt_pi.mp hd i
  simpa only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply,
    Function.comp_def, id_eq,
    second_jet_transport hv hs hB hpde ht i] using hi

/-- Another component changes along a characteristic by the signed difference
of the two transport speeds times its spatial slope. -/
theorem hasDerivAt_value_along_characteristic
    (hv : ContinuousSecondJetOn v s) (hs : IsOpen s)
    (hpde : ∀ p ∈ s, ∀ j, fderiv ℝ v p (1, B j (v p)) j = 0)
    {α : ℝ → ℝ} {t : ℝ} (ht : (t, α t) ∈ s) (i j : ι)
    (hα : HasDerivAt α (B i (v (t, α t))) t) :
    HasDerivAt (fun r ↦ v (r, α r) j)
      ((B i (v (t, α t)) - B j (v (t, α t))) *
        hv.first (t, α t) (0, 1) j) t := by
  let p := (t, α t)
  have hd := hasDerivAt_pi.mp
    ((hv.hasFDerivAt hs ht).comp_hasDerivAt t ((hasDerivAt_id t).prodMk hα)) j
  have heq : (1, B i (v p)) =
      (1, B j (v p)) + (B i (v p) - B j (v p)) • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  have hzero : hv.first p (1, B j (v p)) j = 0 := by
    rw [hv.first_eq ht]
    exact hpde p ht j
  have hvalue : hv.first p (1, B i (v p)) j =
      (B i (v p) - B j (v p)) * hv.first p (0, 1) j := by
    rw [heq, map_add, map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzero, zero_add]
  change HasDerivAt (fun r ↦ v (r, α r) j) (hv.first p (1, B i (v p)) j) t at hd
  rw [hvalue] at hd
  exact hd

/-- The transported component is constant on the entire closed characteristic,
including the initial and terminal faces. Only interior time derivatives are
used in the constancy argument. -/
theorem value_eq_initial_along_characteristic
    {T : ℝ} (hT : 0 < T)
    (hv : ContinuousSecondJetOn v (Ioo (0 : ℝ) T ×ˢ univ))
    (hpde : ∀ p : ℝ × ℝ, p.1 ∈ Ioo 0 T → ∀ j,
      fderiv ℝ v p (1, B j (v p)) j = 0)
    {α : ℝ → ℝ} (hcont : ContinuousOn α (Icc (0 : ℝ) T)) (i : ι)
    (hα : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt α (B i (v (t, α t))) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    v (t, α t) i = v (0, α 0) i := by
  have hclosure : closure (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) =
      Icc (0 : ℝ) T ×ˢ univ := by
    rw [closure_prod_eq, closure_Ioo hT.ne, closure_univ]
  have hc : ContinuousOn (fun r ↦ v (r, α r) i) (Icc (0 : ℝ) T) :=
    (continuous_apply i).comp_continuousOn
      ((hclosure ▸ hv.continuousOn).comp (continuousOn_id.prodMk hcont)
        (fun _ hr ↦ ⟨hr, mem_univ _⟩))
  have hd : ∀ r ∈ Ioo (0 : ℝ) T, HasDerivAt (fun r ↦ v (r, α r) i) 0 r := by
    intro r hr
    simpa only [sub_self, zero_mul] using
      hasDerivAt_value_along_characteristic hv (isOpen_Ioo.prod isOpen_univ)
        (fun p hp j ↦ hpde p hp.1 j) ⟨hr, mem_univ _⟩ i i (hα r hr)
  obtain ⟨c, heq⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun r hr ↦ (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr ↦ (hd r hr).deriv)
  have hclosed : EqOn (fun r ↦ v (r, α r) i) (fun _ ↦ c) (Icc (0 : ℝ) T) :=
    Set.EqOn.of_subset_closure heq hc continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hT.ne])
  exact (hclosed ht).trans (hclosed ⟨le_rfl, hT.le⟩).symm

end PDE.Analysis.Transport
