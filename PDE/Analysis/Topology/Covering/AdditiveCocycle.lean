/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# Additive transition constants on a simply connected space

Local potentials with equal derivatives differ by constants on connected
overlaps. Their transition constants satisfy an additive cocycle identity. On a
simply connected base, they can be removed by changing one constant on each
connected member of the open cover.

We equip the additive coefficient group with the discrete topology and form the
covering described by the transitions. Mathlib's covering-lift theorem supplies
a continuous section. In each connected chart its discrete coordinate is
constant, giving the required additive corrections.
-/

@[expose] public noncomputable section

open Set Topology

namespace Topology

variable {X ι A : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] [AddCommGroup A]

/-- Constant additive transitions on a connected open cover of a simply
connected space are differences of constants. Empty cover members are allowed;
the conclusion concerns only nonempty overlaps. -/
theorem exists_sub_eq_of_additive_cocycle
    (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hconn : ∀ i, IsPreconnected (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (c : ι → ι → A) (hself : ∀ i, c i i = 0)
    (hcocycle : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, c i j + c j k = c i k) :
    ∃ a : ι → A, ∀ i j, (U i ∩ U j).Nonempty → a j - a i = c i j := by
  classical
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let Z : FiberBundleCore ι X A :=
    { baseSet := U
      isOpen_baseSet := hopen
      indexAt := fun x ↦ (hcover x).choose
      mem_baseSet_at := fun x ↦ (hcover x).choose_spec
      coordChange := fun i j _ a ↦ a + c i j
      coordChange_self := fun i _ _ a ↦ by simp [hself]
      continuousOn_coordChange := fun i j ↦
        ((continuous_of_discreteTopology : Continuous (fun a : A ↦ a + c i j)).comp
          continuous_snd).continuousOn
      coordChange_comp := fun i j k x hx a ↦ by rw [add_assoc, hcocycle i j k x hx] }
  have hcov : IsCoveringMap Z.proj :=
    IsFiberBundle.isCoveringMap fun x ↦
      ⟨Z.localTriv (Z.indexAt x), Z.mem_baseSet_at x⟩
  let x₀ : X := Classical.arbitrary X
  obtain ⟨s, ⟨_, hs⟩, _⟩ :=
    hcov.existsUnique_continuousMap_lifts (ContinuousMap.id X) x₀
      (⟨x₀, (0 : A)⟩ : Z.TotalSpace) rfl
  have hproj (x : X) : (s x).1 = x := congrFun hs x
  let coord (i : ι) (x : X) : A := (Z.localTriv i (s x)).2
  have hcoord (i : ι) : ContinuousOn (coord i) (U i) := by
    apply continuous_snd.comp_continuousOn
    apply (Z.localTriv i).continuousOn.comp s.continuous.continuousOn
    intro x hx
    change (s x).1 ∈ U i
    rwa [hproj x]
  let a (i : ι) : A := if h : (U i).Nonempty then coord i h.choose else 0
  have hconstant (i : ι) {x : X} (hx : x ∈ U i) : coord i x = a i := by
    have hi : (U i).Nonempty := ⟨x, hx⟩
    dsimp only [a]
    rw [dite_eq_left hi]
    exact (hconn i).constant (hcoord i) hx hi.choose_spec
  refine ⟨a, ?_⟩
  rintro i j ⟨x, hxi, hxj⟩
  have htransition : coord i x + c i j = coord j x := by
    change ((show A from (s x).2) + c (Z.indexAt (s x).1) i) + c i j =
      (show A from (s x).2) + c (Z.indexAt (s x).1) j
    have hmem : (s x).1 ∈ U (Z.indexAt (s x).1) ∩ U i ∩ U j :=
      ⟨⟨Z.mem_baseSet_at (s x).1, by simpa only [hproj x] using hxi⟩,
        by simpa only [hproj x] using hxj⟩
    rw [add_assoc, hcocycle _ i j (s x).1 hmem]
  rw [hconstant i hxi, hconstant j hxj] at htransition
  exact (sub_eq_iff_eq_add).mpr (by simpa only [add_comm] using htransition.symm)

end Topology
