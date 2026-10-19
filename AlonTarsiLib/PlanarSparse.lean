/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar

/-!
# Planar bipartite graphs are sparse

Every set `s` of edges of a finite planar bipartite graph satisfies `#s ≤ 2 v(s)`, where `v(s)`
is the number of vertices incident to an edge of `s` (`card_le_two_mul_card_verts`).

The proof removes edges at vertices incident to a single edge of `s`; when there is none, the
graph `fromEdgeSet s` is planar (a subgraph of a planar graph, `isPlanar_of_le`) and bipartite
with all non-isolated vertices of degree at least two, so all its faces have length at least
four (`four_le_card_face_of_two_le`) and Euler's formula `PlaneMap.euler` gives the bound
(`card_edgeSet_le_of_isPlanar_bipartite`).
-/

@[expose] public section

open Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

namespace AlonTarsi

variable {V : Type*}

/-- A subgraph of a finite planar graph is planar. -/
theorem isPlanar_of_le [Finite V] {G H : SimpleGraph V} (hG : IsPlanar G) (h : H ≤ G) :
    IsPlanar H :=
  isPlanar_of_minorModel hG
    { branch := fun w => {w}
      branch_nonempty := fun w => Finset.singleton_nonempty _
      branch_connected := fun w => by
        rw [← connSet_iff_induce_connected]
        simpa using connSet_singleton G w
      branch_disjoint := fun w w' hw => by simpa using hw
      branch_adjacent := fun w w' hw => ⟨w, by simp, w', by simp, h hw⟩ }

section Faces

variable {H : SimpleGraph V} {σ : Perm H.Dart} (hσ : IsRotationSystem H σ)
include hσ

/-- Variant of `face_face_ne_self` requiring degree at least two only at non-isolated
vertices. -/
theorem face_face_ne_self_of_two_le [Finite V]
    (hdeg : ∀ v u, H.Adj v u → 2 ≤ Nat.card {w // H.Adj v w})
    (d : H.Dart) : (σ * dartSymm H) ((σ * dartSymm H) d) ≠ d := by
  intro h
  set e := (σ * dartSymm H) d with he
  have h1 : e.fst = d.snd := facePerm_fst hσ d
  have h2 : e.snd = d.fst := by
    have := facePerm_fst hσ e
    rw [h] at this
    exact this.symm
  have hed : e = d.symm := SimpleGraph.Dart.ext_iff _ _ |>.2 (Prod.ext h1 h2)
  have hfix : σ d.symm = d.symm := by
    have : (σ * dartSymm H) d = σ d.symm := rfl
    rw [← this, ← he, hed]
  have hall : ∀ u (hu : H.Adj d.snd u), (⟨(d.snd, u), hu⟩ : H.Dart) = d.symm := by
    intro u hu
    exact ((hσ.sameCycle d.symm ⟨(d.snd, u), hu⟩ rfl).eq_of_left hfix).symm
  have hnt : Nontrivial {u // H.Adj d.snd u} :=
    Finite.one_lt_card_iff_nontrivial.1 (by have := hdeg d.snd d.fst d.adj.symm; omega)
  obtain ⟨⟨u, hu⟩, ⟨u', hu'⟩, hne⟩ := hnt.exists_pair_ne
  have k1 := hall u hu
  have k2 := hall u' hu'
  apply hne
  have := congrArg (fun e : H.Dart => e.snd) (k1.trans k2.symm)
  exact Subtype.ext this

/-- Variant of `four_le_card_face` requiring degree at least two only at non-isolated
vertices: in a bipartite graph, every face has length at least four. -/
theorem four_le_card_face_of_two_le [Finite V]
    (hdeg : ∀ v u, H.Adj v u → 2 ≤ Nat.card {w // H.Adj v w})
    (side : V → Bool) (hside : ∀ u v, H.Adj u v → side u ≠ side v) (d : H.Dart) :
    4 ≤ Nat.card {e // SameCycle (σ * dartSymm H) d e} := by
  classical
  have := Fintype.ofFinite V
  set φ := σ * dartSymm H
  have hs : ∀ e : H.Dart, side (φ e).fst = !side e.fst := by
    intro e
    rw [facePerm_fst hσ]
    have := hside _ _ e.adj
    revert this
    cases side e.fst <;> cases side e.snd <;> simp
  have n1 : φ d ≠ d := face_ne_self hσ d
  have n2 : φ (φ d) ≠ d := face_face_ne_self_of_two_le hσ hdeg d
  have n3 : φ (φ (φ d)) ≠ d := by
    intro h
    have := hs (φ (φ d))
    rw [h, hs, hs] at this
    cases side d.fst <;> simp at this
  have m1 : φ (φ d) ≠ φ d := face_ne_self hσ (φ d)
  have m2 : φ (φ (φ d)) ≠ φ d := face_face_ne_self_of_two_le hσ hdeg (φ d)
  have m3 : φ (φ (φ d)) ≠ φ (φ d) := face_ne_self hσ (φ (φ d))
  refine le_natCard_of_list [d, φ d, φ (φ d), φ (φ (φ d))] ?_ ?_
  · simp [Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm m1, Ne.symm m2, Ne.symm m3]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact SameCycle.refl _ _
    · exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    · exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))
    · exact sameCycle_apply_right.2 (sameCycle_apply_right.2
        (sameCycle_apply_right.2 (SameCycle.refl _ _)))

/-- The rotation cycles are indexed by the non-isolated vertices. -/
theorem cycleCount_le_card_nonisolated [Fintype V] [DecidableRel H.Adj] :
    cycleCount σ ≤ #{v | ∃ u, H.Adj v u} := by
  unfold cycleCount numClasses
  calc Nat.card (Quotient (SameCycle.setoid σ)) ≤ Nat.card {v // ∃ u, H.Adj v u} := by
        refine Nat.card_le_card_of_injective (Quotient.lift
          (fun d : H.Dart => (⟨d.fst, d.snd, d.adj⟩ : {v // ∃ u, H.Adj v u})) ?_) ?_
        · intro a b hab
          have := sameCycle_of_step (Setoid.ker fun d : H.Dart => d.fst)
            (fun z => by rw [Setoid.ker_def]; exact (hσ.fst_apply z).symm) hab
          exact Subtype.ext this
        · intro p q hpq
          induction p using Quotient.inductionOn with
          | h a =>
          induction q using Quotient.inductionOn with
          | h b =>
          apply Quotient.sound
          exact hσ.sameCycle a b (congrArg Subtype.val hpq)
    _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Faces

/-- **Euler bound.** A finite planar bipartite graph whose non-isolated vertices have degree at
least two has at most twice as many edges as non-isolated vertices. -/
theorem card_edgeSet_le_of_isPlanar_bipartite [Fintype V] {H : SimpleGraph V}
    [DecidableRel H.Adj] (hP : IsPlanar H) (side : V → Bool)
    (hside : ∀ u v, H.Adj u v → side u ≠ side v)
    (hdeg : ∀ v u, H.Adj v u → 2 ≤ Nat.card {w // H.Adj v w}) :
    Nat.card H.edgeSet ≤ 2 * #{v | ∃ u, H.Adj v u} := by
  obtain ⟨M⟩ := hP
  have he := M.euler
  have hV := cycleCount_le_card_nonisolated M.isRotationSystem
  have hF : 4 * cycleCount (M.rot * dartSymm H) ≤ Nat.card H.Dart :=
    mul_numClasses_le _ 4 fun d => four_le_card_face_of_two_le M.isRotationSystem hdeg side
      hside d
  have h2 := card_dart_eq_two_mul H
  have hE := card_edgeSet_eq_cycleCount H
  unfold PlaneMap.numFaces PlaneMap.facePerm at he
  omega

/-- **Sparsity of planar bipartite graphs.** Every set `s` of edges of a finite planar
bipartite graph has at most twice as many edges as vertices incident to them. -/
theorem card_le_two_mul_card_verts [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hP : IsPlanar G) (side : V → Bool) (hside : ∀ u v, G.Adj u v → side u ≠ side v) :
    ∀ s : Finset (Sym2 V), (∀ e ∈ s, e ∈ G.edgeSet) → #s ≤ 2 * #{v | ∃ e ∈ s, v ∈ e} := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro hs
  by_cases h1 : ∃ v, ∃ e ∈ s, ∀ e' ∈ s, v ∈ e' ↔ e' = e
  · obtain ⟨v, e, he, hu⟩ := h1
    have hve : v ∈ e := (hu e he).2 rfl
    have ih' := ih (s.erase e) (Finset.erase_ssubset he)
      (fun e' he' => hs e' (Finset.mem_of_mem_erase he'))
    have hsub : ({w | ∃ e' ∈ s.erase e, w ∈ e'} : Finset V) ⊆
        ({w | ∃ e' ∈ s, w ∈ e'} : Finset V).erase v := by
      intro w hw
      simp only [mem_filter, mem_univ, true_and, mem_erase] at hw ⊢
      obtain ⟨e', ⟨hne, he'⟩, hw⟩ := hw
      refine ⟨?_, e', he', hw⟩
      rintro rfl
      exact hne ((hu e' he').1 hw)
    have hvmem : v ∈ ({w | ∃ e' ∈ s, w ∈ e'} : Finset V) := by
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨e, he, hve⟩
    have c1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hvmem] at c1
    rw [Finset.card_erase_of_mem he] at ih'
    have hpos : 0 < #s := Finset.card_pos.2 ⟨e, he⟩
    have hpos2 : 0 < #({w | ∃ e' ∈ s, w ∈ e'} : Finset V) := Finset.card_pos.2 ⟨v, hvmem⟩
    omega
  · have h1' : ∀ v e, e ∈ s → v ∈ e → ∃ e' ∈ s, v ∈ e' ∧ e' ≠ e := by
      intro v e he hve
      by_contra hc
      exact h1 ⟨v, e, he, fun e' he' => ⟨fun hv => by_contra fun hne => hc ⟨e', he', hv, hne⟩,
        fun h => h ▸ hve⟩⟩
    classical
    let H := SimpleGraph.fromEdgeSet (s : Set (Sym2 V))
    have hHG : H ≤ G := fun u w huw => by
      rw [SimpleGraph.fromEdgeSet_adj] at huw
      exact hs _ huw.1
    have hdeg : ∀ v u, H.Adj v u → 2 ≤ Nat.card {w // H.Adj v w} := by
      intro v u hvu
      rw [SimpleGraph.fromEdgeSet_adj] at hvu
      obtain ⟨e', he', hve', hne⟩ := h1' v _ hvu.1 (Sym2.mem_mk_left v u)
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hve'
      have hvw : G.Adj v w := hs _ he'
      have hHvw : H.Adj v w := (SimpleGraph.fromEdgeSet_adj _).2 ⟨he', hvw.ne⟩
      have hHvu : H.Adj v u := (SimpleGraph.fromEdgeSet_adj _).2 hvu
      have hwu : (⟨w, hHvw⟩ : {w // H.Adj v w}) ≠ ⟨u, hHvu⟩ := by
        intro h
        apply hne
        rw [show w = u from congrArg Subtype.val h]
      have := Finite.one_lt_card_iff_nontrivial.2 (nontrivial_of_ne _ _ hwu)
      omega
    have key := card_edgeSet_le_of_isPlanar_bipartite (isPlanar_of_le hP hHG) side
      (fun u v huv => hside u v (hHG huv)) hdeg
    have hEset : H.edgeSet = (s : Set (Sym2 V)) := by
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      ext e
      simp only [Set.mem_sdiff, Finset.mem_coe, and_iff_left_iff_imp]
      intro he
      exact G.not_isDiag_of_mem_edgeSet (hs e he)
    have hEcard : Nat.card H.edgeSet = #s := by
      rw [hEset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hVle : #{v | ∃ u, H.Adj v u} ≤ #({v | ∃ e ∈ s, v ∈ e} : Finset V) := by
      refine Finset.card_le_card fun v hv => ?_
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      obtain ⟨u, hu⟩ := hv
      exact ⟨_, ((SimpleGraph.fromEdgeSet_adj _).1 hu).1, Sym2.mem_mk_left v u⟩
    omega

end AlonTarsi
