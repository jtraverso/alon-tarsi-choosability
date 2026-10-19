/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import LeanPool.K5MinorFreeChoosability.Planar.Embedding
public import AlonTarsiLib.GraphPolynomial
public import AlonTarsiLib.PlanarSparse

/-!
# The Alon–Tarsi theorem and 3-choosability of planar bipartite graphs

An *orientation* of a simple graph `G` is a relation `D` such that every arc `D u v` is an edge of
`G`, every edge is oriented in at least one direction, and no edge in both. An *Eulerian
subdigraph* of `D` is a set `F` of arcs with, at every vertex, as many arcs of `F` leaving as
entering; it is *even* or *odd* according to `#F`.

* `AlonTarsi.alon_tarsi`: **Alon–Tarsi (1992).** If `G` has an orientation `D` whose numbers of
  even and odd Eulerian subdigraphs differ, then `G` has a proper colouring from any lists with
  `|L v| > outdeg_D v` for every vertex `v`.
* `AlonTarsi.choosable_three_of_isPlanar_bipartite`: **Alon–Tarsi (1992).** Every finite planar
  bipartite graph is 3-choosable. Planarity is the combinatorial notion of a plane map (a rotation
  system of genus zero) used in the registered entry PALOMAR-2026-10-15-000005
  (`LeanPool.K5MinorFreeChoosability.IsPlanar`).
-/

@[expose] public section

open Finset SimpleGraph

namespace AlonTarsi

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `D` is an orientation of `G`: every arc is an edge, every edge is oriented, never both ways. -/
def IsOrientation (G : SimpleGraph V) (D : V → V → Prop) : Prop :=
  (∀ u v, D u v → G.Adj u v) ∧ (∀ u v, G.Adj u v → D u v ∨ D v u) ∧ ∀ u v, D u v → ¬ D v u

open Classical in
/-- The number of Eulerian subdigraphs of `D` (sets of arcs with in-degree equal to out-degree at
every vertex) whose number of arcs has parity `r`. -/
noncomputable def eulerianCount (D : V → V → Prop) (r : ℕ) : ℕ :=
  #{F ∈ (univ.filter fun p : V × V => D p.1 p.2).powerset |
    (∀ v, #{p ∈ F | p.1 = v} = #{p ∈ F | p.2 = v}) ∧ F.card % 2 = r}

open Classical in
/-- **The Alon–Tarsi theorem (1992).** If an orientation `D` of `G` has different numbers of even
and odd Eulerian subdigraphs, then `G` can be properly coloured from any lists `L` with
`|L v|` larger than the out-degree of `v` in `D`. -/
theorem alon_tarsi {Color : Type*} (G : SimpleGraph V) (D : V → V → Prop)
    (hD : IsOrientation G D) (hEO : eulerianCount D 0 ≠ eulerianCount D 1)
    (L : V → Finset Color) (hL : ∀ v, #{w | D v w} < (L v).card) :
    ∃ f : V → Color, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v := by
  classical
  set A : Finset (V × V) := univ.filter fun p : V × V => D p.1 p.2 with hAdef
  have hsum : ∑ t ∈ A.powerset with (∀ v, #{p ∈ t | p.1 = v} = #{p ∈ t | p.2 = v}),
      (-1 : ℤ) ^ #t = (eulerianCount D 0 : ℤ) - eulerianCount D 1 := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun t : Finset (V × V) => #t % 2 = 0)]
    rw [sub_eq_add_neg]
    congr 1
    · rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)), Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.filter_filter]
      · unfold eulerianCount
        congr 2
      · intro t ht
        rw [Finset.mem_filter] at ht
        exact Even.neg_one_pow (Nat.even_iff.2 ht.2)
    · rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℤ)), Finset.sum_const, nsmul_eq_mul,
        mul_neg_one, Finset.filter_filter]
      · unfold eulerianCount
        congr 3
        ext t
        simp only [A, Finset.mem_filter, Nat.mod_two_ne_zero]
      · intro t ht
        rw [Finset.mem_filter] at ht
        exact Odd.neg_one_pow (Nat.odd_iff.2 (Nat.mod_two_ne_zero.1 ht.2))
  have hne : ∑ t ∈ A.powerset with (∀ v, #{p ∈ t | p.1 = v} = #{p ∈ t | p.2 = v}),
      (-1 : ℤ) ^ #t ≠ 0 := by
    rw [hsum, sub_ne_zero]
    exact fun h => hEO (by exact_mod_cast h)
  set U : Finset Color := univ.biUnion L
  let ι : Color → ℤ := fun c => if h : c ∈ U then ((U.equivFin ⟨c, h⟩ : ℕ) : ℤ) else 0
  have hinj : Set.InjOn ι U := by
    intro c hc c' hc' h
    simp only [ι, Finset.mem_coe.1 hc, Finset.mem_coe.1 hc', ↓reduceDIte] at h
    have := U.equivFin.injective (Fin.ext (by exact_mod_cast h))
    exact congrArg Subtype.val this
  have hLU : ∀ v, L v ⊆ U := fun v c hc => Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _, hc⟩
  have hout : ∀ v, #{a ∈ A | a.1 = v} = #{w | D v w} := by
    intro v
    refine Finset.card_bij' (fun a _ => a.2) (fun w _ => (v, w)) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [← ha.2]; exact ha.1
    · intro w hw
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      simpa using hw
    · intro a ha
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [← ha.2]
    · intro w _
      rfl
  obtain ⟨x, hx, hxne⟩ := exists_eval_graphPoly_ne_zero A hne (fun v => (L v).image ι)
    (fun v => by
      rw [hout, Finset.card_image_of_injOn (hinj.mono (by exact_mod_cast hLU v))]
      exact hL v)
  have hpick : ∀ v, ∃ c ∈ L v, ι c = x v := fun v => Finset.mem_image.1 (hx v)
  choose f hfL hfx using hpick
  refine ⟨f, hfL, fun u v huv hf => ?_⟩
  have hxe : x u = x v := by rw [← hfx u, ← hfx v, hf]
  rcases hD.2.1 u v huv with h | h
  · exact hxne (u, v) (by simp [A, h]) hxe
  · exact hxne (v, u) (by simp [A, h]) hxe.symm

open Classical in
/-- **Hakimi's lemma** (for out-degree two), via Hall's theorem: if every set of edges spans at
least half as many vertices as it has edges, then `G` has an orientation with all out-degrees at
most two. -/
theorem exists_orientation_card_le_two (G : SimpleGraph V)
    (hsp : ∀ s : Finset (Sym2 V), (∀ e ∈ s, e ∈ G.edgeSet) → #s ≤ 2 * #{v | ∃ e ∈ s, v ∈ e}) :
    ∃ D : V → V → Prop, IsOrientation G D ∧ ∀ v, #{w | D v w} ≤ 2 := by
  let t : G.edgeSet → Finset (V × Bool) := fun e => univ.filter fun p => p.1 ∈ (e : Sym2 V)
  have hHall : ∀ s : Finset G.edgeSet, #s ≤ #(s.biUnion t) := by
    intro s
    have h := hsp (s.map (Function.Embedding.subtype _)) (fun e he => by
      obtain ⟨e', _, rfl⟩ := Finset.mem_map.1 he
      exact e'.2)
    have hb : s.biUnion t =
        ({v | ∃ e ∈ s.map (Function.Embedding.subtype _), v ∈ e} : Finset V) ×ˢ univ := by
      ext ⟨v, b⟩
      simp [t]
    rw [hb, Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]
    rwa [Finset.card_map] at h
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hHall
  have hfmem : ∀ e : G.edgeSet, (f e).1 ∈ e.1 := fun e => by
    have := hft e
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  let D : V → V → Prop := fun u w => ∃ h : G.Adj u w, (f ⟨s(u, w), G.mem_edgeSet.2 h⟩).1 = u
  have hsymm : ∀ u w (h : G.Adj u w),
      (⟨s(w, u), G.mem_edgeSet.2 h.symm⟩ : G.edgeSet) = ⟨s(u, w), G.mem_edgeSet.2 h⟩ :=
    fun u w h => Subtype.ext Sym2.eq_swap
  refine ⟨D, ⟨fun u w h => h.1, fun u w h => ?_, fun u w h h' => ?_⟩, fun u => ?_⟩
  · have := hfmem ⟨s(u, w), G.mem_edgeSet.2 h⟩
    rcases Sym2.mem_iff.1 this with h1 | h1
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr ⟨h.symm, by rw [hsymm u w h]; exact h1⟩
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨_, h3⟩ := h'
    rw [hsymm u w h1] at h3
    exact h1.ne (h2.symm.trans h3)
  · let g : V → Bool := fun w => if h : G.Adj u w then (f ⟨s(u, w), G.mem_edgeSet.2 h⟩).2
      else false
    refine le_trans (Finset.card_le_card_of_injOn (t := (univ : Finset Bool)) g
      (fun _ _ => Finset.mem_coe.2 (mem_univ _)) ?_) (by simp)
    intro w hw w' hw' hgw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw hw'
    obtain ⟨hw1, hw2⟩ := hw
    obtain ⟨hw1', hw2'⟩ := hw'
    simp only [g, hw1, hw1', ↓reduceDIte] at hgw
    have := hfinj (Prod.ext (hw2.trans hw2'.symm) hgw)
    have := congrArg Subtype.val this
    exact (Sym2.congr_right.1 this)

open Classical in
/-- In an orientation of a bipartite graph there are no odd Eulerian subdigraphs. -/
theorem eulerianCount_one_eq_zero (G : SimpleGraph V) (D : V → V → Prop)
    (hD : IsOrientation G D) (side : V → Bool) (hside : ∀ u v, G.Adj u v → side u ≠ side v) :
    eulerianCount D 1 = 0 := by
  unfold eulerianCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro F hF ⟨hE, hodd⟩
  rw [Finset.mem_powerset] at hF
  have hFadj : ∀ p ∈ F, G.Adj p.1 p.2 := fun p hp => by
    have := hF hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hD.1 _ _ this
  have hfib : ∀ (g : V × V → V) (b : Bool),
      #{p ∈ F | side (g p) = b} = ∑ v with side v = b, #{p ∈ F | g p = v} := by
    intro g b
    rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := univ.filter fun v => side v = b)]
    · refine Finset.sum_congr rfl fun v hv => ?_
      rw [Finset.mem_filter] at hv
      rw [Finset.filter_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hp, -, h⟩; exact ⟨hp, h⟩
      · rintro ⟨hp, h⟩; exact ⟨hp, h ▸ hv.2, h⟩
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
      exact hp.2
  have h1 : #{p ∈ F | side p.1 = true} = #{p ∈ F | side p.2 = true} := by
    rw [hfib Prod.fst, hfib Prod.snd]
    exact Finset.sum_congr rfl fun v _ => hE v
  have h2 : #{p ∈ F | side p.2 = true} = #{p ∈ F | ¬ side p.1 = true} := by
    congr 1
    refine Finset.filter_congr fun p hp => ?_
    have := hside _ _ (hFadj p hp)
    revert this
    cases side p.1 <;> cases side p.2 <;> simp
  have h3 := Finset.card_filter_add_card_filter_not (s := F)
    (fun p : V × V => side p.1 = true)
  omega

omit [Fintype V] [DecidableEq V] in
/-- **Alon–Tarsi (1992).** Every finite planar bipartite graph is 3-choosable. -/
theorem choosable_three_of_isPlanar_bipartite [Finite V] {Color : Type*} (G : SimpleGraph V)
    (hP : LeanPool.K5MinorFreeChoosability.IsPlanar G) (hB : G.Colorable 2)
    (L : V → Finset Color) (hL : ∀ v, 3 ≤ (L v).card) :
    ∃ f : V → Color, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨c⟩ := hB
  let side : V → Bool := fun v => decide (c v = 0)
  have hside : ∀ u v, G.Adj u v → side u ≠ side v := by
    intro u v huv
    have hne := c.valid huv
    simp only [side]
    revert hne
    generalize c u = a
    generalize c v = b
    revert a b
    decide
  obtain ⟨D, hD, hout⟩ := exists_orientation_card_le_two G
    (card_le_two_mul_card_verts hP side hside)
  have hEO : eulerianCount D 0 ≠ eulerianCount D 1 := by
    rw [eulerianCount_one_eq_zero G D hD side hside]
    unfold eulerianCount
    refine Finset.card_ne_zero.2 ⟨∅, ?_⟩
    simp
  exact alon_tarsi G D hD hEO L fun v => by
    have h1 := hout v
    have h2 := hL v
    omega

end AlonTarsi
