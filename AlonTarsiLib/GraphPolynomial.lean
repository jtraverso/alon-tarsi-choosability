/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# The graph polynomial of a set of arcs

For a finite set `A` of arcs `(u, v)` we consider `graphPoly A = ∏_{(u,v) ∈ A} (x_u - x_v)`
over `ℤ`.  Its coefficient at the out-degree monomial `∏_v x_v ^ outdeg_A v` is the signed count
`∑ (-1) ^ #F` over the Eulerian subsets `F ⊆ A` (`coeff_outExp_graphPoly`).  Together with the
Combinatorial Nullstellensatz this gives `exists_eval_graphPoly_ne_zero`.
-/

@[expose] public section

open Finset MvPolynomial

namespace AlonTarsi

variable {V : Type*}

/-- The graph polynomial `∏_{(u,v) ∈ A} (x_u - x_v)`. -/
noncomputable def graphPoly (A : Finset (V × V)) : MvPolynomial V ℤ :=
  ∏ a ∈ A, (X a.1 - X a.2)

/-- The out-degree exponent `∑_{(u,v) ∈ A} e_u`. -/
noncomputable def outExp (A : Finset (V × V)) : V →₀ ℕ :=
  ∑ a ∈ A, Finsupp.single a.1 1

theorem sum_single_apply [DecidableEq V] (s : Finset (V × V)) (g : V × V → V) (v : V) :
    (∑ a ∈ s, Finsupp.single (g a) 1 : V →₀ ℕ) v = #{a ∈ s | g a = v} := by
  rw [Finsupp.finsetSum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

theorem outExp_apply [DecidableEq V] (A : Finset (V × V)) (v : V) :
    outExp A v = #{a ∈ A | a.1 = v} :=
  sum_single_apply A Prod.fst v

theorem degree_outExp (A : Finset (V × V)) : (outExp A).degree = #A := by
  classical
  unfold outExp
  rw [map_sum]
  simp [Finsupp.degree_single]

theorem totalDegree_graphPoly (A : Finset (V × V)) : (graphPoly A).totalDegree ≤ #A := by
  unfold graphPoly
  refine (totalDegree_finsetProd _ _).trans ?_
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun a _ => ?_
  refine (totalDegree_sub _ _).trans ?_
  simp [totalDegree_X]

theorem eval_graphPoly (A : Finset (V × V)) (x : V → ℤ) :
    eval x (graphPoly A) = ∏ a ∈ A, (x a.1 - x a.2) := by
  simp [graphPoly, map_prod]

/-- The coefficient of the out-degree monomial in the graph polynomial is the signed number of
Eulerian subsets of `A`. -/
theorem coeff_outExp_graphPoly [DecidableEq V] [Fintype V] (A : Finset (V × V)) :
    (graphPoly A).coeff (outExp A) =
      ∑ t ∈ A.powerset with (∀ v, #{p ∈ t | p.1 = v} = #{p ∈ t | p.2 = v}), (-1 : ℤ) ^ #t := by
  have hexp : graphPoly A = ∑ t ∈ A.powerset,
      monomial (∑ a ∈ t, Finsupp.single a.2 1 + ∑ a ∈ A \ t, Finsupp.single a.1 1)
        ((-1 : ℤ) ^ #t) := by
    unfold graphPoly
    have : ∀ a : V × V, (X a.1 - X a.2 : MvPolynomial V ℤ) = -X a.2 + X a.1 := fun a => by ring
    simp_rw [this]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h1 : ∏ a ∈ t, (-X a.2 : MvPolynomial V ℤ) =
        C ((-1 : ℤ) ^ #t) * monomial (∑ a ∈ t, Finsupp.single a.2 1) 1 := by
      rw [monomial_sum_one]
      have : ∀ a : V × V,
          (-X a.2 : MvPolynomial V ℤ) = C (-1) * monomial (Finsupp.single a.2 1) 1 := fun a => by
            rw [← X, map_neg, map_one]; ring
      simp_rw [this]
      rw [Finset.prod_mul_distrib, Finset.prod_const, map_pow]
    have h2 : ∏ a ∈ A \ t, (X a.1 : MvPolynomial V ℤ) =
        monomial (∑ a ∈ A \ t, Finsupp.single a.1 1) 1 := by
      rw [monomial_sum_one]; rfl
    rw [h1, h2, mul_assoc, monomial_mul_monomial, one_mul, C_mul_monomial, mul_one]
  rw [hexp, coeff_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_powerset] at ht
  rw [coeff_monomial]
  congr 1
  apply propext
  rw [Finsupp.ext_iff]
  refine forall_congr' fun v => ?_
  rw [Finsupp.add_apply, sum_single_apply, sum_single_apply, outExp_apply]
  have hsplit : #{a ∈ A | a.1 = v} = #{a ∈ A \ t | a.1 = v} + #{a ∈ t | a.1 = v} := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext a
      simp only [mem_filter, mem_union, mem_sdiff]
      constructor
      · rintro ⟨ha, rfl⟩
        by_cases hat : a ∈ t
        · exact Or.inr ⟨hat, rfl⟩
        · exact Or.inl ⟨⟨ha, hat⟩, rfl⟩
      · rintro (⟨⟨ha, _⟩, rfl⟩ | ⟨ha, rfl⟩)
        · exact ⟨ha, rfl⟩
        · exact ⟨ht ha, rfl⟩
    · rw [Finset.disjoint_left]
      intro a ha hb
      simp only [mem_filter, mem_sdiff] at ha hb
      exact ha.1.2 hb.1
  omega

/-- **Alon–Tarsi via the Combinatorial Nullstellensatz.** If the signed number of Eulerian
subsets of `A` is nonzero, then from any sets `S v` larger than the out-degrees one can pick
values separating the endpoints of every arc. -/
theorem exists_eval_graphPoly_ne_zero [DecidableEq V] [Fintype V] (A : Finset (V × V))
    (hA : ∑ t ∈ A.powerset with (∀ v, #{p ∈ t | p.1 = v} = #{p ∈ t | p.2 = v}),
      (-1 : ℤ) ^ #t ≠ 0)
    (S : V → Finset ℤ) (hS : ∀ v, #{a ∈ A | a.1 = v} < #(S v)) :
    ∃ x : V → ℤ, (∀ v, x v ∈ S v) ∧ ∀ a ∈ A, x a.1 ≠ x a.2 := by
  have hc : (graphPoly A).coeff (outExp A) ≠ 0 := by rwa [coeff_outExp_graphPoly]
  have hdeg : (graphPoly A).totalDegree = (outExp A).degree := by
    refine le_antisymm ((totalDegree_graphPoly A).trans (degree_outExp A).ge) ?_
    have := le_totalDegree (mem_support_iff.2 hc)
    rw [Finsupp.degree_apply]
    exact this
  obtain ⟨x, hx, hne⟩ := combinatorial_nullstellensatz_exists_eval_nonzero (graphPoly A)
    (outExp A) hc hdeg S (fun v => by rw [outExp_apply]; exact hS v)
  refine ⟨x, hx, fun a ha h => hne ?_⟩
  rw [eval_graphPoly]
  exact Finset.prod_eq_zero ha (by rw [h, sub_self])

end AlonTarsi
