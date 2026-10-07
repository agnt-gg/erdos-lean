import Erdos.Ramsey
import Archive.Wiedijk100Theorems.FriendshipGraphs

/-!
# Erdős Problem 552: $R(C_4, K_{1,n+1}) \le R(C_4, K_{1,n}) + 2$

Burr, Erdős, Faudree, Rousseau and Schelp asked whether $f(n+1) \le f(n) + 2$ for all $n$, where
$f(n) = R(C_4, K_{1,n})$ (erdosproblems.com/552). Chen Guantao proved it
(*A result on $C_4$-star Ramsey numbers*, Discrete Math. 163 (1997), 243–246). This file gives a
formal proof for every $n \ge 1$, stated with `SimpleGraph.graphRamsey` of formal-conjectures.

Proof. Let $N = f(n)$ and let $H$ be a $C_4$-free graph on $N + 2$ vertices. Two distinct vertices
of $H$ have at most one common neighbour.
* If some pair $x \ne y$ has no common neighbour, delete it. The remaining $N$ vertices contain a
  vertex $w$ with at least $n$ non-neighbours. Since $w$ is not adjacent to both $x$ and $y$, it has
  at least $n + 1$ non-neighbours in $H$.
* Otherwise every pair has exactly one common neighbour, so $H$ has a vertex $p$ adjacent to all
  others (friendship theorem). Any other vertex $u$ is adjacent only to $p$ and to the common
  neighbour of $u$ and $p$, so it has at least $N - 1 \ge n + 1$ non-neighbours, as $N \ge n + 2$.
-/

open Finset SimpleGraph

namespace Erdos552

section Lemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A vertex of degree at least `n` gives a copy of the star `K_{1,n}`. -/
lemma star_isContained_of_le_degree (D : SimpleGraph V) [DecidableRel D.Adj] {n : ℕ} {v : V}
    (hv : n ≤ D.degree v) : (completeBipartiteGraph (Fin 1) (Fin n)).IsContained D := by
  rw [← card_neighborFinset_eq_degree] at hv
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hv
  let e : Fin n ≃ s := (s.equivFinOfCardEq hcard).symm
  have hmem : ∀ i, D.Adj v (e i) := fun i => (mem_neighborFinset _ _ _).mp (hs (e i).2)
  let g : Fin 1 ⊕ Fin n → V := Sum.elim (fun _ => v) (fun i => (e i : V))
  have hg : Function.Injective g := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b <;> simp only [g, Sum.elim_inl, Sum.elim_inr] at hab
    · exact congrArg Sum.inl (Subsingleton.elim a b)
    · have h := hmem b
      rw [← hab] at h
      exact (h.ne rfl).elim
    · have h := hmem a
      rw [hab] at h
      exact (h.ne rfl).elim
    · exact congrArg Sum.inr (e.injective (Subtype.ext hab))
  refine ⟨⟨⟨g, ?_⟩, hg⟩⟩
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;> simp [g, completeBipartiteGraph] at hab ⊢
  · exact hmem b
  · exact (hmem a).symm

omit [DecidableEq V] in
/-- A copy of the star `K_{1,n}` has a centre of degree at least `n`. -/
lemma exists_le_degree_of_star_isContained (D : SimpleGraph V) [DecidableRel D.Adj] {n : ℕ}
    (h : (completeBipartiteGraph (Fin 1) (Fin n)).IsContained D) : ∃ v, n ≤ D.degree v := by
  obtain ⟨f⟩ := h
  refine ⟨f (Sum.inl 0), ?_⟩
  rw [← card_neighborFinset_eq_degree]
  have key := Finset.card_le_card_of_injOn (s := (univ : Finset (Fin n)))
    (t := D.neighborFinset (f (Sum.inl 0))) (fun i => f (Sum.inr i)) ?_ ?_
  · simpa using key
  · intro i _
    rw [Finset.mem_coe, mem_neighborFinset]
    exact f.toHom.map_adj (by simp [completeBipartiteGraph])
  · intro i _ j _ hij
    exact Sum.inr_injective (f.injective hij)

omit [Fintype V] [DecidableEq V] in
/-- Two distinct vertices with two distinct common neighbours span a 4-cycle. -/
lemma cycle_isContained_of_two_common (C : SimpleGraph V) {a b x y : V} (hab : a ≠ b)
    (hxy : x ≠ y) (hax : C.Adj a x) (hbx : C.Adj b x) (hay : C.Adj a y) (hby : C.Adj b y) :
    (cycleGraph 4).IsContained C := by
  let f : Fin 4 → V := ![a, x, b, y]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    have hedge : ∀ i j : Fin 4, (cycleGraph 4).Adj i j →
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
        (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3) := by
      intro i j h
      rw [cycleGraph_adj] at h
      revert h
      fin_cases i <;> fin_cases j <;> decide
    rcases hedge i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hax
    · exact hax.symm
    · exact hbx.symm
    · exact hbx
    · exact hby
    · exact hby.symm
    · exact hay.symm
    · exact hay
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, hab, hab.symm, hxy, hxy.symm, hax.ne, hax.ne.symm, hbx.ne, hbx.ne.symm,
        hay.ne, hay.ne.symm, hby.ne, hby.ne.symm] at hij ⊢

end Lemmas

/-- The set whose infimum is `R(C₄, K_{1,n})`. -/
abbrev ramseySet (n : ℕ) : Set ℕ :=
  { m : ℕ | ∀ (C : SimpleGraph (Fin m)),
    (cycleGraph 4).IsContained C ∨ (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Cᶜ }

/-- On `2n + 2` vertices there is a `C₄` or a `K_{1,n}` in the complement: if every vertex has
fewer than `n` non-neighbours, two vertices of degree at least `n + 2` share two neighbours. -/
lemma two_mul_add_two_mem (n : ℕ) : 2 * n + 2 ∈ ramseySet n := by
  intro C
  classical
  by_cases h : ∃ v, n ≤ Cᶜ.degree v
  · obtain ⟨v, hv⟩ := h
    exact Or.inr (star_isContained_of_le_degree _ hv)
  · push Not at h
    left
    have hdeg : ∀ v, n + 2 ≤ C.degree v := by
      intro v
      have hv := h v
      rw [degree_compl, Fintype.card_fin] at hv
      have := C.degree_lt_card_verts v
      rw [Fintype.card_fin] at this
      omega
    let a : Fin (2 * n + 2) := ⟨0, by omega⟩
    let b : Fin (2 * n + 2) := ⟨1, by omega⟩
    have hab : a ≠ b := Fin.ne_of_val_ne (by simp [a, b])
    have hu := Finset.card_union_add_card_inter (C.neighborFinset a) (C.neighborFinset b)
    have hle : (C.neighborFinset a ∪ C.neighborFinset b).card ≤ 2 * n + 2 := by
      simpa using Finset.card_le_univ (C.neighborFinset a ∪ C.neighborFinset b)
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hu
    have hI : 1 < (C.neighborFinset a ∩ C.neighborFinset b).card := by
      have := hdeg a
      have := hdeg b
      omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hI
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hx hy
    exact cycle_isContained_of_two_common C hab hxy hx.1 hx.2 hy.1 hy.2

lemma ramseySet_nonempty (n : ℕ) : (ramseySet n).Nonempty :=
  ⟨_, two_mul_add_two_mem n⟩

/-- The star centred at vertex `0` of `Fin m`. -/
def centreStar (m : ℕ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun u _ => u.val = 0

/-- The star has no 4-cycle: each edge of a 4-cycle needs the centre, and two disjoint edges
cannot both use it. -/
lemma not_cycle_isContained_centreStar (m : ℕ) : ¬ (cycleGraph 4).IsContained (centreStar m) := by
  rintro ⟨f⟩
  have hadj : ∀ i j : Fin 4, (cycleGraph 4).Adj i j → (f i).val = 0 ∨ (f j).val = 0 := by
    intro i j hij
    have h := f.toHom.map_adj hij
    simp only [centreStar, fromRel_adj] at h
    rcases h.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h01 := hadj 0 1 (by simp [cycleGraph_adj'])
  have h23 := hadj 2 3 (by simp [cycleGraph_adj'])
  have hinj : ∀ i j : Fin 4, (f i).val = 0 → (f j).val = 0 → i = j := fun i j hi hj =>
    f.injective (Fin.ext (hi.trans hj.symm))
  rcases h01 with h0 | h1 <;> rcases h23 with h2 | h3
  · exact absurd (hinj 0 2 h0 h2) (by decide)
  · exact absurd (hinj 0 3 h0 h3) (by decide)
  · exact absurd (hinj 1 2 h1 h2) (by decide)
  · exact absurd (hinj 1 3 h1 h3) (by decide)

/-- `R(C₄, K_{1,n}) ≥ n + 2` for `n ≥ 1`: on `m ≤ n + 1` vertices the centred star has no `C₄`,
and in its complement every vertex has degree less than `n`. -/
lemma add_two_le_ramsey (n : ℕ) (hn : 1 ≤ n) :
    n + 2 ≤ graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) := by
  apply le_csInf (ramseySet_nonempty n)
  intro m hm
  by_contra hlt
  push Not at hlt
  classical
  rcases hm (centreStar m) with h4 | hs
  · exact not_cycle_isContained_centreStar m h4
  · obtain ⟨v, hv⟩ := exists_le_degree_of_star_isContained _ hs
    rw [degree_compl, Fintype.card_fin] at hv
    rcases Nat.lt_or_ge m (n + 1) with hsmall | hbig
    · omega
    · -- m = n + 1 ≥ 2, so every vertex of the star has a neighbour
      have hm2 : 2 ≤ m := by omega
      have hpos : 0 < (centreStar m).degree v := by
        rw [(centreStar m).degree_pos_iff_exists_adj]
        by_cases hv0 : v.val = 0
        · refine ⟨⟨1, by omega⟩, ?_⟩
          simp only [centreStar, fromRel_adj]
          exact ⟨Fin.ne_of_val_ne (by simp [hv0]), Or.inl hv0⟩
        · refine ⟨⟨0, by omega⟩, ?_⟩
          simp only [centreStar, fromRel_adj]
          exact ⟨Fin.ne_of_val_ne (by simpa using hv0), by simp⟩
      omega

/-- The main step: `R(C₄, K_{1,n}) + 2` vertices suffice for `K_{1,n+1}`. -/
lemma ramsey_add_two_mem (n : ℕ) (hn : 1 ≤ n) :
    graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) + 2 ∈ ramseySet (n + 1) := by
  set N := graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) with hN_def
  have hNmem : N ∈ ramseySet n := Nat.sInf_mem (ramseySet_nonempty n)
  have hNge : n + 2 ≤ N := add_two_le_ramsey n hn
  intro H
  classical
  by_cases hc : (cycleGraph 4).IsContained H
  · exact Or.inl hc
  right
  -- In a C₄-free graph two distinct vertices have at most one common neighbour.
  have hcommon : ∀ x y, x ≠ y → ∀ a b, H.Adj x a → H.Adj y a → H.Adj x b → H.Adj y b →
      a = b := by
    intro x y hxy a b hxa hya hxb hyb
    by_contra hab
    exact hc (cycle_isContained_of_two_common H hxy hab hxa hya hxb hyb)
  by_cases hpair : ∃ x y, x ≠ y ∧ ∀ v, ¬ (H.Adj x v ∧ H.Adj y v)
  · obtain ⟨x, y, hxy, hno⟩ := hpair
    have hT : Fintype.card {v : Fin (N + 2) // v ≠ x ∧ v ≠ y} = N := by
      rw [Fintype.card_subtype]
      have hfilter : (univ.filter fun v : Fin (N + 2) => v ≠ x ∧ v ≠ y) =
          (univ.erase x).erase y := by
        ext v
        simp [and_comm]
      rw [hfilter, Finset.card_erase_of_mem (by simp [Ne.symm hxy]),
        Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]
      omega
    let e : Fin N ≃ {v : Fin (N + 2) // v ≠ x ∧ v ≠ y} := (Fintype.equivFinOfCardEq hT).symm
    let ι : Fin N → Fin (N + 2) := fun i => (e i).1
    have hι : Function.Injective ι := fun i j h => e.injective (Subtype.ext h)
    rcases hNmem (H.comap ι) with h4 | hs
    · exact absurd (h4.trans ⟨⟨⟨ι, fun h => h⟩, hι⟩⟩) hc
    · obtain ⟨w, hw⟩ := exists_le_degree_of_star_isContained _ hs
      apply star_isContained_of_le_degree Hᶜ (v := ι w)
      -- `ι w` misses `x` or `y`.
      obtain ⟨z, hz, hzxy⟩ : ∃ z, ¬ H.Adj (ι w) z ∧ (z = x ∨ z = y) := by
        by_cases hx : H.Adj (ι w) x
        · exact ⟨y, fun hy => hno (ι w) ⟨hx.symm, hy.symm⟩, Or.inr rfl⟩
        · exact ⟨x, hx, Or.inl rfl⟩
      have hzι : ∀ i, ι i ≠ z := by
        intro i hi
        rcases hzxy with rfl | rfl
        · exact (e i).2.1 hi
        · exact (e i).2.2 hi
      let A := ((H.comap ι)ᶜ.neighborFinset w).map ⟨ι, hι⟩
      have hA : A ⊆ Hᶜ.neighborFinset (ι w) := by
        intro u hu
        simp only [A, Finset.mem_map, mem_neighborFinset, compl_adj, comap_adj,
          Function.Embedding.coeFn_mk] at hu
        obtain ⟨u', ⟨hne, hnadj⟩, rfl⟩ := hu
        rw [mem_neighborFinset, compl_adj]
        exact ⟨fun h => hne (hι h), hnadj⟩
      have hzA : z ∉ A := by
        simp only [A, Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
        exact fun i _ => hzι i
      have hzN : z ∈ Hᶜ.neighborFinset (ι w) := by
        rw [mem_neighborFinset, compl_adj]
        exact ⟨fun h => hzι w h, hz⟩
      have hcard : (insert z A).card ≤ Hᶜ.degree (ι w) := by
        rw [← card_neighborFinset_eq_degree]
        exact Finset.card_le_card (Finset.insert_subset hzN hA)
      rw [Finset.card_insert_of_notMem hzA, Finset.card_map,
        card_neighborFinset_eq_degree] at hcard
      omega
  · push Not at hpair
    -- Every pair has exactly one common neighbour: a friendship graph.
    have hfr : Theorems100.Friendship H := by
      intro v w hvw
      rw [Fintype.card_eq_one_iff]
      obtain ⟨c, hvc, hwc⟩ := hpair v w hvw
      refine ⟨⟨c, H.mem_commonNeighbors.mpr ⟨hvc, hwc⟩⟩, ?_⟩
      rintro ⟨d, hd⟩
      rw [H.mem_commonNeighbors] at hd
      exact Subtype.ext (hcommon v w hvw d c hd.1 hd.2 hvc hwc)
    obtain ⟨p, hp⟩ := Theorems100.friendship_theorem hfr
    obtain ⟨u, hup⟩ := exists_ne p
    obtain ⟨c, huc, hpc⟩ := hpair u p hup
    have hdeg : H.degree u ≤ 2 := by
      rw [← card_neighborFinset_eq_degree]
      calc (H.neighborFinset u).card ≤ ({p, c} : Finset (Fin (N + 2))).card := by
            apply Finset.card_le_card
            intro t ht
            rw [mem_neighborFinset] at ht
            by_cases htp : t = p
            · simp [htp]
            · have hpt : H.Adj p t := hp t (fun h => htp h.symm)
              have htc : t = c := hcommon u p hup t c ht hpt huc hpc
              simp [htc]
        _ ≤ 2 := Finset.card_le_two
    apply star_isContained_of_le_degree Hᶜ (v := u)
    rw [degree_compl, Fintype.card_fin]
    omega

/-- **Chen (1997).** For every `n ≥ 1`, `R(C₄, K_{1,n+1}) ≤ R(C₄, K_{1,n}) + 2`. -/
theorem erdos_552.variants.succ_le_add_two (n : ℕ) (hn : 1 ≤ n) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (completeBipartiteGraph (Fin 1) (Fin (n + 1))) ≤
      SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (completeBipartiteGraph (Fin 1) (Fin n)) + 2 :=
  Nat.sInf_le (ramsey_add_two_mem n hn)

end Erdos552

#print axioms Erdos552.erdos_552.variants.succ_le_add_two
