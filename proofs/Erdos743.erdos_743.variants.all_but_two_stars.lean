import FormalConjectures.ErdosProblems.«743»

/-!
# Proof of Erdős Problem 743 (all but two stars variant)

We formalize Theorem 1 of Gyárfás and Lehel (1978): if `T 2, ..., T n` are trees such that
all but at most two of them are stars, then they pack edge-disjointly into `K_n`.

The proof proceeds by strong induction on `n`:
- Case A: `T n` is a star. Place it centered at the last vertex and recurse on `n - 1`.
- Case B: `T (n - 1)` is a star (and `T n` is not). Peel a leaf from `T n` to form a tree
  of order `n - 1`, pack into `K_{n-1}`, and attach the leaf and `T (n - 1)` using the new vertex.
- Case C: Neither `T n` nor `T (n - 1)` is a star (so all smaller trees are stars, and `n ≥ 5`).
  Each non-star tree has two leaves with distinct parents. Peel both leaves from each,
  pack into `K_{n-2}`, attach the four leaves to two new vertices `u, v` avoiding collisions
  (always possible by swapping `u` and `v`), and assign the remaining edges incident to `u` and `v`
  to the stars `T (n - 2)` and `T (n - 3)`.
-/

namespace OMA_Erdos743_AllButTwoStars

open SimpleGraph

private lemma disjoint_edgeSet_of_adj {V : Type*} {G₁ G₂ : SimpleGraph V}
    (h : ∀ u v : V, G₁.Adj u v → ¬ G₂.Adj u v) :
    Disjoint G₁.edgeSet G₂.edgeSet := by
  rw [Set.disjoint_left]
  intro e he1 he2
  induction e using Sym2.ind with
  | _ u v =>
    exact h u v he1 he2

private lemma isTree_path_length_eq_dist {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq, hqlen⟩ := (hG.connected u v).exists_path_of_dist
  obtain ⟨r, _, huniq⟩ := hG.existsUnique_path u v
  have hpq : p = q := (huniq p hp).trans (huniq q hq).symm
  rw [hpq, hqlen]

private lemma isTree_dist_eq_zero_iff {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {u v : V} : G.dist u v = 0 ↔ u = v := by
  constructor
  · intro h
    obtain ⟨p, hp, hlen⟩ := (hG.connected u v).exists_path_of_dist
    rw [h] at hlen
    exact SimpleGraph.Walk.eq_of_length_eq_zero hlen
  · rintro rfl
    exact SimpleGraph.dist_self

private lemma isTree_max_dist_endpoint_isLeaf {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.IsTree) {u v : V} (hmax : ∀ x y : V, G.dist x y ≤ G.dist u v)
    {p₁ : V} (hadj : G.Adj u p₁) {P' : G.Walk p₁ v} (hP : (Walk.cons hadj P').IsPath) :
    ∀ w : V, G.Adj u w ↔ w = p₁ := by
  intro w
  constructor
  · intro huw
    by_contra hne
    have hw_not_mem : w ∉ (Walk.cons hadj P').support := by
      intro hmem
      simp only [Walk.support_cons, List.mem_cons] at hmem
      rcases hmem with rfl | hmem'
      · exact G.ne_of_adj huw rfl
      · have hP'_path : P'.IsPath := hP.of_cons
        let Q := P'.takeUntil w hmem'
        have hQ_path : Q.IsPath := hP'_path.takeUntil hmem'
        have hu_not_Q : u ∉ Q.support := by
          intro huQ
          have huP' : u ∈ P'.support := Walk.support_takeUntil_subset_support P' hmem' huQ
          have hnd := hP.support_nodup
          simp only [Walk.support_cons, List.nodup_cons] at hnd
          exact hnd.1 huP'
        have hpath2 : (Walk.cons hadj Q).IsPath := Walk.IsPath.cons hQ_path hu_not_Q
        have hpath1 : (Walk.cons huw Walk.nil).IsPath :=
          Walk.IsPath.cons Walk.IsPath.nil (by simp [G.ne_of_adj huw])
        obtain ⟨r, _, huniq⟩ := hG.existsUnique_path u w
        have heq := (huniq _ hpath2).trans (huniq _ hpath1).symm
        have hlen := congrArg Walk.length heq
        simp only [Walk.length_cons, Walk.length_nil] at hlen
        have hQ0 : Q.length = 0 := by omega
        exact hne (Walk.eq_of_length_eq_zero hQ0).symm
    have hbig : (Walk.cons huw.symm (Walk.cons hadj P')).IsPath :=
      Walk.IsPath.cons hP hw_not_mem
    have hdist_w := isTree_path_length_eq_dist hG _ hbig
    have hdist_u := isTree_path_length_eq_dist hG _ hP
    have hle := hmax w v
    simp only [Walk.length_cons] at hdist_w hdist_u
    omega
  · rintro rfl
    exact hadj

private lemma isTree_exists_leaf {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsTree) (hcard : 2 ≤ Fintype.card V) :
    ∃ ℓ p : V, ℓ ≠ p ∧ ∀ w : V, G.Adj ℓ w ↔ w = p := by
  have hne : (Finset.univ : Finset (V × V)).Nonempty := by
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    exact Finset.univ_nonempty
  obtain ⟨⟨u, v⟩, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (V × V))
    (fun q => G.dist q.1 q.2) hne
  have hmax' : ∀ x y : V, G.dist x y ≤ G.dist u v := fun x y => hmax (x, y) (Finset.mem_univ _)
  obtain ⟨P, hP, hPlen⟩ := (hG.connected u v).exists_path_of_dist
  have hpos : 0 < P.length := by
    by_contra h0
    have hlen0 : P.length = 0 := by omega
    have hdist0 : G.dist u v = 0 := by omega
    have hcard1 : Fintype.card V ≤ 1 := by
      rw [Fintype.card_le_one_iff]
      intro x y
      have hxy : G.dist x y = 0 := by have := hmax' x y; omega
      exact (isTree_dist_eq_zero_iff hG).mp hxy
    omega
  cases P with
  | nil => simp at hpos
  | cons hadj P' =>
    rename_i p₁
    refine ⟨u, p₁, G.ne_of_adj hadj, isTree_max_dist_endpoint_isLeaf hG hmax' hadj hP⟩

private lemma isTree_exists_two_leaves_distinct_parents {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.IsTree) (hnotstar : ∀ c : V, G ≠ starGraph c) :
    4 ≤ Fintype.card V ∧
    ∃ ℓ₁ ℓ₂ p₁ p₂ : V,
      ℓ₁ ≠ ℓ₂ ∧ ℓ₁ ≠ p₁ ∧ ℓ₁ ≠ p₂ ∧ ℓ₂ ≠ p₁ ∧ ℓ₂ ≠ p₂ ∧ p₁ ≠ p₂ ∧
      (∀ w : V, G.Adj ℓ₁ w ↔ w = p₁) ∧
      (∀ w : V, G.Adj ℓ₂ w ↔ w = p₂) := by
  have : Nonempty V := hG.connected.nonempty
  obtain ⟨⟨u, v⟩, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (V × V))
    (fun q => G.dist q.1 q.2) Finset.univ_nonempty
  have hmax' : ∀ x y : V, G.dist x y ≤ G.dist u v := fun x y => hmax (x, y) (Finset.mem_univ _)
  obtain ⟨P, hP, hPlen⟩ := (hG.connected u v).exists_path_of_dist
  have hge3 : 3 ≤ G.dist u v := by
    by_contra hlt
    have hle2 : G.dist u v ≤ 2 := by omega
    have hd_cases : G.dist u v = 0 ∨ G.dist u v = 1 ∨ G.dist u v = 2 := by omega
    rcases hd_cases with hd0 | hd1 | hd2
    · apply hnotstar u
      ext x y
      have hx : x = u := (isTree_dist_eq_zero_iff hG).mp (by have := hmax' x u; omega)
      have hy : y = u := (isTree_dist_eq_zero_iff hG).mp (by have := hmax' y u; omega)
      subst hx; subst hy
      simp [starGraph]
    · apply hnotstar u
      ext x y
      simp only [starGraph, SimpleGraph.fromRel_adj]
      constructor
      · intro hxy
        refine ⟨G.ne_of_adj hxy, ?_⟩
        by_contra hne
        have hxu : x ≠ u := fun h => hne (Or.inl h)
        have hyu : y ≠ u := fun h => hne (Or.inr h)
        have hux : G.Adj u x := by
          rw [← SimpleGraph.dist_eq_one_iff_adj]
          have h1 := hmax' u x
          have h0 : G.dist u x ≠ 0 := fun h => hxu ((isTree_dist_eq_zero_iff hG).mp h).symm
          omega
        have huy : G.Adj u y := by
          rw [← SimpleGraph.dist_eq_one_iff_adj]
          have h1 := hmax' u y
          have h0 : G.dist u y ≠ 0 := fun h => hyu ((isTree_dist_eq_zero_iff hG).mp h).symm
          omega
        have hp1 : (Walk.cons hxy Walk.nil).IsPath :=
          Walk.IsPath.cons Walk.IsPath.nil (by simp [G.ne_of_adj hxy])
        have hp2 : (Walk.cons hux.symm (Walk.cons huy Walk.nil)).IsPath :=
          Walk.IsPath.cons (Walk.IsPath.cons Walk.IsPath.nil (by simp [hyu.symm]))
            (by simp [hxu, G.ne_of_adj hxy])
        obtain ⟨r, _, huniq⟩ := hG.existsUnique_path x y
        have hlen := congrArg Walk.length ((huniq _ hp1).trans (huniq _ hp2).symm)
        simp at hlen
      · rintro ⟨hxy, rfl | rfl⟩
        · rw [← SimpleGraph.dist_eq_one_iff_adj]
          have h1 := hmax' x y
          have h0 : G.dist x y ≠ 0 := fun h => hxy ((isTree_dist_eq_zero_iff hG).mp h)
          omega
        · rw [← SimpleGraph.dist_eq_one_iff_adj]
          have h1 := hmax' x y
          have h0 : G.dist x y ≠ 0 := fun h => hxy ((isTree_dist_eq_zero_iff hG).mp h)
          omega
    · rw [hd2] at hPlen
      cases P with
      | nil => simp at hPlen
      | cons h1 P1 =>
        rename_i c
        cases P1 with
        | nil => simp at hPlen
        | cons h2 P2 =>
          rename_i v'
          cases P2 with
          | cons _ _ => simp at hPlen
          | nil =>
            have huc : u ≠ c := G.ne_of_adj h1
            have hvc : v ≠ c := (G.ne_of_adj h2).symm
            have huv : u ≠ v := by
              intro h; subst h; rw [SimpleGraph.dist_self] at hd2; omega
            have hall_adj : ∀ w : V, w ≠ c → G.Adj c w := by
              intro w hwc
              rw [← SimpleGraph.dist_eq_one_iff_adj]
              have hle := hmax' c w
              have h0 : G.dist c w ≠ 0 := fun h => hwc ((isTree_dist_eq_zero_iff hG).mp h).symm
              by_contra hne1
              have hcw2 : G.dist c w = 2 := by omega
              obtain ⟨Q, hQ, hQlen⟩ := (hG.connected c w).exists_path_of_dist
              rw [hcw2] at hQlen
              cases Q with
              | nil => simp at hQlen
              | cons hq1 Q1 =>
                rename_i x
                cases Q1 with
                | nil => simp at hQlen
                | cons hq2 Q2 =>
                  cases Q2 with
                  | cons _ _ => simp at hQlen
                  | nil =>
                    have hxc : x ≠ c := (G.ne_of_adj hq1).symm
                    have hxw : x ≠ w := G.ne_of_adj hq2
                    have huw : u ≠ w := by
                      intro h; subst h
                      have : G.dist c u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h1.symm
                      omega
                    have hvw : v ≠ w := by
                      intro h; subst h
                      have : G.dist c v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h2
                      omega
                    by_cases hxu : x = u
                    · have hxv : x ≠ v := by rwa [hxu]
                      have hv_not : v ∉ (Walk.cons hq1 (Walk.cons hq2 Walk.nil)).support := by
                        simp [hvc, hxv.symm, hvw]
                      have hpath3 : (Walk.cons h2.symm (Walk.cons hq1 (Walk.cons hq2 Walk.nil))).IsPath :=
                        Walk.IsPath.cons hQ hv_not
                      have h3 := isTree_path_length_eq_dist hG _ hpath3
                      have hle3 := hmax' v w
                      simp at h3
                      omega
                    · have hu_not : u ∉ (Walk.cons hq1 (Walk.cons hq2 Walk.nil)).support := by
                        simp [huc, Ne.symm hxu, huw]
                      have hpath3 : (Walk.cons h1 (Walk.cons hq1 (Walk.cons hq2 Walk.nil))).IsPath :=
                        Walk.IsPath.cons hQ hu_not
                      have h3 := isTree_path_length_eq_dist hG _ hpath3
                      have hle3 := hmax' u w
                      simp at h3
                      omega
            apply hnotstar c
            ext x y
            simp only [starGraph, SimpleGraph.fromRel_adj]
            constructor
            · intro hxy
              refine ⟨G.ne_of_adj hxy, ?_⟩
              by_contra hne
              have hxc : x ≠ c := fun h => hne (Or.inl h)
              have hyc : y ≠ c := fun h => hne (Or.inr h)
              have hcx := hall_adj x hxc
              have hcy := hall_adj y hyc
              have hp1 : (Walk.cons hxy Walk.nil).IsPath :=
                Walk.IsPath.cons Walk.IsPath.nil (by simp [G.ne_of_adj hxy])
              have hp2 : (Walk.cons hcx.symm (Walk.cons hcy Walk.nil)).IsPath :=
                Walk.IsPath.cons (Walk.IsPath.cons Walk.IsPath.nil (by simp [hyc.symm]))
                  (by simp [hxc, G.ne_of_adj hxy])
              obtain ⟨r, _, huniq⟩ := hG.existsUnique_path x y
              have hlen := congrArg Walk.length ((huniq _ hp1).trans (huniq _ hp2).symm)
              simp at hlen
            · rintro ⟨hxy, rfl | rfl⟩
              · exact hall_adj y hxy.symm
              · exact (hall_adj x hxy).symm
  cases P with
  | nil => simp [SimpleGraph.dist_self] at hge3
  | cons hadj1 P1 =>
    rename_i p₁
    have hrev_path : (Walk.cons hadj1 P1).reverse.IsPath := hP.reverse
    have hrev_len : (Walk.cons hadj1 P1).reverse.length = G.dist u v := by
      rw [Walk.length_reverse, hPlen]
    have hmax_rev : ∀ x y : V, G.dist x y ≤ G.dist v u := by
      intro x y
      have := hmax' x y
      rwa [SimpleGraph.dist_comm (u := u) (v := v)] at this
    generalize hR : (Walk.cons hadj1 P1).reverse = R at hrev_path hrev_len
    cases R with
    | nil => simp only [Walk.length_nil] at hrev_len; omega
    | cons hadj2 R1 =>
      rename_i p₂
      have hleaf1 : ∀ w : V, G.Adj u w ↔ w = p₁ :=
        isTree_max_dist_endpoint_isLeaf hG hmax' hadj1 hP
      have hleaf2 : ∀ w : V, G.Adj v w ↔ w = p₂ :=
        isTree_max_dist_endpoint_isLeaf hG hmax_rev hadj2 hrev_path
      have hdu_p1 : G.dist u p₁ = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj1
      have hR1_path : R1.reverse.IsPath := hrev_path.of_cons.reverse
      have hdu_p2 : G.dist u p₂ = G.dist u v - 1 := by
        have hlen := isTree_path_length_eq_dist hG R1.reverse hR1_path
        rw [Walk.length_reverse] at hlen
        simp only [Walk.length_cons] at hrev_len
        omega
      have hdu_u : G.dist u u = 0 := SimpleGraph.dist_self
      have h_uv : u ≠ v := by intro h; subst h; omega
      have h_up1 : u ≠ p₁ := by intro h; subst h; omega
      have h_up2 : u ≠ p₂ := by intro h; subst h; omega
      have h_vp1 : v ≠ p₁ := by intro h; subst h; omega
      have h_vp2 : v ≠ p₂ := by intro h; subst h; omega
      have h_p1p2 : p₁ ≠ p₂ := by intro h; subst h; omega
      have hcard4 : 4 ≤ Fintype.card V := by
        have hsub : ({u, v, p₁, p₂} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
        have h4 : ({u, v, p₁, p₂} : Finset V).card = 4 := by
          simp [h_uv, h_up1, h_up2, h_vp1, h_vp2, h_p1p2]
        have hle := Finset.card_le_card hsub
        rw [h4, Finset.card_univ] at hle
        exact hle
      exact ⟨hcard4, u, v, p₁, p₂, h_uv, h_up1, h_up2, h_vp1, h_vp2, h_p1p2, hleaf1, hleaf2⟩

private lemma walk_induce_of_not_mem {V : Type*} {G : SimpleGraph V} {S : Set V}
    {u v : V} (p : G.Walk u v) (hp : ∀ z ∈ p.support, z ∈ S) :
    (G.induce S).Reachable ⟨u, hp u (Walk.start_mem_support p)⟩
      ⟨v, hp v (Walk.end_mem_support p)⟩ := by
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj p' ih =>
    rename_i a b c
    have ha : a ∈ S := hp a (by simp)
    have hb : b ∈ S := hp b (by simp)
    have hp' : ∀ z ∈ p'.support, z ∈ S := fun z hz => hp z (by simp [hz])
    exact Reachable.trans (Adj.reachable (show (G.induce S).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hadj)) (ih hp')

private lemma isTree_induce_erase_leaf {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsTree) {ℓ p : V} (hne : ℓ ≠ p) (hleaf : ∀ w : V, G.Adj ℓ w ↔ w = p) :
    (G.induce {x : V | x ≠ ℓ}).IsTree := by
  have : Nonempty {x : V | x ≠ ℓ} := ⟨⟨p, hne.symm⟩⟩
  refine ⟨SimpleGraph.Connected.mk ?_, ?_⟩
  · rintro ⟨xv, hxv⟩ ⟨yv, hyv⟩
    obtain ⟨P, hP, _⟩ := (hG.connected xv yv).exists_path_of_dist
    have hnot : ∀ z ∈ P.support, z ≠ ℓ := by
      intro z hz hzl
      subst z
      let P₁ := P.takeUntil ℓ hz
      let P₂ := P.dropUntil ℓ hz
      have hP12 : P₁.append P₂ = P := Walk.take_spec P hz
      generalize hR1 : P₁.reverse = R1
      cases R1 with
      | nil => exact hxv rfl
      | cons hadj1 Q1 =>
        rename_i a
        generalize hP2eq : P₂ = P2
        cases P2 with
        | nil => exact hyv rfl
        | cons hadj2 Q2 =>
          rename_i b
          have ha : a = p := (hleaf a).mp hadj1
          have hb : b = p := (hleaf b).mp hadj2
          subst a; subst b
          have hnd : P.support.Nodup := hP.support_nodup
          rw [← hP12, Walk.support_append] at hnd
          have hp1 : p ∈ P₁.support := by
            have hmem_rev : p ∈ P₁.reverse.support := by rw [hR1]; simp
            rw [Walk.support_reverse] at hmem_rev
            exact List.mem_reverse.mp hmem_rev
          have hp2 : p ∈ P₂.support.tail := by
            rw [hP2eq]
            simp [Walk.support_cons]
          exact (List.nodup_append.mp hnd).2.2 p hp1 p hp2 rfl
    exact walk_induce_of_not_mem P hnot
  · intro u c hc
    have hmap := hc.map (f := (SimpleGraph.Embedding.induce (G := G) {x : V | x ≠ ℓ}).toHom)
      (SimpleGraph.Embedding.induce (G := G) {x : V | x ≠ ℓ}).injective
    exact hG.isAcyclic _ hmap

private lemma isTree_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.IsTree) (e : G ≃g H) : H.IsTree := by
  have : Nonempty W := ⟨e hG.connected.nonempty.some⟩
  refine ⟨SimpleGraph.Connected.mk ?_, ?_⟩
  · intro x y
    obtain ⟨p⟩ := hG.connected (e.symm x) (e.symm y)
    have hp : H.Reachable (e (e.symm x)) (e (e.symm y)) := (p.map e.toHom).reachable
    simpa using hp
  · intro u c hc
    have hmap := hc.map (f := e.symm.toHom) e.symm.injective
    exact hG.isAcyclic _ hmap

private lemma isTree_comap_equiv {V W : Type*} {G : SimpleGraph V} (hG : G.IsTree) (e : W ≃ V) :
    (G.comap e).IsTree := by
  have iso : G ≃g G.comap e :=
    { toEquiv := e.symm
      map_rel_iff' := by intro a b; simp [SimpleGraph.comap_adj] }
  exact isTree_of_iso hG iso

private lemma card_fin_ne {k : ℕ} (c : Fin k) : Fintype.card {x : Fin k // x ≠ c} = k - 1 := by
  have hset : {x : Fin k // x ≠ c} ≃ {x : Fin k // x ∈ Finset.univ.erase c} :=
    { toFun := fun x => ⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩
      invFun := fun x => ⟨x.1, (Finset.mem_erase.mp x.2).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr hset, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]

private lemma star_embed_into_finset {k n : ℕ} (c : Fin k) (center : Fin n)
    (leaves : Finset (Fin n)) (hnotmem : center ∉ leaves) (hcard : leaves.card + 1 = k) :
    ∃ f : Fin k → Fin n, Function.Injective f ∧ f c = center ∧
      ∀ u v : Fin n, ((starGraph c).map f).Adj u v ↔
        (u = center ∧ v ∈ leaves) ∨ (v = center ∧ u ∈ leaves) := by
  have h1 : Fintype.card {x : Fin k // x ≠ c} = Fintype.card {y : Fin n // y ∈ leaves} := by
    rw [card_fin_ne, Fintype.card_coe]
    omega
  let e : {x : Fin k // x ≠ c} ≃ {y : Fin n // y ∈ leaves} := Fintype.equivOfCardEq h1
  let f : Fin k → Fin n := fun x =>
    if hx : x = c then center else (e ⟨x, hx⟩).1
  have hfc : f c = center := by simp [f]
  have hfinj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = c <;> by_cases hy : y = c
    · exact hx.trans hy.symm
    · simp only [f, hx, hy, dite_true, dite_false] at hxy
      exact absurd (hxy ▸ (e ⟨y, hy⟩).2) hnotmem
    · simp only [f, hx, hy, dite_true, dite_false] at hxy
      exact absurd (hxy.symm ▸ (e ⟨x, hx⟩).2) hnotmem
    · simp only [f, hx, hy, dite_false] at hxy
      have := e.injective (Subtype.ext hxy)
      exact congrArg Subtype.val this
  refine ⟨f, hfinj, hfc, fun u v => ?_⟩
  constructor
  · rintro ⟨huv, a, b, hab, rfl, rfl⟩
    have hab' : a ≠ b ∧ (a = c ∨ b = c) := by
      simpa [starGraph, SimpleGraph.fromRel_adj] using hab
    rcases hab' with ⟨hne, rfl | rfl⟩
    · left
      refine ⟨hfc, ?_⟩
      simp only [f, hne.symm, dite_false]
      exact (e ⟨b, hne.symm⟩).2
    · right
      refine ⟨hfc, ?_⟩
      simp only [f, hne, dite_false]
      exact (e ⟨a, hne⟩).2
  · rintro (⟨rfl, hv⟩ | ⟨rfl, hu⟩)
    · let a := (e.symm ⟨v, hv⟩).1
      have ha : a ≠ c := (e.symm ⟨v, hv⟩).2
      have hfa : f a = v := by
        simp only [f, ha, dite_false]
        exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)
      refine ⟨fun h => hnotmem (h ▸ hv), c, a, ?_, hfc, hfa⟩
      simp [starGraph, SimpleGraph.fromRel_adj, ha.symm]
    · let a := (e.symm ⟨u, hu⟩).1
      have ha : a ≠ c := (e.symm ⟨u, hu⟩).2
      have hfa : f a = u := by
        simp only [f, ha, dite_false]
        exact congrArg Subtype.val (e.apply_symm_apply ⟨u, hu⟩)
      refine ⟨fun h => hnotmem (h.symm ▸ hu), a, c, ?_, hfa, hfc⟩
      simp [starGraph, SimpleGraph.fromRel_adj, ha]

private lemma map_comp_adj {V W U : Type*} {G : SimpleGraph V} {f : V → W} {g : W → U}
    (hg : Function.Injective g) (u v : U) :
    (G.map (g ∘ f)).Adj u v ↔ ∃ u' v', (G.map f).Adj u' v' ∧ g u' = u ∧ g v' = v := by
  constructor
  · rintro ⟨huv, a, b, hab, rfl, rfl⟩
    refine ⟨f a, f b, ⟨fun h => huv (congrArg g h), a, b, hab, rfl, rfl⟩, rfl, rfl⟩
  · rintro ⟨u', v', ⟨huv', a, b, hab, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨fun h => huv' (hg h), a, b, hab, rfl, rfl⟩

private lemma isTree_induce_erase_two_leaves {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsTree)
    {ℓ₁ ℓ₂ p₁ p₂ : V} (h12 : ℓ₁ ≠ ℓ₂) (h1p1 : ℓ₁ ≠ p₁) (h2p2 : ℓ₂ ≠ p₂) (h1p2 : ℓ₁ ≠ p₂)
    (hleaf1 : ∀ w : V, G.Adj ℓ₁ w ↔ w = p₁) (hleaf2 : ∀ w : V, G.Adj ℓ₂ w ↔ w = p₂) :
    (G.induce {x : V | x ≠ ℓ₁ ∧ x ≠ ℓ₂}).IsTree := by
  have hG1 : (G.induce {x : V | x ≠ ℓ₁}).IsTree := isTree_induce_erase_leaf hG h1p1 hleaf1
  have hleaf2' : ∀ w : {x : V | x ≠ ℓ₁}, (G.induce {x : V | x ≠ ℓ₁}).Adj ⟨ℓ₂, h12.symm⟩ w ↔
      w = ⟨p₂, h1p2.symm⟩ := by
    intro w
    change G.Adj ℓ₂ w.1 ↔ w = ⟨p₂, h1p2.symm⟩
    rw [hleaf2]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hne' : (⟨ℓ₂, h12.symm⟩ : {x : V | x ≠ ℓ₁}) ≠ ⟨p₂, h1p2.symm⟩ := fun h =>
    h2p2 (congrArg Subtype.val h)
  have hG2 := isTree_induce_erase_leaf hG1 hne' hleaf2'
  let e : {y : {x : V | x ≠ ℓ₁} | y ≠ ⟨ℓ₂, h12.symm⟩} ≃ {x : V | x ≠ ℓ₁ ∧ x ≠ ℓ₂} :=
    { toFun := fun z => ⟨z.1.1, z.1.2, fun h => z.2 (Subtype.ext h)⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, fun h => x.2.2 (congrArg Subtype.val h)⟩
      left_inv := fun z => by ext; rfl
      right_inv := fun x => by ext; rfl }
  have iso : ((G.induce {x : V | x ≠ ℓ₁}).induce {y | y ≠ ⟨ℓ₂, h12.symm⟩}) ≃g
      (G.induce {x : V | x ≠ ℓ₁ ∧ x ≠ ℓ₂}) :=
    { toEquiv := e
      map_rel_iff' := by intro a b; rfl }
  exact isTree_of_iso hG2 iso

private lemma extend_one_leaf {m : ℕ} {G : SimpleGraph (Fin (m + 1))}
    {ℓ p : Fin (m + 1)} (hne : ℓ ≠ p) (hleaf : ∀ w, G.Adj ℓ w ↔ w = p)
    (e : {x : Fin (m + 1) // x ≠ ℓ} ≃ Fin m)
    {g : Fin m → Fin m} (hg : Function.Injective g) :
    ∃ f : Fin (m + 1) → Fin (m + 1), Function.Injective f ∧
      ∀ u v : Fin (m + 1), (G.map f).Adj u v →
        (∃ u' v' : Fin m, (((G.induce {x | x ≠ ℓ}).comap e.symm).map g).Adj u' v' ∧
          u = Fin.castSucc u' ∧ v = Fin.castSucc v') ∨
        (u = Fin.last m ∧ v = Fin.castSucc (g (e ⟨p, hne.symm⟩))) ∨
        (v = Fin.last m ∧ u = Fin.castSucc (g (e ⟨p, hne.symm⟩))) := by
  let f : Fin (m + 1) → Fin (m + 1) := fun x =>
    if hx : x = ℓ then Fin.last m else Fin.castSucc (g (e ⟨x, hx⟩))
  have hfinj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = ℓ <;> by_cases hy : y = ℓ
    · exact hx.trans hy.symm
    · simp only [f, hx, hy, dite_true, dite_false] at hxy
      exact absurd hxy.symm (Fin.castSucc_ne_last _)
    · simp only [f, hx, hy, dite_true, dite_false] at hxy
      exact absurd hxy (Fin.castSucc_ne_last _)
    · simp only [f, hx, hy, dite_false] at hxy
      have := e.injective (hg (Fin.castSucc_injective m hxy))
      exact congrArg Subtype.val this
  refine ⟨f, hfinj, fun u v hadj => ?_⟩
  rcases hadj with ⟨huv, a, b, hab, rfl, rfl⟩
  by_cases ha : a = ℓ
  · subst ha
    have hbp : b = p := (hleaf b).mp hab
    subst hbp
    right; left
    simp [f, hne.symm]
  · by_cases hb : b = ℓ
    · subst hb
      have hap : a = p := (hleaf a).mp hab.symm
      subst hap
      right; right
      simp [f, hne.symm]
    · left
      refine ⟨g (e ⟨a, ha⟩), g (e ⟨b, hb⟩), ?_, by simp [f, ha], by simp [f, hb]⟩
      refine ⟨fun h => huv (by simp [f, ha, hb, h]), e ⟨a, ha⟩, e ⟨b, hb⟩, ?_, rfl, rfl⟩
      simp only [SimpleGraph.comap_adj, Equiv.symm_apply_apply]
      exact hab

private lemma extend_two_leaves {k n : ℕ} (_hk : 4 ≤ k) (_hkn : k ≤ n)
    {G : SimpleGraph (Fin k)} {ℓ₁ ℓ₂ p₁ p₂ : Fin k}
    (h12 : ℓ₁ ≠ ℓ₂) (h1p1 : ℓ₁ ≠ p₁) (h1p2 : ℓ₁ ≠ p₂) (h2p1 : ℓ₂ ≠ p₁) (h2p2 : ℓ₂ ≠ p₂)
    (hleaf1 : ∀ w, G.Adj ℓ₁ w ↔ w = p₁) (hleaf2 : ∀ w, G.Adj ℓ₂ w ↔ w = p₂)
    (e : {x : Fin k // x ≠ ℓ₁ ∧ x ≠ ℓ₂} ≃ Fin (k - 2))
    {g : Fin (k - 2) → Fin (n - 2)} (hg : Function.Injective g)
    {u₀ v₀ : Fin n} (huv₀ : u₀ ≠ v₀) (hu₀ : n - 2 ≤ u₀.val) (hv₀ : n - 2 ≤ v₀.val) :
    ∃ f : Fin k → Fin n, Function.Injective f ∧
      ∀ u v : Fin n, (G.map f).Adj u v →
        (∃ u' v' : Fin (n - 2),
          (((G.induce {x | x ≠ ℓ₁ ∧ x ≠ ℓ₂}).comap e.symm).map g).Adj u' v' ∧
          u = Fin.castLE (by omega) u' ∧ v = Fin.castLE (by omega) v') ∨
        (u = u₀ ∧ v = Fin.castLE (by omega) (g (e ⟨p₁, h1p1.symm, h2p1.symm⟩))) ∨
        (v = u₀ ∧ u = Fin.castLE (by omega) (g (e ⟨p₁, h1p1.symm, h2p1.symm⟩))) ∨
        (u = v₀ ∧ v = Fin.castLE (by omega) (g (e ⟨p₂, h1p2.symm, h2p2.symm⟩))) ∨
        (v = v₀ ∧ u = Fin.castLE (by omega) (g (e ⟨p₂, h1p2.symm, h2p2.symm⟩))) := by
  let castN : Fin (n - 2) → Fin n := Fin.castLE (by omega)
  have hcastN_inj : Function.Injective castN := Fin.castLE_injective _
  let f : Fin k → Fin n := fun x =>
    if hx1 : x = ℓ₁ then u₀
    else if hx2 : x = ℓ₂ then v₀
    else castN (g (e ⟨x, hx1, hx2⟩))
  have hfinj : Function.Injective f := by
    intro x y hxy
    by_cases hx1 : x = ℓ₁ <;> by_cases hy1 : y = ℓ₁
    · exact hx1.trans hy1.symm
    · by_cases hy2 : y = ℓ₂
      · dsimp only [f] at hxy
        rw [dif_pos hx1, dif_neg hy1, dif_pos hy2] at hxy
        exact absurd hxy huv₀
      · dsimp only [f] at hxy
        rw [dif_pos hx1, dif_neg hy1, dif_neg hy2] at hxy
        have hval := congrArg Fin.val hxy
        have hlt : (g (e ⟨y, hy1, hy2⟩)).val < n - 2 := (g (e ⟨y, hy1, hy2⟩)).isLt
        dsimp only [castN, Fin.val_castLE] at hval
        omega
    · by_cases hx2 : x = ℓ₂
      · dsimp only [f] at hxy
        rw [dif_neg hx1, dif_pos hx2, dif_pos hy1] at hxy
        exact absurd hxy.symm huv₀
      · dsimp only [f] at hxy
        rw [dif_neg hx1, dif_neg hx2, dif_pos hy1] at hxy
        have hval := congrArg Fin.val hxy
        have hlt : (g (e ⟨x, hx1, hx2⟩)).val < n - 2 := (g (e ⟨x, hx1, hx2⟩)).isLt
        dsimp only [castN, Fin.val_castLE] at hval
        omega
    · by_cases hx2 : x = ℓ₂ <;> by_cases hy2 : y = ℓ₂
      · exact hx2.trans hy2.symm
      · dsimp only [f] at hxy
        rw [dif_neg hx1, dif_pos hx2, dif_neg hy1, dif_neg hy2] at hxy
        have hval := congrArg Fin.val hxy
        have hlt : (g (e ⟨y, hy1, hy2⟩)).val < n - 2 := (g (e ⟨y, hy1, hy2⟩)).isLt
        dsimp only [castN, Fin.val_castLE] at hval
        omega
      · dsimp only [f] at hxy
        rw [dif_neg hx1, dif_neg hx2, dif_neg hy1, dif_pos hy2] at hxy
        have hval := congrArg Fin.val hxy
        have hlt : (g (e ⟨x, hx1, hx2⟩)).val < n - 2 := (g (e ⟨x, hx1, hx2⟩)).isLt
        dsimp only [castN, Fin.val_castLE] at hval
        omega
      · dsimp only [f] at hxy
        rw [dif_neg hx1, dif_neg hx2, dif_neg hy1, dif_neg hy2] at hxy
        have := e.injective (hg (hcastN_inj hxy))
        exact congrArg Subtype.val this
  refine ⟨f, hfinj, fun u v hadj => ?_⟩
  rcases hadj with ⟨huv, a, b, hab, rfl, rfl⟩
  by_cases ha1 : a = ℓ₁
  · subst ha1
    have hbp : b = p₁ := (hleaf1 b).mp hab
    subst hbp
    right; left
    simp [f, h1p1.symm, h2p1.symm, castN]
  · by_cases hb1 : b = ℓ₁
    · subst hb1
      have hap : a = p₁ := (hleaf1 a).mp hab.symm
      subst hap
      right; right; left
      simp [f, h1p1.symm, h2p1.symm, castN]
    · by_cases ha2 : a = ℓ₂
      · subst ha2
        have hbp : b = p₂ := (hleaf2 b).mp hab
        subst hbp
        right; right; right; left
        simp [f, h12.symm, h1p2.symm, h2p2.symm, castN]
      · by_cases hb2 : b = ℓ₂
        · subst hb2
          have hap : a = p₂ := (hleaf2 a).mp hab.symm
          subst hap
          right; right; right; right
          simp [f, h12.symm, h1p2.symm, h2p2.symm, castN]
        · left
          refine ⟨g (e ⟨a, ha1, ha2⟩), g (e ⟨b, hb1, hb2⟩), ?_,
            by simp [f, ha1, ha2, castN], by simp [f, hb1, hb2, castN]⟩
          refine ⟨fun h => huv (by simp [f, ha1, ha2, hb1, hb2, h]),
            e ⟨a, ha1, ha2⟩, e ⟨b, hb1, hb2⟩, ?_, rfl, rfl⟩
          simp only [SimpleGraph.comap_adj, Equiv.symm_apply_apply]
          exact hab

private lemma pack_case_A {n : ℕ} (hn3 : 3 ≤ n) {T : (k : ℕ) → SimpleGraph (Fin k)}
    {cn : Fin n} (hTn : T n = starGraph cn)
    (hprev : Erdos743.IsPacking (n - 1) (Set.Icc 2 (n - 1)) T) :
    Erdos743.IsPacking n (Set.Icc 2 n) T := by
  obtain ⟨f', hf'_inj, hf'_disj⟩ := hprev
  let lastV : Fin n := ⟨n - 1, by omega⟩
  let leaves : Finset (Fin n) := Finset.univ.erase lastV
  have hleaves_card : leaves.card + 1 = n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨fn, hfn_inj, _, hfn_adj⟩ :=
    star_embed_into_finset cn lastV leaves (Finset.notMem_erase _ _) hleaves_card
  let castPrev : Fin (n - 1) → Fin n := Fin.castLE (by omega)
  have hcastPrev_inj : Function.Injective castPrev := Fin.castLE_injective _
  let f : (k : Set.Icc 2 n) → Fin k → Fin n := fun k =>
    if hk : (k : ℕ) = n then
      fun x => fn (x.cast hk)
    else
      fun x => castPrev (f' ⟨k.1, ⟨k.2.1, by have := k.2.2; omega⟩⟩ x)
  refine ⟨f, ?_, ?_⟩
  · intro k
    by_cases hk : (k : ℕ) = n
    · rcases k with ⟨kv, hkm⟩
      dsimp only at hk; subst kv
      have hfk : f ⟨n, hkm⟩ = fn := by funext x; simp [f]
      rw [hfk]; exact hfn_inj
    · have hfk : f k = castPrev ∘ f' ⟨k.1, ⟨k.2.1, by have := k.2.2; omega⟩⟩ := by
        funext x; simp [f, hk]
      rw [hfk]; exact hcastPrev_inj.comp (hf'_inj _)
  · intro k l hkl
    by_cases hl : (l : ℕ) = n
    · have hk : (k : ℕ) ≠ n := by omega
      rcases l with ⟨lv, hlm⟩
      dsimp only at hl; subst lv
      have hfl : f ⟨n, hlm⟩ = fn := by funext x; simp [f]
      have hfk : f k = castPrev ∘ f' ⟨k.1, ⟨k.2.1, by have := k.2.2; omega⟩⟩ := by
        funext x; simp [f, hk]
      rw [hfk, hfl, hTn]
      apply disjoint_edgeSet_of_adj
      intro u v hadjk hadjl
      rw [map_comp_adj hcastPrev_inj] at hadjk
      rcases hadjk with ⟨u', v', _, rfl, rfl⟩
      rw [hfn_adj] at hadjl
      rcases hadjl with ⟨hu, _⟩ | ⟨hv, _⟩
      · have := congrArg Fin.val hu; dsimp [castPrev, lastV] at this; omega
      · have := congrArg Fin.val hv; dsimp [castPrev, lastV] at this; omega
    · have hk : (k : ℕ) ≠ n := by have := l.2.2; omega
      have hfk : f k = castPrev ∘ f' ⟨k.1, ⟨k.2.1, by have := k.2.2; omega⟩⟩ := by
        funext x; simp [f, hk]
      have hfl : f l = castPrev ∘ f' ⟨l.1, ⟨l.2.1, by have := l.2.2; omega⟩⟩ := by
        funext x; simp [f, hl]
      rw [hfk, hfl]
      apply disjoint_edgeSet_of_adj
      intro u v hadjk hadjl
      rw [map_comp_adj hcastPrev_inj] at hadjk hadjl
      rcases hadjk with ⟨u₁, v₁, h1, hu1, hv1⟩
      rcases hadjl with ⟨u₂, v₂, h2, hu2, hv2⟩
      have hu : u₁ = u₂ := hcastPrev_inj (hu1.trans hu2.symm)
      have hv : v₁ = v₂ := hcastPrev_inj (hv1.trans hv2.symm)
      subst hu; subst hv
      have hdisj := hf'_disj ⟨k.1, ⟨k.2.1, by have := k.2.2; omega⟩⟩
        ⟨l.1, ⟨l.2.1, by have := l.2.2; omega⟩⟩ hkl
      exact Set.disjoint_left.mp hdisj (show s(u₁, v₁) ∈ _ from h1)
        (show s(u₁, v₁) ∈ _ from h2)

private lemma pack_case_B {n : ℕ} (hn3 : 3 ≤ n) {T : (k : ℕ) → SimpleGraph (Fin k)}
    (hT : ∀ k ∈ Set.Icc 2 n, (T k).IsTree)
    {cn1 : Fin (n - 1)} (hTn1 : T (n - 1) = starGraph cn1)
    {a' : ℕ} (ha' : ∀ k ∈ Set.Icc 2 (n - 1), k ≠ a' → ∃ c : Fin k, T k = starGraph c)
    (ih : ∀ T' : (k : ℕ) → SimpleGraph (Fin k),
      (∀ k ∈ Set.Icc 2 (n - 1), (T' k).IsTree) →
      (∃ a₁ b₁ : ℕ, ∀ k ∈ Set.Icc 2 (n - 1), k ≠ a₁ → k ≠ b₁ → ∃ c : Fin k, T' k = starGraph c) →
      Erdos743.IsPacking (n - 1) (Set.Icc 2 (n - 1)) T') :
    Erdos743.IsPacking n (Set.Icc 2 n) T := by
  have hTn_tree : (T n).IsTree := hT n ⟨by omega, le_refl _⟩
  obtain ⟨ℓ, p, hne, hleaf⟩ := isTree_exists_leaf hTn_tree (by simp; omega)
  have hcard_eq : Fintype.card {x : Fin n // x ≠ ℓ} = Fintype.card (Fin (n - 1)) := by
    rw [card_fin_ne, Fintype.card_fin]
  let e : {x : Fin n // x ≠ ℓ} ≃ Fin (n - 1) := Fintype.equivOfCardEq hcard_eq
  let Tn' : SimpleGraph (Fin (n - 1)) := ((T n).induce {x | x ≠ ℓ}).comap e.symm
  have hTn'_tree : Tn'.IsTree :=
    isTree_comap_equiv (isTree_induce_erase_leaf hTn_tree hne hleaf) e.symm
  let T' : (k : ℕ) → SimpleGraph (Fin k) := fun k =>
    if hk : k = n - 1 then
      Tn'.comap (Fin.cast hk)
    else T k
  have hT'_tree : ∀ k ∈ Set.Icc 2 (n - 1), (T' k).IsTree := by
    intro k hk
    by_cases hkn1 : k = n - 1
    · simp only [T', hkn1, dite_true]
      exact isTree_comap_equiv hTn'_tree (finCongr hkn1)
    · simp only [T', hkn1, dite_false]
      exact hT k ⟨hk.1, by have := hk.2; omega⟩
  have hT'_star : ∃ a₁ b₁ : ℕ, ∀ k ∈ Set.Icc 2 (n - 1), k ≠ a₁ → k ≠ b₁ →
      ∃ c : Fin k, T' k = starGraph c := by
    refine ⟨a', n - 1, fun k hk hka hkn1 => ?_⟩
    simp only [T', hkn1, dite_false]
    exact ha' k hk hka
  obtain ⟨f', hf'_inj, hf'_disj⟩ := ih T' hT'_tree hT'_star
  have hm_eq : n - 1 + 1 = n := by omega
  let e_n : Fin (n - 1 + 1) ≃ Fin n := finCongr hm_eq
  let G_m : SimpleGraph (Fin (n - 1 + 1)) := (T n).comap e_n
  have hleaf_m : ∀ w : Fin (n - 1 + 1), G_m.Adj (e_n.symm ℓ) w ↔ w = e_n.symm p := by
    intro w
    simp only [G_m, SimpleGraph.comap_adj, Equiv.apply_symm_apply, hleaf]
    exact ⟨fun h => e_n.injective (by simpa using h), fun h => by rw [h]; simp⟩
  have hne_m : e_n.symm ℓ ≠ e_n.symm p := fun h => hne (e_n.symm.injective h)
  let e_sub : {x : Fin (n - 1 + 1) // x ≠ e_n.symm ℓ} ≃ Fin (n - 1) :=
    { toFun := fun x => e ⟨e_n x.1, fun h => x.2 (e_n.injective (by simpa using h))⟩
      invFun := fun y => ⟨e_n.symm (e.symm y).1, fun h => (e.symm y).2 (e_n.symm.injective h)⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by simp }
  let gn1 : Fin (n - 1) → Fin (n - 1) := f' ⟨n - 1, ⟨by omega, le_refl _⟩⟩
  have hgn1_inj : Function.Injective gn1 := hf'_inj ⟨n - 1, ⟨by omega, le_refl _⟩⟩
  obtain ⟨fm, hfm_inj, hfm_adj⟩ := extend_one_leaf hne_m hleaf_m e_sub hgn1_inj
  let fn : Fin n → Fin n := fun x => e_n (fm (e_n.symm x))
  have hfn_inj : Function.Injective fn := e_n.injective.comp (hfm_inj.comp e_n.symm.injective)
  let p_img : Fin (n - 1) := gn1 (e ⟨p, hne.symm⟩)
  let lastV : Fin n := e_n (Fin.last (n - 1))
  let castPrev : Fin (n - 1) → Fin n := fun y => e_n (Fin.castSucc y)
  have hcastPrev_inj : Function.Injective castPrev := e_n.injective.comp (Fin.castSucc_injective _)
  have hcastPrev_ne_last : ∀ y : Fin (n - 1), castPrev y ≠ lastV := fun y h =>
    Fin.castSucc_ne_last y (e_n.injective h)
  let leaves : Finset (Fin n) := (Finset.univ.erase p_img).image castPrev
  have hlast_not_leaves : lastV ∉ leaves := by
    simp only [leaves, Finset.mem_image, not_exists, not_and]
    intro y _ hy
    exact hcastPrev_ne_last y hy
  have hleaves_card : leaves.card + 1 = n - 1 := by
    rw [Finset.card_image_of_injective _ hcastPrev_inj,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨fn1, hfn1_inj, _, hfn1_adj⟩ :=
    star_embed_into_finset cn1 lastV leaves hlast_not_leaves hleaves_card
  have hfn_adj : ∀ u v : Fin n, ((T n).map fn).Adj u v →
      (∃ u' v' : Fin (n - 1), ((T' (n - 1)).map gn1).Adj u' v' ∧
        u = castPrev u' ∧ v = castPrev v') ∨
      (u = lastV ∧ v = castPrev p_img) ∨ (v = lastV ∧ u = castPrev p_img) := by
    intro u v hadj
    have hadj_m : (G_m.map fm).Adj (e_n.symm u) (e_n.symm v) := by
      rcases hadj with ⟨huv, a, b, hab, rfl, rfl⟩
      refine ⟨fun h => huv (by simpa [fn] using congrArg e_n h),
        e_n.symm a, e_n.symm b, ?_, by simp [fn], by simp [fn]⟩
      simpa [G_m, SimpleGraph.comap_adj] using hab
    have hres := hfm_adj (e_n.symm u) (e_n.symm v) hadj_m
    have he_sub_p : e_sub ⟨e_n.symm p, hne_m.symm⟩ = e ⟨p, hne.symm⟩ := by simp [e_sub]
    rcases hres with ⟨u', v', hmid, hu', hv'⟩ | ⟨hu', hv'⟩ | ⟨hv', hu'⟩
    · left
      refine ⟨u', v', ?_, by simpa [castPrev] using congrArg e_n hu',
        by simpa [castPrev] using congrArg e_n hv'⟩
      rcases hmid with ⟨huv', a, b, hab, rfl, rfl⟩
      refine ⟨huv', a, b, ?_, rfl, rfl⟩
      simp only [T', dite_true, Tn', SimpleGraph.comap_adj]
      exact hab
    · right; left
      rw [he_sub_p] at hv'
      exact ⟨by simpa [lastV] using congrArg e_n hu',
        by simpa [castPrev, p_img] using congrArg e_n hv'⟩
    · right; right
      rw [he_sub_p] at hu'
      exact ⟨by simpa [lastV] using congrArg e_n hv',
        by simpa [castPrev, p_img] using congrArg e_n hu'⟩
  let f : (k : Set.Icc 2 n) → Fin k → Fin n := fun k =>
    if hk : (k : ℕ) = n then
      fun x => fn (x.cast hk)
    else if hk1 : (k : ℕ) = n - 1 then
      fun x => fn1 (x.cast hk1)
    else
      fun x => castPrev (f' ⟨k.1, ⟨k.2.1, by have := k.2.2; omega⟩⟩ x)
  refine ⟨f, ?_, ?_⟩
  · intro k
    by_cases hk : (k : ℕ) = n
    · rcases k with ⟨kv, hkm⟩; dsimp only at hk; subst kv
      have : f ⟨n, hkm⟩ = fn := by funext x; simp [f]
      rw [this]; exact hfn_inj
    · by_cases hk1 : (k : ℕ) = n - 1
      · rcases k with ⟨kv, hkm⟩; dsimp only at hk1; subst kv
        have : f ⟨n - 1, hkm⟩ = fn1 := by funext x; simp [f, hk]
        rw [this]; exact hfn1_inj
      · have : f k = castPrev ∘ f' ⟨k.1, ⟨k.2.1, by have := k.2.2; omega⟩⟩ := by
          funext x; simp [f, hk, hk1]
        rw [this]; exact hcastPrev_inj.comp (hf'_inj _)
  · intro k l hkl
    by_cases hl : (l : ℕ) = n
    · rcases l with ⟨lv, hlm⟩; dsimp only at hl; subst lv; dsimp only at hkl
      have hfl : f ⟨n, hlm⟩ = fn := by funext x; simp [f]
      by_cases hk1 : (k : ℕ) = n - 1
      · rcases k with ⟨kv, hkm⟩; dsimp only at hk1; subst kv
        have hne_n : n - 1 ≠ n := by omega
        have hfk : f ⟨n - 1, hkm⟩ = fn1 := by funext x; simp [f, hne_n]
        rw [hfk, hfl, hTn1]
        apply disjoint_edgeSet_of_adj
        intro u v hadjk hadjl
        rw [hfn1_adj] at hadjk
        have hres := hfn_adj u v hadjl
        rcases hadjk with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
        · simp only [leaves, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true] at hv
          rcases hv with ⟨y, hyp, rfl⟩
          rcases hres with ⟨u', v', _, hu', _⟩ | ⟨_, hv'⟩ | ⟨hv', _⟩
          · exact hcastPrev_ne_last u' hu'.symm
          · exact hyp (hcastPrev_inj hv')
          · exact hcastPrev_ne_last y hv'
        · simp only [leaves, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true] at hu
          rcases hu with ⟨y, hyp, rfl⟩
          rcases hres with ⟨u', v', _, _, hv'⟩ | ⟨hu', _⟩ | ⟨_, hu'⟩
          · exact hcastPrev_ne_last v' hv'.symm
          · exact hcastPrev_ne_last y hu'
          · exact hyp (hcastPrev_inj hu')
      · have hk : (k : ℕ) ≠ n := by omega
        have hfk : f k = castPrev ∘ f' ⟨k.1, ⟨k.2.1, by have := k.2.2; omega⟩⟩ := by
          funext x; simp [f, hk, hk1]
        rw [hfk, hfl]
        apply disjoint_edgeSet_of_adj
        intro u v hadjk hadjl
        rw [map_comp_adj hcastPrev_inj] at hadjk
        rcases hadjk with ⟨u₁, v₁, h1, rfl, rfl⟩
        have hres := hfn_adj _ _ hadjl
        rcases hres with ⟨u₂, v₂, h2, hu, hv⟩ | ⟨hu, _⟩ | ⟨hv, _⟩
        · have hu' : u₁ = u₂ := hcastPrev_inj hu
          have hv' : v₁ = v₂ := hcastPrev_inj hv
          subst hu'; subst hv'
          have hTk : T' k.1 = T k.1 := by simp [T', hk1]
          have hdisj := hf'_disj ⟨k.1, ⟨k.2.1, by have := k.2.2; omega⟩⟩
            ⟨n - 1, ⟨by omega, le_refl _⟩⟩ (show (k : ℕ) < n - 1 by have := k.2.2; omega)
          rw [hTk] at hdisj
          exact Set.disjoint_left.mp hdisj (show s(u₁, v₁) ∈ _ from h1)
            (show s(u₁, v₁) ∈ _ from h2)
        · exact hcastPrev_ne_last u₁ hu
        · exact hcastPrev_ne_last v₁ hv
    · by_cases hl1 : (l : ℕ) = n - 1
      · have hk : (k : ℕ) ≠ n := by omega
        have hk1 : (k : ℕ) ≠ n - 1 := by omega
        rcases l with ⟨lv, hlm⟩; dsimp only at hl1; subst lv
        have hfl : f ⟨n - 1, hlm⟩ = fn1 := by funext x; simp [f, hl]
        have hfk : f k = castPrev ∘ f' ⟨k.1, ⟨k.2.1, by have := k.2.2; omega⟩⟩ := by
          funext x; simp [f, hk, hk1]
        rw [hfk, hfl, hTn1]
        apply disjoint_edgeSet_of_adj
        intro u v hadjk hadjl
        rw [map_comp_adj hcastPrev_inj] at hadjk
        rcases hadjk with ⟨u₁, v₁, _, rfl, rfl⟩
        rw [hfn1_adj] at hadjl
        rcases hadjl with ⟨hu, _⟩ | ⟨hv, _⟩
        · exact hcastPrev_ne_last u₁ hu
        · exact hcastPrev_ne_last v₁ hv
      · have hk : (k : ℕ) ≠ n := by have := l.2.2; omega
        have hk1 : (k : ℕ) ≠ n - 1 := by have := l.2.2; omega
        have hfk : f k = castPrev ∘ f' ⟨k.1, ⟨k.2.1, by have := k.2.2; omega⟩⟩ := by
          funext x; simp [f, hk, hk1]
        have hfl : f l = castPrev ∘ f' ⟨l.1, ⟨l.2.1, by have := l.2.2; omega⟩⟩ := by
          funext x; simp [f, hl, hl1]
        rw [hfk, hfl]
        apply disjoint_edgeSet_of_adj
        intro u v hadjk hadjl
        rw [map_comp_adj hcastPrev_inj] at hadjk hadjl
        rcases hadjk with ⟨u₁, v₁, h1, hu1, hv1⟩
        rcases hadjl with ⟨u₂, v₂, h2, hu2, hv2⟩
        have hu : u₁ = u₂ := hcastPrev_inj (hu1.trans hu2.symm)
        have hv : v₁ = v₂ := hcastPrev_inj (hv1.trans hv2.symm)
        subst hu; subst hv
        have hTk : T' k.1 = T k.1 := by simp [T', hk1]
        have hTl : T' l.1 = T l.1 := by simp [T', hl1]
        have hdisj := hf'_disj ⟨k.1, ⟨k.2.1, by have := k.2.2; omega⟩⟩
          ⟨l.1, ⟨l.2.1, by have := l.2.2; omega⟩⟩ hkl
        rw [hTk, hTl] at hdisj
        exact Set.disjoint_left.mp hdisj (show s(u₁, v₁) ∈ _ from h1)
          (show s(u₁, v₁) ∈ _ from h2)

private lemma pack_case_C_assemble {n : ℕ} (hn5 : 5 ≤ n)
    {T T' : (k : ℕ) → SimpleGraph (Fin k)}
    (hTk_small : ∀ k : ℕ, k ≤ n - 4 → T' k = T k)
    {f' : (k : Set.Icc 2 (n - 2)) → Fin k → Fin (n - 2)}
    (hf'_inj : ∀ k, Function.Injective (f' k))
    (hf'_disj : ∀ k l : Set.Icc 2 (n - 2), (k : ℕ) < (l : ℕ) →
      Disjoint ((T' k).map (f' k)).edgeSet ((T' l).map (f' l)).edgeSet)
    {uV vV : Fin n} (huvV : uV ≠ vV)
    {castN : Fin (n - 2) → Fin n} (hcastN_inj : Function.Injective castN)
    (hcastN_ne_u : ∀ x, castN x ≠ uV) (hcastN_ne_v : ∀ x, castN x ≠ vV)
    {P₁ P₂ Qu Qv : Fin (n - 2)} (hQuP1 : Qu ≠ P₁) (hQvP2 : Qv ≠ P₂)
    {fn : Fin n → Fin n} (hfn_inj : Function.Injective fn)
    (hfn_adj' : ∀ u v : Fin n, ((T n).map fn).Adj u v →
      (∃ u' v' : Fin (n - 2), ((T' (n - 2)).map (f' ⟨n - 2, ⟨by omega, le_refl _⟩⟩)).Adj u' v' ∧
        u = castN u' ∧ v = castN v') ∨
      (u = uV ∧ v = castN P₁) ∨ (v = uV ∧ u = castN P₁) ∨
      (u = vV ∧ v = castN P₂) ∨ (v = vV ∧ u = castN P₂))
    {fn1 : Fin (n - 1) → Fin n} (hfn1_inj : Function.Injective fn1)
    (hfn1_adj : ∀ u v : Fin n, ((T (n - 1)).map fn1).Adj u v →
      (∃ u' v' : Fin (n - 2), ((T' (n - 3)).map (f' ⟨n - 3, ⟨by omega, by omega⟩⟩)).Adj u' v' ∧
        u = castN u' ∧ v = castN v') ∨
      (u = uV ∧ v = castN Qu) ∨ (v = uV ∧ u = castN Qu) ∨
      (u = vV ∧ v = castN Qv) ∨ (v = vV ∧ u = castN Qv))
    {fn2 : Fin (n - 2) → Fin n} (hfn2_inj : Function.Injective fn2)
    (hfn2_adj : ∀ u v : Fin n, ((T (n - 2)).map fn2).Adj u v ↔
      (u = uV ∧ v ∈ insert vV (((Finset.univ.erase P₁).erase Qu).image castN)) ∨
      (v = uV ∧ u ∈ insert vV (((Finset.univ.erase P₁).erase Qu).image castN)))
    {fn3 : Fin (n - 3) → Fin n} (hfn3_inj : Function.Injective fn3)
    (hfn3_adj : ∀ u v : Fin n, ((T (n - 3)).map fn3).Adj u v ↔
      (u = vV ∧ v ∈ ((Finset.univ.erase P₂).erase Qv).image castN) ∨
      (v = vV ∧ u ∈ ((Finset.univ.erase P₂).erase Qv).image castN)) :
    Erdos743.IsPacking n (Set.Icc 2 n) T := by
  let f : (k : Set.Icc 2 n) → Fin k → Fin n := fun k =>
    if hk0 : (k : ℕ) = n then fun x => fn (x.cast hk0)
    else if hk1 : (k : ℕ) = n - 1 then fun x => fn1 (x.cast hk1)
    else if hk2 : (k : ℕ) = n - 2 then fun x => fn2 (x.cast hk2)
    else if hk3 : (k : ℕ) = n - 3 then fun x => fn3 (x.cast hk3)
    else fun x => castN (f' ⟨k.1, ⟨k.2.1, by have := k.2.2; omega⟩⟩ x)
  have hsmall_eq : ∀ (k : Set.Icc 2 n) (hk : (k : ℕ) ≤ n - 4),
      f k = castN ∘ f' ⟨k.1, ⟨k.2.1, by omega⟩⟩ := by
    intro k hk
    have h0 : (k : ℕ) ≠ n := by omega
    have h1 : (k : ℕ) ≠ n - 1 := by omega
    have h2 : (k : ℕ) ≠ n - 2 := by omega
    have h3 : (k : ℕ) ≠ n - 3 := by omega
    funext x
    simp [f, h0, h1, h2, h3]
  refine ⟨f, ?_, ?_⟩
  · intro k
    by_cases hk0 : (k : ℕ) = n
    · rcases k with ⟨kv, hkm⟩; dsimp only at hk0; subst kv
      have : f ⟨n, hkm⟩ = fn := by funext x; simp [f]
      rw [this]; exact hfn_inj
    · by_cases hk1 : (k : ℕ) = n - 1
      · rcases k with ⟨kv, hkm⟩; dsimp only at hk1; subst kv
        have : f ⟨n - 1, hkm⟩ = fn1 := by funext x; simp [f, hk0]
        rw [this]; exact hfn1_inj
      · by_cases hk2 : (k : ℕ) = n - 2
        · rcases k with ⟨kv, hkm⟩; dsimp only at hk2; subst kv
          have : f ⟨n - 2, hkm⟩ = fn2 := by funext x; simp [f, hk0, hk1]
          rw [this]; exact hfn2_inj
        · by_cases hk3 : (k : ℕ) = n - 3
          · rcases k with ⟨kv, hkm⟩; dsimp only at hk3; subst kv
            have : f ⟨n - 3, hkm⟩ = fn3 := by funext x; simp [f, hk0, hk1, hk2]
            rw [this]; exact hfn3_inj
          · rw [hsmall_eq k (by have := k.2.2; omega)]
            exact hcastN_inj.comp (hf'_inj _)
  · intro k l hkl
    by_cases hl0 : (l : ℕ) = n
    · rcases l with ⟨lv, hlm⟩; dsimp only at hl0; subst lv; dsimp only at hkl
      have hfl : f ⟨n, hlm⟩ = fn := by funext x; simp [f]
      by_cases hk1 : (k : ℕ) = n - 1
      · rcases k with ⟨kv, hkm⟩; dsimp only at hk1; subst kv
        have hfk : f ⟨n - 1, hkm⟩ = fn1 := by funext x; simp [f, (show n - 1 ≠ n by omega)]
        rw [hfk, hfl]
        apply disjoint_edgeSet_of_adj
        intro u v hadjk hadjl
        rcases hfn1_adj u v hadjk with ⟨u₁, v₁, h1, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases hfn_adj' _ _ hadjl with ⟨u₂, v₂, h2, hu, hv⟩ | ⟨hu, _⟩ | ⟨hv, _⟩ | ⟨hu, _⟩ | ⟨hv, _⟩
          · have hu' := hcastN_inj hu; have hv' := hcastN_inj hv; subst hu'; subst hv'
            have hdisj := hf'_disj ⟨n - 3, ⟨by omega, by omega⟩⟩ ⟨n - 2, ⟨by omega, le_refl _⟩⟩
              (show n - 3 < n - 2 by omega)
            exact Set.disjoint_left.mp hdisj (show s(u₁, v₁) ∈ _ from h1) (show s(u₁, v₁) ∈ _ from h2)
          · exact hcastN_ne_u u₁ hu
          · exact hcastN_ne_u v₁ hv
          · exact hcastN_ne_v u₁ hu
          · exact hcastN_ne_v v₁ hv
        · rcases hfn_adj' _ _ hadjl with ⟨u₂, _, _, hu, _⟩ | ⟨_, hv⟩ | ⟨hv, _⟩ | ⟨hu, _⟩ | ⟨_, hu⟩
          · exact hcastN_ne_u u₂ hu.symm
          · exact hQuP1 (hcastN_inj hv)
          · exact hcastN_ne_u Qu hv
          · exact huvV hu
          · exact hcastN_ne_u P₂ hu.symm
        · rcases hfn_adj' _ _ hadjl with ⟨_, v₂, _, _, hv⟩ | ⟨hu, _⟩ | ⟨_, hu⟩ | ⟨_, hv⟩ | ⟨hv, _⟩
          · exact hcastN_ne_u v₂ hv.symm
          · exact hcastN_ne_u Qu hu
          · exact hQuP1 (hcastN_inj hu)
          · exact hcastN_ne_u P₂ hv.symm
          · exact huvV hv
        · rcases hfn_adj' _ _ hadjl with ⟨u₂, _, _, hu, _⟩ | ⟨hu, _⟩ | ⟨_, hu⟩ | ⟨_, hv⟩ | ⟨hv, _⟩
          · exact hcastN_ne_v u₂ hu.symm
          · exact huvV hu.symm
          · exact hcastN_ne_v P₁ hu.symm
          · exact hQvP2 (hcastN_inj hv)
          · exact hcastN_ne_v Qv hv
        · rcases hfn_adj' _ _ hadjl with ⟨_, v₂, _, _, hv⟩ | ⟨_, hv⟩ | ⟨hv, _⟩ | ⟨hu, _⟩ | ⟨_, hu⟩
          · exact hcastN_ne_v v₂ hv.symm
          · exact hcastN_ne_v P₁ hv.symm
          · exact huvV hv.symm
          · exact hcastN_ne_v Qv hu
          · exact hQvP2 (hcastN_inj hu)
      · by_cases hk2 : (k : ℕ) = n - 2
        · rcases k with ⟨kv, hkm⟩; dsimp only at hk2; subst kv
          have hfk : f ⟨n - 2, hkm⟩ = fn2 := by
            funext x; simp [f, (show n - 2 ≠ n by omega), (show n - 2 ≠ n - 1 by omega)]
          rw [hfk, hfl]
          apply disjoint_edgeSet_of_adj
          intro u v hadjk hadjl
          rw [hfn2_adj] at hadjk
          rcases hadjk with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
          · simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase, Finset.mem_univ,
              and_true] at hv
            rcases hv with rfl | ⟨y, ⟨_, hyP1⟩, rfl⟩
            · rcases hfn_adj' _ _ hadjl with ⟨u', _, _, hu', _⟩ | ⟨_, hv'⟩ | ⟨hv', _⟩ | ⟨hu', _⟩ | ⟨_, hu'⟩
              · exact hcastN_ne_u u' hu'.symm
              · exact hcastN_ne_v P₁ hv'.symm
              · exact huvV hv'.symm
              · exact huvV hu'
              · exact hcastN_ne_u P₂ hu'.symm
            · rcases hfn_adj' _ _ hadjl with ⟨u', _, _, hu', _⟩ | ⟨_, hv'⟩ | ⟨hv', _⟩ | ⟨hu', _⟩ | ⟨_, hu'⟩
              · exact hcastN_ne_u u' hu'.symm
              · exact hyP1 (hcastN_inj hv')
              · exact hcastN_ne_u y hv'
              · exact huvV hu'
              · exact hcastN_ne_u P₂ hu'.symm
          · simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase, Finset.mem_univ,
              and_true] at hu
            rcases hu with rfl | ⟨y, ⟨_, hyP1⟩, rfl⟩
            · rcases hfn_adj' _ _ hadjl with ⟨_, v', _, _, hv'⟩ | ⟨hu', _⟩ | ⟨_, hu'⟩ | ⟨_, hv'⟩ | ⟨hv', _⟩
              · exact hcastN_ne_u v' hv'.symm
              · exact huvV hu'.symm
              · exact hcastN_ne_v P₁ hu'.symm
              · exact hcastN_ne_u P₂ hv'.symm
              · exact huvV hv'
            · rcases hfn_adj' _ _ hadjl with ⟨_, v', _, _, hv'⟩ | ⟨hu', _⟩ | ⟨_, hu'⟩ | ⟨_, hv'⟩ | ⟨hv', _⟩
              · exact hcastN_ne_u v' hv'.symm
              · exact hcastN_ne_u y hu'
              · exact hyP1 (hcastN_inj hu')
              · exact hcastN_ne_u P₂ hv'.symm
              · exact huvV hv'
        · by_cases hk3 : (k : ℕ) = n - 3
          · rcases k with ⟨kv, hkm⟩; dsimp only at hk3; subst kv
            have hfk : f ⟨n - 3, hkm⟩ = fn3 := by
              funext x; simp [f, (show n - 3 ≠ n by omega),
                (show n - 3 ≠ n - 1 by omega), (show n - 3 ≠ n - 2 by omega)]
            rw [hfk, hfl]
            apply disjoint_edgeSet_of_adj
            intro u v hadjk hadjl
            rw [hfn3_adj] at hadjk
            rcases hadjk with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
            · simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true] at hv
              rcases hv with ⟨y, ⟨_, hyP2⟩, rfl⟩
              rcases hfn_adj' _ _ hadjl with ⟨u', _, _, hu', _⟩ | ⟨hu', _⟩ | ⟨_, hu'⟩ | ⟨_, hv'⟩ | ⟨hv', _⟩
              · exact hcastN_ne_v u' hu'.symm
              · exact huvV hu'.symm
              · exact hcastN_ne_v P₁ hu'.symm
              · exact hyP2 (hcastN_inj hv')
              · exact hcastN_ne_v y hv'
            · simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true] at hu
              rcases hu with ⟨y, ⟨_, hyP2⟩, rfl⟩
              rcases hfn_adj' _ _ hadjl with ⟨_, v', _, _, hv'⟩ | ⟨_, hv'⟩ | ⟨hv', _⟩ | ⟨hu', _⟩ | ⟨_, hu'⟩
              · exact hcastN_ne_v v' hv'.symm
              · exact hcastN_ne_v P₁ hv'.symm
              · exact huvV hv'.symm
              · exact hcastN_ne_v y hu'
              · exact hyP2 (hcastN_inj hu')
          · have hk_le : (k : ℕ) ≤ n - 4 := by omega
            rw [hsmall_eq k hk_le, hfl]
            apply disjoint_edgeSet_of_adj
            intro u v hadjk hadjl
            rw [map_comp_adj hcastN_inj] at hadjk
            rcases hadjk with ⟨u₁, v₁, h1, rfl, rfl⟩
            rcases hfn_adj' _ _ hadjl with ⟨u₂, v₂, h2, hu, hv⟩ | ⟨hu, _⟩ | ⟨hv, _⟩ | ⟨hu, _⟩ | ⟨hv, _⟩
            · have hu' := hcastN_inj hu; have hv' := hcastN_inj hv; subst hu'; subst hv'
              have hdisj := hf'_disj ⟨k.1, ⟨k.2.1, by omega⟩⟩ ⟨n - 2, ⟨by omega, le_refl _⟩⟩
                (show k.1 < n - 2 by omega)
              rw [hTk_small k.1 hk_le] at hdisj
              exact Set.disjoint_left.mp hdisj (show s(u₁, v₁) ∈ _ from h1) (show s(u₁, v₁) ∈ _ from h2)
            · exact hcastN_ne_u u₁ hu
            · exact hcastN_ne_u v₁ hv
            · exact hcastN_ne_v u₁ hu
            · exact hcastN_ne_v v₁ hv
    · by_cases hl1 : (l : ℕ) = n - 1
      · rcases l with ⟨lv, hlm⟩; dsimp only at hl1; subst lv; dsimp only at hkl
        have hfl : f ⟨n - 1, hlm⟩ = fn1 := by funext x; simp [f, hl0]
        by_cases hk2 : (k : ℕ) = n - 2
        · rcases k with ⟨kv, hkm⟩; dsimp only at hk2; subst kv
          have hfk : f ⟨n - 2, hkm⟩ = fn2 := by
            funext x; simp [f, (show n - 2 ≠ n by omega), (show n - 2 ≠ n - 1 by omega)]
          rw [hfk, hfl]
          apply disjoint_edgeSet_of_adj
          intro u v hadjk hadjl
          rw [hfn2_adj] at hadjk
          rcases hadjk with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
          · simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase, Finset.mem_univ,
              and_true] at hv
            rcases hv with rfl | ⟨y, ⟨hyQu, _⟩, rfl⟩
            · rcases hfn1_adj _ _ hadjl with ⟨u', _, _, hu', _⟩ | ⟨_, hv'⟩ | ⟨hv', _⟩ | ⟨hu', _⟩ | ⟨_, hu'⟩
              · exact hcastN_ne_u u' hu'.symm
              · exact hcastN_ne_v Qu hv'.symm
              · exact huvV hv'.symm
              · exact huvV hu'
              · exact hcastN_ne_u Qv hu'.symm
            · rcases hfn1_adj _ _ hadjl with ⟨u', _, _, hu', _⟩ | ⟨_, hv'⟩ | ⟨hv', _⟩ | ⟨hu', _⟩ | ⟨_, hu'⟩
              · exact hcastN_ne_u u' hu'.symm
              · exact hyQu (hcastN_inj hv')
              · exact hcastN_ne_u y hv'
              · exact huvV hu'
              · exact hcastN_ne_u Qv hu'.symm
          · simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase, Finset.mem_univ,
              and_true] at hu
            rcases hu with rfl | ⟨y, ⟨hyQu, _⟩, rfl⟩
            · rcases hfn1_adj _ _ hadjl with ⟨_, v', _, _, hv'⟩ | ⟨hu', _⟩ | ⟨_, hu'⟩ | ⟨_, hv'⟩ | ⟨hv', _⟩
              · exact hcastN_ne_u v' hv'.symm
              · exact huvV hu'.symm
              · exact hcastN_ne_v Qu hu'.symm
              · exact hcastN_ne_u Qv hv'.symm
              · exact huvV hv'
            · rcases hfn1_adj _ _ hadjl with ⟨_, v', _, _, hv'⟩ | ⟨hu', _⟩ | ⟨_, hu'⟩ | ⟨_, hv'⟩ | ⟨hv', _⟩
              · exact hcastN_ne_u v' hv'.symm
              · exact hcastN_ne_u y hu'
              · exact hyQu (hcastN_inj hu')
              · exact hcastN_ne_u Qv hv'.symm
              · exact huvV hv'
        · by_cases hk3 : (k : ℕ) = n - 3
          · rcases k with ⟨kv, hkm⟩; dsimp only at hk3; subst kv
            have hfk : f ⟨n - 3, hkm⟩ = fn3 := by
              funext x; simp [f, (show n - 3 ≠ n by omega),
                (show n - 3 ≠ n - 1 by omega), (show n - 3 ≠ n - 2 by omega)]
            rw [hfk, hfl]
            apply disjoint_edgeSet_of_adj
            intro u v hadjk hadjl
            rw [hfn3_adj] at hadjk
            rcases hadjk with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
            · simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true] at hv
              rcases hv with ⟨y, ⟨hyQv, _⟩, rfl⟩
              rcases hfn1_adj _ _ hadjl with ⟨u', _, _, hu', _⟩ | ⟨hu', _⟩ | ⟨_, hu'⟩ | ⟨_, hv'⟩ | ⟨hv', _⟩
              · exact hcastN_ne_v u' hu'.symm
              · exact huvV hu'.symm
              · exact hcastN_ne_v Qu hu'.symm
              · exact hyQv (hcastN_inj hv')
              · exact hcastN_ne_v y hv'
            · simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true] at hu
              rcases hu with ⟨y, ⟨hyQv, _⟩, rfl⟩
              rcases hfn1_adj _ _ hadjl with ⟨_, v', _, _, hv'⟩ | ⟨_, hv'⟩ | ⟨hv', _⟩ | ⟨hu', _⟩ | ⟨_, hu'⟩
              · exact hcastN_ne_v v' hv'.symm
              · exact hcastN_ne_v Qu hv'.symm
              · exact huvV hv'.symm
              · exact hcastN_ne_v y hu'
              · exact hyQv (hcastN_inj hu')
          · have hk_le : (k : ℕ) ≤ n - 4 := by omega
            rw [hsmall_eq k hk_le, hfl]
            apply disjoint_edgeSet_of_adj
            intro u v hadjk hadjl
            rw [map_comp_adj hcastN_inj] at hadjk
            rcases hadjk with ⟨u₁, v₁, h1, rfl, rfl⟩
            rcases hfn1_adj _ _ hadjl with ⟨u₂, v₂, h2, hu, hv⟩ | ⟨hu, _⟩ | ⟨hv, _⟩ | ⟨hu, _⟩ | ⟨hv, _⟩
            · have hu' := hcastN_inj hu; have hv' := hcastN_inj hv; subst hu'; subst hv'
              have hdisj := hf'_disj ⟨k.1, ⟨k.2.1, by omega⟩⟩ ⟨n - 3, ⟨by omega, by omega⟩⟩
                (show k.1 < n - 3 by omega)
              rw [hTk_small k.1 hk_le] at hdisj
              exact Set.disjoint_left.mp hdisj (show s(u₁, v₁) ∈ _ from h1) (show s(u₁, v₁) ∈ _ from h2)
            · exact hcastN_ne_u u₁ hu
            · exact hcastN_ne_u v₁ hv
            · exact hcastN_ne_v u₁ hu
            · exact hcastN_ne_v v₁ hv
      · by_cases hl2 : (l : ℕ) = n - 2
        · rcases l with ⟨lv, hlm⟩; dsimp only at hl2; subst lv; dsimp only at hkl
          have hfl : f ⟨n - 2, hlm⟩ = fn2 := by funext x; simp [f, hl0, hl1]
          by_cases hk3 : (k : ℕ) = n - 3
          · rcases k with ⟨kv, hkm⟩; dsimp only at hk3; subst kv
            have hfk : f ⟨n - 3, hkm⟩ = fn3 := by
              funext x; simp [f, (show n - 3 ≠ n by omega),
                (show n - 3 ≠ n - 1 by omega), (show n - 3 ≠ n - 2 by omega)]
            rw [hfk, hfl]
            apply disjoint_edgeSet_of_adj
            intro u v hadjk hadjl
            rw [hfn3_adj] at hadjk
            rw [hfn2_adj] at hadjl
            rcases hadjk with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
            · simp only [Finset.mem_image] at hv
              rcases hv with ⟨y, _, rfl⟩
              rcases hadjl with ⟨hu, _⟩ | ⟨hv, _⟩
              · exact huvV hu.symm
              · exact hcastN_ne_u y hv
            · simp only [Finset.mem_image] at hu
              rcases hu with ⟨y, _, rfl⟩
              rcases hadjl with ⟨hu, _⟩ | ⟨hv, _⟩
              · exact hcastN_ne_u y hu
              · exact huvV hv.symm
          · have hk_le : (k : ℕ) ≤ n - 4 := by omega
            rw [hsmall_eq k hk_le, hfl]
            apply disjoint_edgeSet_of_adj
            intro u v hadjk hadjl
            rw [map_comp_adj hcastN_inj] at hadjk
            rcases hadjk with ⟨u₁, v₁, _, rfl, rfl⟩
            rw [hfn2_adj] at hadjl
            rcases hadjl with ⟨hu, _⟩ | ⟨hv, _⟩
            · exact hcastN_ne_u u₁ hu
            · exact hcastN_ne_u v₁ hv
        · by_cases hl3 : (l : ℕ) = n - 3
          · rcases l with ⟨lv, hlm⟩; dsimp only at hl3; subst lv; dsimp only at hkl
            have hfl : f ⟨n - 3, hlm⟩ = fn3 := by funext x; simp [f, hl0, hl1, hl2]
            have hk_le : (k : ℕ) ≤ n - 4 := by omega
            rw [hsmall_eq k hk_le, hfl]
            apply disjoint_edgeSet_of_adj
            intro u v hadjk hadjl
            rw [map_comp_adj hcastN_inj] at hadjk
            rcases hadjk with ⟨u₁, v₁, _, rfl, rfl⟩
            rw [hfn3_adj] at hadjl
            rcases hadjl with ⟨hu, _⟩ | ⟨hv, _⟩
            · exact hcastN_ne_v u₁ hu
            · exact hcastN_ne_v v₁ hv
          · have hl_le : (l : ℕ) ≤ n - 4 := by have := l.2.2; omega
            have hk_le : (k : ℕ) ≤ n - 4 := by omega
            rw [hsmall_eq k hk_le, hsmall_eq l hl_le]
            apply disjoint_edgeSet_of_adj
            intro u v hadjk hadjl
            rw [map_comp_adj hcastN_inj] at hadjk hadjl
            rcases hadjk with ⟨u₁, v₁, h1, hu1, hv1⟩
            rcases hadjl with ⟨u₂, v₂, h2, hu2, hv2⟩
            have hu := hcastN_inj (hu1.trans hu2.symm)
            have hv := hcastN_inj (hv1.trans hv2.symm)
            subst hu; subst hv
            have hdisj := hf'_disj ⟨k.1, ⟨k.2.1, by omega⟩⟩ ⟨l.1, ⟨l.2.1, by omega⟩⟩ hkl
            rw [hTk_small k.1 hk_le, hTk_small l.1 hl_le] at hdisj
            exact Set.disjoint_left.mp hdisj (show s(u₁, v₁) ∈ _ from h1)
              (show s(u₁, v₁) ∈ _ from h2)

set_option maxHeartbeats 800000 in
private lemma pack_case_C {n : ℕ} (hn3 : 3 ≤ n) {T : (k : ℕ) → SimpleGraph (Fin k)}
    (hT : ∀ k ∈ Set.Icc 2 n, (T k).IsTree)
    (hTn_notstar : ∀ c : Fin n, T n ≠ starGraph c)
    (hTn1_notstar : ∀ c : Fin (n - 1), T (n - 1) ≠ starGraph c)
    (h_all_small_stars : ∀ k ∈ Set.Icc 2 (n - 2), ∃ c : Fin k, T k = starGraph c)
    (ih : ∀ T' : (k : ℕ) → SimpleGraph (Fin k),
      (∀ k ∈ Set.Icc 2 (n - 2), (T' k).IsTree) →
      (∃ a₁ b₁ : ℕ, ∀ k ∈ Set.Icc 2 (n - 2), k ≠ a₁ → k ≠ b₁ → ∃ c : Fin k, T' k = starGraph c) →
      Erdos743.IsPacking (n - 2) (Set.Icc 2 (n - 2)) T') :
    Erdos743.IsPacking n (Set.Icc 2 n) T := by
  have hTn_tree : (T n).IsTree := hT n ⟨by omega, le_refl _⟩
  have hTn1_tree : (T (n - 1)).IsTree := hT (n - 1) ⟨by omega, by omega⟩
  obtain ⟨hcard_n, ℓ₁, ℓ₂, p₁, p₂, h12, h1p1, h1p2, h2p1, h2p2, hp12, hleaf1, hleaf2⟩ :=
    isTree_exists_two_leaves_distinct_parents hTn_tree hTn_notstar
  obtain ⟨hcard_n1, m₁, m₂, q₁, q₂, hm12, hm1q1, hm1q2, hm2q1, hm2q2, hq12, hmleaf1, hmleaf2⟩ :=
    isTree_exists_two_leaves_distinct_parents hTn1_tree hTn1_notstar
  rw [Fintype.card_fin] at hcard_n hcard_n1
  have hn5 : 5 ≤ n := by omega
  have hcard_e1 : Fintype.card {x : Fin n // x ≠ ℓ₁ ∧ x ≠ ℓ₂} = Fintype.card (Fin (n - 2)) := by
    have hset : ({x : Fin n // x ≠ ℓ₁ ∧ x ≠ ℓ₂} : Type) ≃
        {x : Fin n // x ∈ (Finset.univ.erase ℓ₁).erase ℓ₂} :=
      { toFun := fun x => ⟨x.1, by simp [x.2.1, x.2.2]⟩
        invFun := fun x => ⟨x.1, by
          have hx1 := Finset.mem_erase.mp x.2
          have hx2 := Finset.mem_erase.mp hx1.2
          exact ⟨hx2.1, hx1.1⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr hset, Fintype.card_coe,
      Finset.card_erase_of_mem (by simp [h12.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin]
    omega
  have hcard_e2 : Fintype.card {x : Fin (n - 1) // x ≠ m₁ ∧ x ≠ m₂} =
      Fintype.card (Fin (n - 1 - 2)) := by
    have hset : ({x : Fin (n - 1) // x ≠ m₁ ∧ x ≠ m₂} : Type) ≃
        {x : Fin (n - 1) // x ∈ (Finset.univ.erase m₁).erase m₂} :=
      { toFun := fun x => ⟨x.1, by simp [x.2.1, x.2.2]⟩
        invFun := fun x => ⟨x.1, by
          have hx1 := Finset.mem_erase.mp x.2
          have hx2 := Finset.mem_erase.mp hx1.2
          exact ⟨hx2.1, hx1.1⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr hset, Fintype.card_coe,
      Finset.card_erase_of_mem (by simp [hm12.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin]
    omega
  let e1 : {x : Fin n // x ≠ ℓ₁ ∧ x ≠ ℓ₂} ≃ Fin (n - 2) := Fintype.equivOfCardEq hcard_e1
  let e2 : {x : Fin (n - 1) // x ≠ m₁ ∧ x ≠ m₂} ≃ Fin (n - 1 - 2) :=
    Fintype.equivOfCardEq hcard_e2
  let Tn'' : SimpleGraph (Fin (n - 2)) :=
    ((T n).induce {x | x ≠ ℓ₁ ∧ x ≠ ℓ₂}).comap e1.symm
  let Tn1'' : SimpleGraph (Fin (n - 1 - 2)) :=
    ((T (n - 1)).induce {x | x ≠ m₁ ∧ x ≠ m₂}).comap e2.symm
  have hTn''_tree : Tn''.IsTree :=
    isTree_comap_equiv
      (isTree_induce_erase_two_leaves hTn_tree h12 h1p1 h2p2 h1p2 hleaf1 hleaf2) e1.symm
  have hTn1''_tree : Tn1''.IsTree :=
    isTree_comap_equiv
      (isTree_induce_erase_two_leaves hTn1_tree hm12 hm1q1 hm2q2 hm1q2 hmleaf1 hmleaf2) e2.symm
  let T' : (k : ℕ) → SimpleGraph (Fin k) := fun k =>
    if hk : k = n - 2 then Tn''.comap (Fin.cast hk)
    else if hk1 : k = n - 3 then Tn1''.comap (Fin.cast (by omega))
    else T k
  have hT'_tree : ∀ k ∈ Set.Icc 2 (n - 2), (T' k).IsTree := by
    intro k hk
    by_cases h1 : k = n - 2
    · simp only [T', h1, dite_true]
      exact isTree_comap_equiv hTn''_tree (finCongr h1)
    · by_cases h2 : k = n - 3
      · subst h2
        simp only [T', (show n - 3 ≠ n - 2 by omega), dite_false, dite_true]
        exact isTree_comap_equiv hTn1''_tree (finCongr (by omega))
      · simp only [T', h1, h2, dite_false]
        exact hT k ⟨hk.1, by have := hk.2; omega⟩
  have hT'_star : ∃ a₁ b₁ : ℕ, ∀ k ∈ Set.Icc 2 (n - 2), k ≠ a₁ → k ≠ b₁ →
      ∃ c : Fin k, T' k = starGraph c := by
    refine ⟨n - 2, n - 3, fun k hk h1 h2 => ?_⟩
    simp only [T', h1, h2, dite_false]
    exact h_all_small_stars k hk
  obtain ⟨f', hf'_inj, hf'_disj⟩ := ih T' hT'_tree hT'_star
  let gn2 : Fin (n - 2) → Fin (n - 2) := f' ⟨n - 2, ⟨by omega, le_refl _⟩⟩
  let gn3 : Fin (n - 1 - 2) → Fin (n - 2) :=
    fun x => f' ⟨n - 3, ⟨by omega, by omega⟩⟩ (x.cast (show n - 1 - 2 = n - 3 by omega))
  have hgn2_inj : Function.Injective gn2 := hf'_inj ⟨n - 2, ⟨by omega, le_refl _⟩⟩
  have hgn3_inj : Function.Injective gn3 := by
    intro x y h
    have := hf'_inj ⟨n - 3, ⟨by omega, by omega⟩⟩ h
    exact Fin.ext (by simpa using congrArg Fin.val this)
  let P₁ : Fin (n - 2) := gn2 (e1 ⟨p₁, h1p1.symm, h2p1.symm⟩)
  let P₂ : Fin (n - 2) := gn2 (e1 ⟨p₂, h1p2.symm, h2p2.symm⟩)
  let Q₁ : Fin (n - 2) := gn3 (e2 ⟨q₁, hm1q1.symm, hm2q1.symm⟩)
  let Q₂ : Fin (n - 2) := gn3 (e2 ⟨q₂, hm1q2.symm, hm2q2.symm⟩)
  have hP12 : P₁ ≠ P₂ := fun h => hp12 (congrArg Subtype.val (e1.injective (hgn2_inj h)))
  have hQ12 : Q₁ ≠ Q₂ := fun h => hq12 (congrArg Subtype.val (e2.injective (hgn3_inj h)))
  let uV : Fin n := ⟨n - 2, by omega⟩
  let vV : Fin n := ⟨n - 1, by omega⟩
  have huvV : uV ≠ vV := by
    intro h; have := congrArg Fin.val h; dsimp [uV, vV] at this; omega
  let castN : Fin (n - 2) → Fin n := Fin.castLE (by omega)
  have hcastN_inj : Function.Injective castN := Fin.castLE_injective _
  have hcastN_ne_u : ∀ x : Fin (n - 2), castN x ≠ uV := fun x h => by
    have := congrArg Fin.val h; dsimp [castN, uV] at this; omega
  have hcastN_ne_v : ∀ x : Fin (n - 2), castN x ≠ vV := fun x h => by
    have := congrArg Fin.val h; dsimp [castN, vV] at this; omega
  obtain ⟨fn, hfn_inj, hfn_adj⟩ :=
    extend_two_leaves (by omega) (le_refl n) h12 h1p1 h1p2 h2p1 h2p2 hleaf1 hleaf2
      e1 hgn2_inj huvV (by dsimp [uV]; omega) (by dsimp [vV]; omega)
  have hpair : ∃ (uM vM : Fin n) (Qu Qv : Fin (n - 2)),
      ((uM = uV ∧ vM = vV ∧ Qu = Q₁ ∧ Qv = Q₂) ∨
       (uM = vV ∧ vM = uV ∧ Qu = Q₂ ∧ Qv = Q₁)) ∧
      Qu ≠ P₁ ∧ Qv ≠ P₂ := by
    by_cases h : Q₁ ≠ P₁ ∧ Q₂ ≠ P₂
    · exact ⟨uV, vV, Q₁, Q₂, Or.inl ⟨rfl, rfl, rfl, rfl⟩, h.1, h.2⟩
    · refine ⟨vV, uV, Q₂, Q₁, Or.inr ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
      · intro h21; apply h
        refine ⟨fun h11 => hQ12 (h11.trans h21.symm), fun h22 => hP12 (h21.symm.trans h22)⟩
      · intro h12'; apply h
        refine ⟨fun h11 => hP12 (h11.symm.trans h12'), fun h22 => hQ12 (h12'.trans h22.symm)⟩
  obtain ⟨uM, vM, Qu, Qv, hpair_eq, hQuP1, hQvP2⟩ := hpair
  have huvM : uM ≠ vM := by
    rcases hpair_eq with ⟨rfl, rfl, _, _⟩ | ⟨rfl, rfl, _, _⟩
    · exact huvV
    · exact huvV.symm
  have huM_ge : n - 2 ≤ uM.val := by
    rcases hpair_eq with ⟨rfl, rfl, _, _⟩ | ⟨rfl, rfl, _, _⟩
    · exact le_refl _
    · exact Nat.sub_le_sub_left (by decide) n
  have hvM_ge : n - 2 ≤ vM.val := by
    rcases hpair_eq with ⟨rfl, rfl, _, _⟩ | ⟨rfl, rfl, _, _⟩
    · exact Nat.sub_le_sub_left (by decide) n
    · exact le_refl _
  obtain ⟨fn1, hfn1_inj, hfn1_adj_raw⟩ :=
    extend_two_leaves (by omega) (by omega) hm12 hm1q1 hm1q2 hm2q1 hm2q2 hmleaf1 hmleaf2
      e2 hgn3_inj huvM huM_ge hvM_ge
  have hfn1_adj : ∀ u v : Fin n, ((T (n - 1)).map fn1).Adj u v →
      (∃ u' v' : Fin (n - 2), ((T' (n - 3)).map (f' ⟨n - 3, ⟨by omega, by omega⟩⟩)).Adj u' v' ∧
        u = castN u' ∧ v = castN v') ∨
      (u = uV ∧ v = castN Qu) ∨ (v = uV ∧ u = castN Qu) ∨
      (u = vV ∧ v = castN Qv) ∨ (v = vV ∧ u = castN Qv) := by
    intro u v hadj
    have hres := hfn1_adj_raw u v hadj
    rcases hres with ⟨u', v', hmid, hu', hv'⟩ | h1 | h2 | h3 | h4
    · left
      refine ⟨u', v', ?_, hu', hv'⟩
      rcases hmid with ⟨huv', a, b, hab, rfl, rfl⟩
      refine ⟨huv', a.cast (show n - 1 - 2 = n - 3 by omega),
        b.cast (show n - 1 - 2 = n - 3 by omega), ?_, rfl, rfl⟩
      simp only [T', (show n - 3 ≠ n - 2 by omega), dite_false, dite_true, Tn1'',
        SimpleGraph.comap_adj]
      exact hab
    · rcases hpair_eq with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · right; left; exact h1
      · right; right; right; left; exact h1
    · rcases hpair_eq with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · right; right; left; exact h2
      · right; right; right; right; exact h2
    · rcases hpair_eq with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · right; right; right; left; exact h3
      · right; left; exact h3
    · rcases hpair_eq with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · right; right; right; right; exact h4
      · right; right; left; exact h4
  obtain ⟨cn2, hTn2⟩ := h_all_small_stars (n - 2) ⟨by omega, le_refl _⟩
  let leaves_u : Finset (Fin n) := insert vV (((Finset.univ.erase P₁).erase Qu).image castN)
  have huV_not_leaves : uV ∉ leaves_u := by
    simp only [leaves_u, Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
    exact ⟨huvV, fun x _ hx => hcastN_ne_u x hx⟩
  have hleaves_u_card : leaves_u.card + 1 = n - 2 := by
    have hv_not : vV ∉ (((Finset.univ.erase P₁).erase Qu).image castN) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro x _ hx; exact hcastN_ne_v x hx
    rw [Finset.card_insert_of_notMem hv_not,
      Finset.card_image_of_injective _ hcastN_inj,
      Finset.card_erase_of_mem (by simp [hQuP1]),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨fn2, hfn2_inj, _, hfn2_adj⟩ :=
    star_embed_into_finset cn2 uV leaves_u huV_not_leaves hleaves_u_card
  obtain ⟨cn3, hTn3⟩ := h_all_small_stars (n - 3) ⟨by omega, by omega⟩
  let leaves_v : Finset (Fin n) := ((Finset.univ.erase P₂).erase Qv).image castN
  have hvV_not_leaves : vV ∉ leaves_v := by
    simp only [leaves_v, Finset.mem_image, not_exists, not_and]
    intro x _ hx; exact hcastN_ne_v x hx
  have hleaves_v_card : leaves_v.card + 1 = n - 3 := by
    rw [Finset.card_image_of_injective _ hcastN_inj,
      Finset.card_erase_of_mem (by simp [hQvP2]),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨fn3, hfn3_inj, _, hfn3_adj⟩ :=
    star_embed_into_finset cn3 vV leaves_v hvV_not_leaves hleaves_v_card
  have hfn_adj' : ∀ u v : Fin n, ((T n).map fn).Adj u v →
      (∃ u' v' : Fin (n - 2), ((T' (n - 2)).map gn2).Adj u' v' ∧
        u = castN u' ∧ v = castN v') ∨
      (u = uV ∧ v = castN P₁) ∨ (v = uV ∧ u = castN P₁) ∨
      (u = vV ∧ v = castN P₂) ∨ (v = vV ∧ u = castN P₂) := by
    intro u v hadj
    rcases hfn_adj u v hadj with ⟨u', v', hmid, hu', hv'⟩ | hrest
    · left
      refine ⟨u', v', ?_, hu', hv'⟩
      rcases hmid with ⟨huv', a, b, hab, rfl, rfl⟩
      refine ⟨huv', a, b, ?_, rfl, rfl⟩
      simp only [T', dite_true, Tn'', SimpleGraph.comap_adj]
      exact hab
    · exact Or.inr hrest
  have hTk_small : ∀ k : ℕ, k ≤ n - 4 → T' k = T k := by
    intro k hk
    have h1 : k ≠ n - 2 := by omega
    have h2 : k ≠ n - 3 := by omega
    simp [T', h1, h2]
  exact pack_case_C_assemble hn5 hTk_small hf'_inj hf'_disj huvV hcastN_inj hcastN_ne_u hcastN_ne_v
    hQuP1 hQvP2 hfn_inj hfn_adj' hfn1_inj hfn1_adj hfn2_inj (by rw [hTn2]; exact hfn2_adj)
    hfn3_inj (by rw [hTn3]; exact hfn3_adj)

private lemma pack_all_but_two :
    ∀ n : ℕ, ∀ T : (k : ℕ) → SimpleGraph (Fin k),
      (∀ k ∈ Set.Icc 2 n, (T k).IsTree) →
      (∃ a b : ℕ, ∀ k ∈ Set.Icc 2 n, k ≠ a → k ≠ b → ∃ c : Fin k, T k = starGraph c) →
      Erdos743.IsPacking n (Set.Icc 2 n) T := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T hT hstar
    by_cases hn2 : n < 2
    · refine ⟨fun k => False.elim (by rcases k.2 with ⟨h1, h2⟩; omega), ?_, ?_⟩
      · intro k; exfalso; rcases k.2 with ⟨h1, h2⟩; omega
      · intro k; exfalso; rcases k.2 with ⟨h1, h2⟩; omega
    · by_cases hn_eq2 : n = 2
      · subst hn_eq2
        refine ⟨fun k x => x.cast (by rcases k.2 with ⟨h1, h2⟩; omega), ?_, ?_⟩
        · intro k x y h
          exact Fin.ext (by have := congrArg Fin.val h; simpa using this)
        · intro k l hkl
          exfalso; rcases k.2 with ⟨hk1, hk2⟩; rcases l.2 with ⟨hl1, hl2⟩; omega
      · have hn3 : 3 ≤ n := by omega
        by_cases hTn_star : ∃ c : Fin n, T n = starGraph c
        · obtain ⟨cn, hTn⟩ := hTn_star
          obtain ⟨a, b, hab⟩ := hstar
          exact pack_case_A hn3 hTn (ih (n - 1) (by omega) T
            (fun k hk => hT k ⟨hk.1, by have := hk.2; omega⟩)
            ⟨a, b, fun k hk hka hkb => hab k ⟨hk.1, by have := hk.2; omega⟩ hka hkb⟩)
        · by_cases hTn1_star : ∃ c : Fin (n - 1), T (n - 1) = starGraph c
          · obtain ⟨cn1, hTn1⟩ := hTn1_star
            obtain ⟨a, b, hab⟩ := hstar
            have h_other_star : ∃ a' : ℕ, ∀ k ∈ Set.Icc 2 (n - 1), k ≠ a' →
                ∃ c : Fin k, T k = starGraph c := by
              by_cases hna : n = a
              · exact ⟨b, fun k hk hkb =>
                  hab k ⟨hk.1, by have := hk.2; omega⟩ (by have := hk.2; omega) hkb⟩
              · have hnb : n = b := by
                  by_contra hnb
                  exact hTn_star (hab n ⟨by omega, le_refl _⟩ hna hnb)
                exact ⟨a, fun k hk hka =>
                  hab k ⟨hk.1, by have := hk.2; omega⟩ hka (by have := hk.2; omega)⟩
            obtain ⟨a', ha'⟩ := h_other_star
            exact pack_case_B hn3 hT hTn1 ha' (ih (n - 1) (by omega))
          · obtain ⟨a, b, hab⟩ := hstar
            have h_all_small_stars : ∀ k ∈ Set.Icc 2 (n - 2), ∃ c : Fin k, T k = starGraph c := by
              intro k hk
              have hne_ab : (a = n ∧ b = n - 1) ∨ (a = n - 1 ∧ b = n) := by
                have hna : n = a ∨ n = b := by
                  by_contra h
                  push Not at h
                  exact hTn_star (hab n ⟨by omega, le_refl _⟩ h.1 h.2)
                have hn1a : n - 1 = a ∨ n - 1 = b := by
                  by_contra h
                  push Not at h
                  exact hTn1_star (hab (n - 1) ⟨by omega, by omega⟩ h.1 h.2)
                omega
              rcases hne_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hab k ⟨hk.1, by have := hk.2; omega⟩ (by have := hk.2; omega)
                  (by have := hk.2; omega)
              · exact hab k ⟨hk.1, by have := hk.2; omega⟩ (by have := hk.2; omega)
                  (by have := hk.2; omega)
            exact pack_case_C hn3 hT (fun c hc => hTn_star ⟨c, hc⟩)
              (fun c hc => hTn1_star ⟨c, hc⟩) h_all_small_stars (ih (n - 2) (by omega))

end OMA_Erdos743_AllButTwoStars

theorem OMA.solution : type_of% @Erdos743.erdos_743.variants.all_but_two_stars :=
  OMA_Erdos743_AllButTwoStars.pack_all_but_two

