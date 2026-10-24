/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CliqueMinorsLib.GraphOps

/-!
# Dense graphs have large clique minors; graphs without small clique minors

For finite simple graphs, with minors given by branch-set models (`MinorModel`):

* `CliqueMinors.mader`: **Mader (1967).** A nonempty graph with `2 ^ r · |V| ≤ 8 · |E|` (average
  degree at least `2 ^ (r - 2)`) has `K_r` as a minor.
* `CliqueMinors.exists_degree_le_two`: **Dirac (1952).** A nonempty graph without a `K₄` minor has
  a vertex of degree at most two.
* `CliqueMinors.card_edgeFinset_le`: a graph on `n ≥ 2` vertices without a `K₄` minor has at most
  `2n - 3` edges.
* `CliqueMinors.colorable_two_of_not_isMinor_K3`, `CliqueMinors.colorable_three_of_not_isMinor_K4`:
  **Hadwiger's conjecture for `t ≤ 4`** (Hadwiger 1943, Dirac 1952): a finite graph without a
  `K_t` minor is `(t - 1)`-colourable for `t = 3, 4`.
-/

@[expose] public section

open SimpleGraph

namespace CliqueMinors

variable {V W : Type*}

/-- A branch-set model of `H` as a minor of `G`: disjoint, nonempty, connected branch sets, one
for every vertex of `H`, with an edge of `G` between the branch sets of adjacent vertices. -/
structure MinorModel (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : W → Finset V
  branch_nonempty : ∀ w, (branch w).Nonempty
  branch_connected : ∀ w, (G.induce (↑(branch w) : Set V)).Connected
  branch_disjoint : ∀ w w', w ≠ w' → Disjoint (branch w) (branch w')
  branch_adjacent : ∀ w w', H.Adj w w' → ∃ u ∈ branch w, ∃ v ∈ branch w', G.Adj u v

/-- `H` is a minor of `G`. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop := Nonempty (MinorModel G H)

section Helpers

open Relation

/-- Adjacency of `G` restricted to the vertex set `B`. -/
def InAdj (G : SimpleGraph V) (B : Finset V) (a b : V) : Prop := a ∈ B ∧ b ∈ B ∧ G.Adj a b

theorem reflTransGen_of_step {α : Type*} {r p : α → α → Prop}
    (h : ∀ a b, r a b → ReflTransGen p a b) {a b : α} (hab : ReflTransGen r a b) :
    ReflTransGen p a b := by
  induction hab with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (h _ _ hbc)

theorem induce_connected_of_root (G : SimpleGraph V) (B : Finset V) (r : V) (hr : r ∈ B)
    (h : ∀ v ∈ B, ReflTransGen (InAdj G B) r v) : (G.induce (B : Set V)).Connected := by
  have key : ∀ v, ReflTransGen (InAdj G B) r v → ∀ hv : v ∈ B,
      (G.induce (B : Set V)).Reachable ⟨r, hr⟩ ⟨v, hv⟩ := by
    intro v hrv
    induction hrv with
    | refl => intro _; rfl
    | tail _ hbc ih =>
      intro _
      exact (ih hbc.1).trans (Adj.reachable (by simpa using hbc.2.2))
  rw [connected_iff]
  refine ⟨fun u v => ?_, ⟨⟨r, hr⟩⟩⟩
  exact (key u.1 (h u.1 u.2) u.2).symm.trans (key v.1 (h v.1 v.2) v.2)

theorem reflTransGen_of_connected {G : SimpleGraph V} {B : Finset V}
    (h : (G.induce (B : Set V)).Connected) {u v : V} (hu : u ∈ B) (hv : v ∈ B) :
    ReflTransGen (InAdj G B) u v := by
  have := (reachable_iff_reflTransGen _ _).1 (h.preconnected ⟨u, hu⟩ ⟨v, hv⟩)
  exact this.lift Subtype.val (fun a b hab => ⟨a.2, b.2, hab⟩)

theorem induce_connected_mono {G G' : SimpleGraph V} (hle : G' ≤ G) {B : Finset V}
    (h : (G'.induce (B : Set V)).Connected) : (G.induce (B : Set V)).Connected := by
  obtain ⟨⟨r, hr⟩⟩ := h.nonempty
  exact induce_connected_of_root G _ r hr fun v hv =>
    reflTransGen_of_step (fun a b hab => ReflTransGen.single ⟨hab.1, hab.2.1, hle hab.2.2⟩)
      (reflTransGen_of_connected h hr hv)

theorem singleton_connected (G : SimpleGraph V) (v : V) :
    (G.induce (({v} : Finset V) : Set V)).Connected :=
  induce_connected_of_root G _ v (Finset.mem_singleton_self _) fun w hw => by
    rw [Finset.mem_singleton.1 hw]

theorem MinorModel.exists_adj {G : SimpleGraph V} {r : ℕ}
    (M : MinorModel G (⊤ : SimpleGraph (Fin r))) (hr : 2 ≤ r) (i : Fin r) {v : V}
    (hv : v ∈ M.branch i) : ∃ u, G.Adj v u := by
  obtain ⟨j, hj⟩ : ∃ j : Fin r, j ≠ i := by
    by_cases h : (i : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩
  obtain ⟨u, hu, w, _, huw⟩ := M.branch_adjacent i j (by simpa using hj.symm)
  rcases (reflTransGen_of_connected (M.branch_connected i) hv hu).cases_head with h | ⟨c, hc, _⟩
  · subst h; exact ⟨w, huw⟩
  · exact ⟨c, hc.2.2⟩

theorem isMinor_mono {G G' : SimpleGraph V} {H : SimpleGraph W} (hle : G' ≤ G)
    (h : IsMinor H G') : IsMinor H G := by
  obtain ⟨M⟩ := h
  refine ⟨⟨M.branch, M.branch_nonempty, fun w => induce_connected_mono hle (M.branch_connected w),
    M.branch_disjoint, fun w w' hww' => ?_⟩⟩
  obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent w w' hww'
  exact ⟨u, hu, v, hv, hle huv⟩

theorem isMinor_of_clique {G : SimpleGraph V} {r : ℕ} (f : Fin r → V)
    (hf : ∀ i j, i ≠ j → G.Adj (f i) (f j)) : IsMinor (⊤ : SimpleGraph (Fin r)) G := by
  refine ⟨⟨fun i => {f i}, fun i => Finset.singleton_nonempty _,
    fun i => singleton_connected G (f i), fun i j hij => ?_, fun i j hij => ?_⟩⟩
  · rw [Finset.disjoint_singleton]; exact (hf i j hij).ne
  · exact ⟨f i, Finset.mem_singleton_self _, f j, Finset.mem_singleton_self _,
      hf i j (by simpa using hij)⟩

theorem isMinor_lift_contract {G G' : SimpleGraph V} {x y : V} (hxy : G.Adj x y)
    (hG' : ∀ u v, G'.Adj u v →
      u ≠ y ∧ v ≠ y ∧ (G.Adj u v ∨ (u = x ∧ G.Adj y v) ∨ (v = x ∧ G.Adj y u)))
    {r : ℕ} (hr : 2 ≤ r) (h : IsMinor (⊤ : SimpleGraph (Fin r)) G') :
    IsMinor (⊤ : SimpleGraph (Fin r)) G := by
  classical
  obtain ⟨M⟩ := h
  have hy : ∀ i, y ∉ M.branch i := fun i hyi => by
    obtain ⟨u, hu⟩ := M.exists_adj hr i hyi
    exact (hG' _ _ hu).1 rfl
  let B : Fin r → Finset V := fun i =>
    if x ∈ M.branch i then insert y (M.branch i) else M.branch i
  have hsub : ∀ i, M.branch i ⊆ B i := fun i => by
    simp only [B]; split_ifs
    · exact Finset.subset_insert _ _
    · exact le_rfl
  refine ⟨⟨B, fun i => (M.branch_nonempty i).mono (hsub i), fun i => ?_, fun i j hij => ?_,
    fun i j hij => ?_⟩⟩
  · by_cases hx : x ∈ M.branch i
    · have hB : B i = insert y (M.branch i) := by simp [B, hx]
      have hyB : y ∈ B i := by rw [hB]; exact Finset.mem_insert_self _ _
      apply induce_connected_of_root G _ x (hsub i hx)
      have step : ∀ v ∈ M.branch i, ReflTransGen (InAdj G (B i)) x v := by
        intro v hv
        refine reflTransGen_of_step (fun a b hab => ?_)
          (reflTransGen_of_connected (M.branch_connected i) hx hv)
        obtain ⟨ha, hb, hab⟩ := hab
        rcases (hG' a b hab).2.2 with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
        · exact ReflTransGen.single ⟨hsub i ha, hsub i hb, h⟩
        · exact (ReflTransGen.single ⟨hsub i ha, hyB, hxy⟩).tail ⟨hyB, hsub i hb, h⟩
        · exact (ReflTransGen.single ⟨hsub i ha, hyB, h.symm⟩).tail ⟨hyB, hsub i hb, hxy.symm⟩
      intro v hv
      rw [hB, Finset.mem_insert] at hv
      rcases hv with rfl | hv
      · exact ReflTransGen.single ⟨hsub i hx, hyB, hxy⟩
      · exact step v hv
    · have hB : B i = M.branch i := by simp [B, hx]
      rw [hB]
      obtain ⟨v₀, hv₀⟩ := M.branch_nonempty i
      apply induce_connected_of_root G _ v₀ hv₀
      intro v hv
      refine reflTransGen_of_step (fun a b hab => ?_)
        (reflTransGen_of_connected (M.branch_connected i) hv₀ hv)
      obtain ⟨ha, hb, hab⟩ := hab
      rcases (hG' a b hab).2.2 with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
      · exact ReflTransGen.single ⟨ha, hb, h⟩
      · exact absurd ha hx
      · exact absurd hb hx
  · have hd := M.branch_disjoint i j hij
    simp only [B]
    split_ifs with hi hj hj
    · exact absurd (Finset.disjoint_left.1 hd hi) (by simpa using hj)
    · rw [Finset.disjoint_insert_left]; exact ⟨hy j, hd⟩
    · rw [Finset.disjoint_insert_right]; exact ⟨hy i, hd⟩
    · exact hd
  · obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent i j hij
    rcases (hG' u v huv).2.2 with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact ⟨u, hsub i hu, v, hsub j hv, h⟩
    · refine ⟨y, ?_, v, hsub j hv, h⟩
      simp [B, hu]
    · refine ⟨u, hsub i hu, y, ?_, h.symm⟩
      simp [B, hv]

theorem isMinor_lift_cone {G G' : SimpleGraph V} {x : V}
    (hG' : ∀ u v, G'.Adj u v → G.Adj u v ∧ G.Adj x u ∧ G.Adj x v)
    {r : ℕ} (hr : 2 ≤ r) (h : IsMinor (⊤ : SimpleGraph (Fin r)) G') :
    IsMinor (⊤ : SimpleGraph (Fin (r + 1))) G := by
  obtain ⟨M⟩ := h
  have hle : G' ≤ G := fun u v huv => (hG' u v huv).1
  have hmem : ∀ i, ∀ v ∈ M.branch i, G.Adj x v := fun i v hv => by
    obtain ⟨u, hu⟩ := M.exists_adj hr i hv; exact (hG' _ _ hu).2.1
  have hx : ∀ i, x ∉ M.branch i := fun i hxi => (hmem i x hxi).ne rfl
  let B : Fin (r + 1) → Finset V := Fin.lastCases {x} M.branch
  have hBl : B (Fin.last r) = {x} := Fin.lastCases_last
  have hBc : ∀ i, B i.castSucc = M.branch i := fun i => Fin.lastCases_castSucc i
  refine ⟨⟨B, fun i => ?_, fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩⟩
  · induction i using Fin.lastCases with
    | last => simp [hBl]
    | cast i => simpa [hBl, hBc] using M.branch_nonempty i
  · induction i using Fin.lastCases with
    | last => rw [hBl]; exact singleton_connected G x
    | cast i => rw [hBc]; exact induce_connected_mono hle (M.branch_connected i)
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j => simpa [hBl, hBc] using hx j
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [hBl, hBc] using hx i
      | cast j => simpa [hBl, hBc] using M.branch_disjoint i j (fun h => hij (by rw [h]))
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j =>
        obtain ⟨v, hv⟩ := M.branch_nonempty j
        exact ⟨x, by simp [hBl], v, by simpa [hBl, hBc] using hv, hmem j v hv⟩
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        obtain ⟨v, hv⟩ := M.branch_nonempty i
        exact ⟨v, by simpa [hBl, hBc] using hv, x, by simp [hBl], (hmem i v hv).symm⟩
      | cast j =>
        obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent i j (by simpa using hij)
        exact ⟨u, by simpa [hBl, hBc] using hu, v, by simpa [hBl, hBc] using hv, hle huv⟩

end Helpers

section Counting


variable [Fintype V]

open Classical in
theorem mader_aux (r : ℕ) : ∀ (G : SimpleGraph V) (S : Finset V), S.Nonempty →
    (∀ a b, G.Adj a b → a ∈ S) → 2 ^ r * S.card ≤ 8 * G.edgeFinset.card →
    IsMinor (⊤ : SimpleGraph (Fin r)) G := by
  induction r using Nat.strong_induction_on with
  | _ r ihr =>
  match r with
  | 0 => exact fun G _ _ _ _ => isMinor_of_clique Fin.elim0 (fun i => i.elim0)
  | 1 =>
    intro G S hS _ _
    obtain ⟨v, _⟩ := hS
    exact isMinor_of_clique (fun _ => v) (fun i j h => absurd (Subsingleton.elim i j) h)
  | 2 =>
    intro G S hS _ hE
    have := hS.card_pos
    obtain ⟨a, b, hab⟩ := exists_adj_of_card_pos (G := G) (by omega)
    refine isMinor_of_clique ![a, b] fun i j h => ?_
    fin_cases i <;> fin_cases j <;> simp_all [hab.symm]
  | k + 3 =>
    suffices ∀ n (G : SimpleGraph V) (S : Finset V), S.card = n → S.Nonempty →
        (∀ a b, G.Adj a b → a ∈ S) → 2 ^ (k + 3) * S.card ≤ 8 * G.edgeFinset.card →
        IsMinor (⊤ : SimpleGraph (Fin (k + 3))) G from fun G S => this _ G S rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
    intro G S hn hS hsupp hE
    have hpow : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
    have hE' : 2 ^ k * S.card ≤ G.edgeFinset.card := by
      rw [hpow, mul_assoc] at hE; omega
    have hS1 := hS.card_pos
    have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hE0 : 0 < G.edgeFinset.card := by nlinarith
    obtain ⟨x, y, hxy⟩ := exists_adj_of_card_pos hE0
    have hmul : 2 ^ k * (S.card - 1) + 2 ^ k = 2 ^ k * S.card := by
      rw [Nat.mul_sub_one]; have : 2 ^ k ≤ 2 ^ k * S.card := Nat.le_mul_of_pos_right _ hS1
      omega
    by_cases hc : ∃ y', G.Adj x y' ∧ 2 ^ k * (S.card - 1) ≤ (contractG G x y').edgeFinset.card
    · obtain ⟨y', hxy', hc⟩ := hc
      refine isMinor_lift_contract (G' := contractG G x y') hxy'
        (fun u v h => (contractG_adj.1 h).2) (by omega) ?_
      have hy'S : y' ∈ S := hsupp _ _ hxy'.symm
      refine ihn (S.card - 1) (by omega) (contractG G x y') (S.erase y')
        (Finset.card_erase_of_mem hy'S)
        ⟨x, Finset.mem_erase.2 ⟨hxy'.ne, hsupp _ _ hxy'⟩⟩ (contract_support hxy' hsupp) ?_
      rw [Finset.card_erase_of_mem hy'S, hpow, mul_assoc]
      omega
    · simp only [not_exists, not_and, not_le] at hc
      have hcom : ∀ v, G.Adj x v → 2 ^ k ≤ (G.neighborFinset x ∩ G.neighborFinset v).card := by
        intro v hv
        have h1 := card_edge_contract hv
        have h2 := hc v hv
        omega
      have hcone := cone_edges hcom
      refine isMinor_lift_cone (G' := coneG G x) (fun u v h => h) (r := k + 2) (by omega) ?_
      refine ihr (k + 2) (by omega) (coneG G x) (G.neighborFinset x)
        ⟨y, by simpa using hxy⟩ (fun a b h => by simpa using h.2.1) ?_
      have : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
      rw [this, mul_assoc]
      omega

end Counting

section Dirac


variable [Fintype V]

open Classical in
omit [Fintype V] in
theorem isMinor_K4_of_clique {G : SimpleGraph V} {x a b c : V} (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hxc : G.Adj x c) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    IsMinor (⊤ : SimpleGraph (Fin 4)) G := by
  refine isMinor_of_clique ![x, a, b, c] fun i j h => ?_
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl h |
    simp [hxa, hxb, hxc, hab, hac, hbc, hxa.symm, hxb.symm, hxc.symm, hab.symm, hac.symm, hbc.symm]

open Classical in
/-- The hypotheses available in the minimal-counterexample argument for Dirac's theorem. -/
structure DiracCtx (G : SimpleGraph V) (S : Finset V) : Prop where
  supp : ∀ a b, G.Adj a b → a ∈ S
  deg : ∀ v ∈ S, 3 ≤ G.degree v
  notK4 : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G
  smaller : ∀ (G' : SimpleGraph V) (S' : Finset V), S'.card < S.card → S'.Nonempty →
    (∀ a b, G'.Adj a b → a ∈ S') → (∀ v ∈ S', 3 ≤ G'.degree v) →
    IsMinor (⊤ : SimpleGraph (Fin 4)) G'

namespace DiracCtx

variable {G : SimpleGraph V} {S : Finset V}

open Classical in
theorem deg' (H : DiracCtx G S) {v w : V} (h : G.Adj v w) : 3 ≤ G.degree v :=
  H.deg v (H.supp v w h)

open Classical in
theorem card_nbr (H : DiracCtx G S) {v w : V} (h : G.Adj v w) :
    3 ≤ (G.neighborFinset v).card := by
  rw [card_neighborFinset_eq_degree]; exact H.deg' h

open Classical in
theorem contract (H : DiracCtx G S) {x y : V} (hxy : G.Adj x y)
    (hmerge : 3 ≤ (((G.neighborFinset x ∪ G.neighborFinset y).erase x).erase y).card)
    (hcommon : ∀ z, G.Adj x z → G.Adj y z → 4 ≤ G.degree z) : False := by
  apply H.notK4
  refine isMinor_lift_contract (G' := contractG G x y) hxy (fun u v h => (contractG_adj.1 h).2)
    (by omega) ?_
  have hyS : y ∈ S := H.supp _ _ hxy.symm
  refine H.smaller _ (S.erase y) (Finset.card_erase_lt_of_mem hyS)
    ⟨x, Finset.mem_erase.2 ⟨hxy.ne, H.supp _ _ hxy⟩⟩ (contract_support hxy H.supp)
    (contract_degree 3 hxy H.deg hmerge hcommon)

open Classical in
theorem op (H : DiracCtx G S) {x a b c : V}
    (hx : ∀ t, G.Adj x t ↔ t = a ∨ t = b ∨ t = c)
    (hb : ∀ t, G.Adj b t → t = x ∨ t = a ∨ t = c)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : ¬ G.Adj a c) (hac' : a ≠ c)
    (ha4 : 4 ≤ G.degree a) (hc4 : 4 ≤ G.degree c) : False := by
  have hxa : G.Adj x a := (hx a).2 (Or.inl rfl)
  have hxb : G.Adj x b := (hx b).2 (Or.inr (Or.inl rfl))
  have hxc : G.Adj x c := (hx c).2 (Or.inr (Or.inr rfl))
  apply H.notK4
  refine isMinor_lift_contract (G' := opG G x b a c) (x := a) (y := x) hxa.symm
    (fun u v h => ?_) (by omega) ?_
  · obtain ⟨_, hux, _, hvx, _, h⟩ := opG_adj.1 h
    refine ⟨hux, hvx, ?_⟩
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, hxc⟩)
    · exact Or.inr (Or.inr ⟨rfl, hxc⟩)
  have hxS : x ∈ S := H.supp _ _ hxa
  have hbS : b ∈ S := H.supp _ _ hab.symm
  have hbx : b ≠ x := hxb.ne.symm
  have hS3 : ((S.erase x).erase b).card < S.card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hbx, hbS⟩), Finset.card_erase_of_mem hxS]
    have := Finset.card_pos.2 ⟨x, hxS⟩
    omega
  refine H.smaller _ ((S.erase x).erase b) hS3
    ⟨a, by simp [hab.ne, hxa.ne.symm, H.supp _ _ hab]⟩ (fun u v h => ?_) (fun v hv => ?_)
  · obtain ⟨_, hux, hub, _, _, h⟩ := opG_adj.1 h
    simp only [Finset.mem_erase]
    refine ⟨hub, hux, ?_⟩
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact H.supp _ _ h
    · exact H.supp _ _ hab
    · exact H.supp _ _ hbc.symm
  · simp only [Finset.mem_erase] at hv
    obtain ⟨hvb, hvx, hvS⟩ := hv
    have key : ∀ e e', (e = a ∧ e' = c ∨ e = c ∧ e' = a) → 4 ≤ G.degree e → G.Adj x e →
        G.Adj b e → ¬ G.Adj e e' → e ≠ e' → 3 ≤ (opG G x b a c).degree e := by
      intro e e' hee' he4 hxe hbe hne hne'
      have hsub : insert e' (((G.neighborFinset e).erase x).erase b) ⊆
          (opG G x b a c).neighborFinset e := by
        refine Finset.insert_subset ?_ fun t ht => ?_
        · rw [mem_neighborFinset, opG_adj]
          refine ⟨hne', hxe.ne.symm, hbe.ne.symm, ?_, ?_, Or.inr hee'⟩
          · rintro rfl; exact hne hxe.symm
          · rintro rfl; exact hne hbe.symm
        · simp only [Finset.mem_erase, mem_neighborFinset] at ht
          rw [mem_neighborFinset, opG_adj]
          exact ⟨ht.2.2.ne, hxe.ne.symm, hbe.ne.symm, ht.2.1, ht.1, Or.inl ht.2.2⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp [hne]),
        Finset.card_erase_of_mem (by simp [hbe.symm, hbx]),
        Finset.card_erase_of_mem (by simpa using hxe.symm), card_neighborFinset_eq_degree,
        card_neighborFinset_eq_degree] at h1
      omega
    by_cases hva : v = a
    · subst hva
      exact key v c (Or.inl ⟨rfl, rfl⟩) ha4 hxa hab.symm hac hac'
    by_cases hvc : v = c
    · subst hvc
      exact key v a (Or.inr ⟨rfl, rfl⟩) hc4 hxc hbc (fun h => hac h.symm) hac'.symm
    refine (H.deg v hvS).trans ?_
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    refine Finset.card_le_card fun t ht => ?_
    rw [mem_neighborFinset] at ht
    rw [mem_neighborFinset, opG_adj]
    refine ⟨ht.ne, hvx, hvb, ?_, ?_, Or.inl ht⟩
    · rintro rfl
      rcases (hx v).1 ht.symm with h | h | h <;> contradiction
    · rintro rfl
      rcases hb v ht.symm with h | h | h <;> contradiction

open Classical in
theorem step_nbr (H : DiracCtx G S) {x a b c : V}
    (hx : ∀ t, G.Adj x t ↔ t = a ∨ t = b ∨ t = c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.Adj a b ∨ G.Adj a c := by
  by_contra hn
  simp only [not_or] at hn
  have hxa : G.Adj x a := (hx a).2 (Or.inl rfl)
  have hxb : G.Adj x b := (hx b).2 (Or.inr (Or.inl rfl))
  have hxc : G.Adj x c := (hx c).2 (Or.inr (Or.inr rfl))
  obtain ⟨z, hz, hzx, -⟩ := exists_mem_ne_ne (H.card_nbr hxa.symm) x x
  rw [mem_neighborFinset] at hz
  have hzb : z ≠ b := by rintro rfl; exact hn.1 hz
  have hzc : z ≠ c := by rintro rfl; exact hn.2 hz
  refine H.contract hxa (three_le_card (p := b) (q := c) (r := z) ?_ ?_ ?_ hbc hzb.symm hzc.symm)
    (fun t hxt hat => ?_)
  · exact mem_merged.2 ⟨hab.symm, hxb.ne.symm, Or.inl hxb⟩
  · exact mem_merged.2 ⟨hac.symm, hxc.ne.symm, Or.inl hxc⟩
  · exact mem_merged.2 ⟨hz.ne.symm, hzx, Or.inr hz⟩
  · rcases (hx t).1 hxt with rfl | rfl | rfl
    · exact absurd hat (G.loopless.irrefl _)
    · exact absurd hat hn.1
    · exact absurd hat hn.2

open Classical in
theorem deg_four (H : DiracCtx G S) {x a b c : V}
    (hx : ∀ t, G.Adj x t ↔ t = a ∨ t = b ∨ t = c)
    (hb : ∀ t, G.Adj b t → t = x ∨ t = a ∨ t = c)
    (hab : G.Adj a b) (hac : ¬ G.Adj a c) : 4 ≤ G.degree a := by
  by_contra hlt
  have hxa : G.Adj x a := (hx a).2 (Or.inl rfl)
  have hxb : G.Adj x b := (hx b).2 (Or.inr (Or.inl rfl))
  obtain ⟨z, hz, hzx, hzb⟩ := exists_mem_ne_ne (H.card_nbr hab) x b
  rw [mem_neighborFinset] at hz
  have hzc : z ≠ c := by rintro rfl; exact hac hz
  have hNa : ∀ t, G.Adj a t → t = x ∨ t = b ∨ t = z := fun t ht =>
    eq_of_card_le_three (s := G.neighborFinset a)
      (by rw [card_neighborFinset_eq_degree]; omega) (by simpa using hxa.symm) (by simpa using hab)
      (by simpa using hz) hxb.ne hzx.symm hzb.symm (by simpa using ht)
  have hzx' : ¬ G.Adj z x := fun h => by
    rcases (hx z).1 h.symm with rfl | rfl | rfl
    · exact G.loopless.irrefl _ hz
    · exact hzb rfl
    · exact hzc rfl
  have hzb' : ¬ G.Adj z b := fun h => by
    rcases hb z h.symm with rfl | rfl | rfl
    · exact hzx rfl
    · exact G.loopless.irrefl _ hz
    · exact hzc rfl
  obtain ⟨w, hw, hwa, -⟩ := exists_mem_ne_ne (H.card_nbr hz.symm) a a
  rw [mem_neighborFinset] at hw
  have hwx : w ≠ x := by rintro rfl; exact hzx' hw
  have hwb : w ≠ b := by rintro rfl; exact hzb' hw
  refine H.contract hz (three_le_card (p := x) (q := b) (r := w) ?_ ?_ ?_ hxb.ne hwx.symm
    hwb.symm) (fun t hat hzt => ?_)
  · exact mem_merged.2 ⟨hzx.symm, hxa.ne, Or.inl hxa.symm⟩
  · exact mem_merged.2 ⟨hzb.symm, hab.ne.symm, Or.inl hab⟩
  · exact mem_merged.2 ⟨hw.ne.symm, hwa, Or.inr hw⟩
  · rcases hNa t hat with rfl | rfl | rfl
    · exact absurd hzt hzx'
    · exact absurd hzt hzb'
    · exact absurd hzt (G.loopless.irrefl _)

open Classical in
theorem center (H : DiracCtx G S) {x a b c : V}
    (hx : ∀ t, G.Adj x t ↔ t = a ∨ t = b ∨ t = c) (hab' : a ≠ b) (hac' : a ≠ c) (hbc' : b ≠ c)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : ¬ G.Adj a c) : False := by
  have hxa : G.Adj x a := (hx a).2 (Or.inl rfl)
  have hxb : G.Adj x b := (hx b).2 (Or.inr (Or.inl rfl))
  have hxc : G.Adj x c := (hx c).2 (Or.inr (Or.inr rfl))
  have hb3 : G.degree b ≤ 3 := by
    by_contra hb4
    obtain ⟨z, hz, hzx, hzb⟩ := exists_mem_ne_ne (H.card_nbr hab) x b
    rw [mem_neighborFinset] at hz
    have hzc : z ≠ c := by rintro rfl; exact hac hz
    refine H.contract hxa (three_le_card (p := b) (q := c) (r := z) ?_ ?_ ?_ hbc' hzb.symm
      hzc.symm) (fun t hxt hat => ?_)
    · exact mem_merged.2 ⟨hab'.symm, hxb.ne.symm, Or.inl hxb⟩
    · exact mem_merged.2 ⟨hac'.symm, hxc.ne.symm, Or.inl hxc⟩
    · exact mem_merged.2 ⟨hz.ne.symm, hzx, Or.inr hz⟩
    · rcases (hx t).1 hxt with rfl | rfl | rfl
      · exact absurd hat (G.loopless.irrefl _)
      · omega
      · exact absurd hat hac
  have hb : ∀ t, G.Adj b t → t = x ∨ t = a ∨ t = c := fun t ht =>
    eq_of_card_le_three (s := G.neighborFinset b) (by rw [card_neighborFinset_eq_degree]; omega)
      (by simpa using hxb.symm) (by simpa using hab.symm) (by simpa using hbc) hxa.ne hxc.ne hac'
      (by simpa using ht)
  have ha4 := H.deg_four hx hb hab hac
  have hc4 := H.deg_four (x := x) (a := c) (b := b) (c := a) (fun t => by rw [hx]; tauto)
    (fun t ht => by rcases hb t ht with h | h | h <;> tauto) hbc.symm (fun h => hac h.symm)
  exact H.op hx hb hab hbc hac hac' ha4 hc4

open Classical in
theorem false_of_deg_three (H : DiracCtx G S) {x : V} (hx3 : G.degree x = 3) : False := by
  obtain ⟨a, b, c, hab, hac, hbc, hN⟩ := Finset.card_eq_three.1
    ((card_neighborFinset_eq_degree G x).trans hx3)
  have hx : ∀ t, G.Adj x t ↔ t = a ∨ t = b ∨ t = c := fun t => by
    rw [← mem_neighborFinset, hN]; simp
  have hxa : G.Adj x a := (hx a).2 (Or.inl rfl)
  have hxb : G.Adj x b := (hx b).2 (Or.inr (Or.inl rfl))
  have hxc : G.Adj x c := (hx c).2 (Or.inr (Or.inr rfl))
  have ha := H.step_nbr hx hab hac hbc
  have hb := H.step_nbr (x := x) (a := b) (b := a) (c := c) (fun t => by rw [hx]; tauto)
    hab.symm hbc hac
  have hc := H.step_nbr (x := x) (a := c) (b := a) (c := b) (fun t => by rw [hx]; tauto)
    hac.symm hbc.symm hab
  by_cases h1 : G.Adj a b <;> by_cases h2 : G.Adj a c <;> by_cases h3 : G.Adj b c
  · exact H.notK4 (isMinor_K4_of_clique hxa hxb hxc h1 h2 h3)
  · exact H.center (x := x) (a := b) (b := a) (c := c) (fun t => by rw [hx]; tauto) hab.symm hbc
      hac h1.symm h2 h3
  · exact H.center hx hab hac hbc h1 h3 h2
  · exact absurd (hc.resolve_left (fun h => h2 h.symm)) (fun h => h3 h.symm)
  · exact H.center (x := x) (a := b) (b := c) (c := a) (fun t => by rw [hx]; tauto) hbc
      hab.symm hac.symm h3 h2.symm (fun h => h1 h.symm)
  · exact absurd (hb.resolve_left (fun h => h1 h.symm)) h3
  · exact absurd (ha.resolve_left h1) h2
  · exact absurd (ha.resolve_left h1) h2

end DiracCtx

open Classical in
theorem dirac_aux : ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n → S.Nonempty →
    (∀ a b, G.Adj a b → a ∈ S) → (∀ v ∈ S, 3 ≤ G.degree v) →
    IsMinor (⊤ : SimpleGraph (Fin 4)) G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro G S hn hS hsupp hdeg
  suffices ∀ m (G : SimpleGraph V), G.edgeFinset.card = m → (∀ a b, G.Adj a b → a ∈ S) →
      (∀ v ∈ S, 3 ≤ G.degree v) → IsMinor (⊤ : SimpleGraph (Fin 4)) G from
    this _ G rfl hsupp hdeg
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro G hm hsupp hdeg
  by_contra hK
  have H : DiracCtx G S := ⟨hsupp, hdeg, hK, fun G' S' hS' hne hsupp' hdeg' =>
    ihn S'.card (hn ▸ hS') G' S' rfl hne hsupp' hdeg'⟩
  have hM1 : ∀ u v, G.Adj u v → 4 ≤ G.degree u → 4 ≤ G.degree v → False := by
    intro u v huv hu hv
    apply hK
    refine isMinor_mono (G.deleteEdges_le {s(u, v)}) ?_
    refine ihm _ ?_ (G.deleteEdges {s(u, v)}) rfl
      (fun a b h => hsupp a b (deleteEdges_le _ h)) (fun w hw => ?_)
    · rw [← hm]
      refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun e he => ?_).2
        ⟨s(u, v), by simpa using huv, by simp [mem_edgeFinset, edgeSet_deleteEdges]⟩)
      simp only [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff] at he ⊢
      exact he.1
    · rw [← card_neighborFinset_eq_degree]
      by_cases hwu : w = u
      · subst hwu
        refine le_trans ?_ (Finset.card_le_card (s := (G.neighborFinset w).erase v) ?_)
        · rw [Finset.card_erase_of_mem (by simpa using huv), card_neighborFinset_eq_degree]
          omega
        · intro t ht
          simp only [Finset.mem_erase, mem_neighborFinset] at ht
          rw [mem_neighborFinset, deleteEdges_adj]
          refine ⟨ht.2, ?_⟩
          simp only [Set.mem_singleton_iff, Sym2.congr_right]
          exact ht.1
      by_cases hwv : w = v
      · subst hwv
        refine le_trans ?_ (Finset.card_le_card (s := (G.neighborFinset w).erase u) ?_)
        · rw [Finset.card_erase_of_mem (by simpa using huv.symm), card_neighborFinset_eq_degree]
          omega
        · intro t ht
          simp only [Finset.mem_erase, mem_neighborFinset] at ht
          rw [mem_neighborFinset, deleteEdges_adj]
          refine ⟨ht.2, ?_⟩
          simp only [Set.mem_singleton_iff, Sym2.eq_swap (a := u), Sym2.congr_right]
          exact ht.1
      · refine le_trans ?_ (Finset.card_le_card (s := G.neighborFinset w) ?_)
        · rw [card_neighborFinset_eq_degree]; exact hdeg w hw
        · intro t ht
          rw [mem_neighborFinset] at ht
          rw [mem_neighborFinset, deleteEdges_adj]
          refine ⟨ht, ?_⟩
          simp only [Set.mem_singleton_iff, Sym2.eq_iff]
          tauto
  obtain ⟨v, hv⟩ := hS
  obtain ⟨u, hu, -⟩ := exists_mem_ne_ne (s := G.neighborFinset v)
    (by rw [card_neighborFinset_eq_degree]; exact hdeg v hv) v v
  rw [mem_neighborFinset] at hu
  by_cases hv3 : G.degree v = 3
  · exact H.false_of_deg_three hv3
  by_cases hu3 : G.degree u = 3
  · exact H.false_of_deg_three hu3
  have := hdeg v hv
  have := H.deg' hu.symm
  exact hM1 v u hu (by omega) (by omega)

end Dirac

section Removal


variable [Fintype V]

open Classical in
theorem k3_aux : ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n → S.Nonempty →
    (∀ a b, G.Adj a b → a ∈ S) → (∀ v ∈ S, 2 ≤ G.degree v) →
    IsMinor (⊤ : SimpleGraph (Fin 3)) G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro G S hn hS hsupp hdeg
  obtain ⟨x, hx⟩ := hS
  have hcx : 1 < (G.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree]; have := hdeg x hx; omega
  obtain ⟨y, hy⟩ := Finset.card_pos.1 (show 0 < (G.neighborFinset x).card by omega)
  rw [mem_neighborFinset] at hy
  by_cases hcom : ∃ z, G.Adj x z ∧ G.Adj y z
  · obtain ⟨z, hxz, hyz⟩ := hcom
    refine isMinor_of_clique ![x, y, z] fun i j h => ?_
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl h |
      simp [hy, hxz, hyz, hy.symm, hxz.symm, hyz.symm]
  simp only [not_exists, not_and] at hcom
  obtain ⟨p, hp, hpy⟩ := Finset.exists_mem_ne hcx y
  rw [mem_neighborFinset] at hp
  have hyS : y ∈ S := hsupp _ _ hy.symm
  have hcy : 1 < (G.neighborFinset y).card := by
    rw [card_neighborFinset_eq_degree]; have := hdeg y hyS; omega
  obtain ⟨q, hq, hqx⟩ := Finset.exists_mem_ne hcy x
  rw [mem_neighborFinset] at hq
  have hpq : p ≠ q := by rintro rfl; exact hcom p hp hq
  refine isMinor_lift_contract (G' := contractG G x y) hy (fun u v h => (contractG_adj.1 h).2)
    (by omega) ?_
  refine ihn _ (hn ▸ Finset.card_erase_lt_of_mem hyS) _ (S.erase y) rfl
    ⟨x, Finset.mem_erase.2 ⟨hy.ne, hx⟩⟩ (contract_support hy hsupp)
    (contract_degree 2 hy hdeg ?_ (fun z hxz hyz => absurd hyz (hcom z hxz)))
  refine Finset.one_lt_card.2 ⟨p, ?_, q, ?_, hpq⟩
  · exact mem_merged.2 ⟨hpy, hp.ne.symm, Or.inl hp⟩
  · exact mem_merged.2 ⟨hq.ne.symm, hqx, Or.inr hq⟩

open Classical in
theorem exists_low_deg_K4 (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty)
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) :
    ∃ v ∈ S, G.degree v < 3 := by
  by_contra hc
  simp only [not_exists, not_and, not_lt] at hc
  exact h (dirac_aux _ G S rfl hS hsupp hc)

open Classical in
theorem exists_low_deg_K3 (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty)
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 3)) G) :
    ∃ v ∈ S, G.degree v < 2 := by
  by_contra hc
  simp only [not_exists, not_and, not_lt] at hc
  exact h (k3_aux _ G S rfl hS hsupp hc)

open Classical in
theorem edges_aux : ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n → 2 ≤ n →
    (∀ a b, G.Adj a b → a ∈ S) → ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G →
    G.edgeFinset.card + 3 ≤ 2 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro G S hn h2 hsupp hK
  obtain ⟨v, hv, hdv⟩ := exists_low_deg_K4 G S (Finset.card_pos.1 (by omega)) hsupp hK
  obtain ⟨G', hG'⟩ : ∃ G', G' = G.deleteIncidenceSet v := ⟨_, rfl⟩
  have hE := card_edges_deleteIncidenceSet G G' v hG'
  have hK' : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G' :=
    fun h => hK (isMinor_mono (hG' ▸ deleteIncidenceSet_le' G v) h)
  have hsupp' : ∀ a b, G'.Adj a b → a ∈ S.erase v := by
    subst hG'; exact deleteIncidenceSet_supp hsupp
  have hcard : (S.erase v).card = n - 1 := by rw [Finset.card_erase_of_mem hv, hn]
  by_cases hn2 : n = 2
  · subst hn2
    have hE0 : G'.edgeFinset.card = 0 := by
      refine Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun e he => ?_)
      induction e using Sym2.ind with
      | _ a b =>
        have hab : G'.Adj a b := by simpa using he
        have ha := hsupp' a b hab
        have hb := hsupp' b a hab.symm
        exact hab.ne (Finset.card_le_one.1 (by omega) a ha b hb)
    have hdeg1 : G.degree v ≤ 1 := by
      rw [← card_neighborFinset_eq_degree]
      refine (Finset.card_le_card fun t ht => ?_).trans hcard.le
      rw [mem_neighborFinset] at ht
      exact Finset.mem_erase.2 ⟨ht.ne.symm, hsupp _ _ ht.symm⟩
    omega
  · have := ihn (n - 1) (by omega) G' (S.erase v) hcard (by omega) hsupp' hK'
    omega

open Classical in
theorem color_aux (k : ℕ) (hk : 1 ≤ k) (P : SimpleGraph V → Prop)
    (hP : ∀ G G' : SimpleGraph V, G' ≤ G → P G → P G')
    (hlow : ∀ (G : SimpleGraph V) (S : Finset V), S.Nonempty → (∀ a b, G.Adj a b → a ∈ S) →
      P G → ∃ v ∈ S, G.degree v < k) :
    ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n →
      (∀ a b, G.Adj a b → a ∈ S) → P G → G.Colorable k := by
  intro n
  induction n with
  | zero =>
    intro G S hn hsupp _
    rw [Finset.card_eq_zero] at hn
    subst hn
    exact ⟨Coloring.mk (fun _ => ⟨0, hk⟩) fun h => absurd (hsupp _ _ h) (Finset.notMem_empty _)⟩
  | succ n ih =>
    intro G S hn hsupp hPG
    obtain ⟨v, hv, hdv⟩ := hlow G S (Finset.card_pos.1 (by omega)) hsupp hPG
    obtain ⟨C'⟩ := ih (G.deleteIncidenceSet v) (S.erase v)
      (by rw [Finset.card_erase_of_mem hv, hn]; rfl) (deleteIncidenceSet_supp hsupp)
      (hP _ _ (deleteIncidenceSet_le' G v) hPG)
    obtain ⟨col, -, hcol⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := (G.neighborFinset v).image C') (t := Finset.univ) (by
        rw [Finset.card_univ, Fintype.card_fin]
        exact Finset.card_image_le.trans_lt ((card_neighborFinset_eq_degree G v).trans_lt hdv))
    refine ⟨Coloring.mk (fun u => if u = v then col else C' u) fun {a b} hab => ?_⟩
    by_cases ha : a = v
    · subst ha
      have hb : b ≠ a := hab.ne.symm
      simp only [hb, ite_true, ite_false]
      exact fun h => hcol (Finset.mem_image.2 ⟨b, by simpa using hab, h.symm⟩)
    by_cases hb : b = v
    · subst hb
      simp only [ha, ite_true, ite_false]
      exact fun h => hcol (Finset.mem_image.2 ⟨a, by simpa using hab.symm, h⟩)
    simp only [ha, hb, ite_false]
    exact C'.valid (deleteIncidenceSet_adj.2 ⟨hab, ha, hb⟩)

end Removal

/-- **Mader's theorem (1967).** A nonempty finite graph whose average degree is at least
`2 ^ (r - 2)`, i.e. `2 ^ r · |V| ≤ 8 · |E|`, has the complete graph `K_r` as a minor. -/
theorem mader [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (h : 2 ^ r * Fintype.card V ≤ 8 * G.edgeFinset.card) :
    IsMinor (⊤ : SimpleGraph (Fin r)) G := by
  classical
  refine mader_aux r G Finset.univ Finset.univ_nonempty (fun _ _ _ => Finset.mem_univ _) ?_
  convert h using 3
  · exact Finset.card_univ
  · ext e; simp

/-- **Dirac (1952).** A nonempty finite graph without a `K₄` minor has a vertex of degree at most
two. -/
theorem exists_degree_le_two [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) : ∃ v, G.degree v ≤ 2 := by
  classical
  obtain ⟨v, -, hv⟩ := exists_low_deg_K4 G Finset.univ Finset.univ_nonempty
    (fun _ _ _ => Finset.mem_univ _) h
  refine ⟨v, ?_⟩
  convert Nat.le_of_lt_succ hv using 1
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  congr 1; ext; simp

/-- A finite graph on `n ≥ 2` vertices without a `K₄` minor has at most `2n - 3` edges. -/
theorem card_edgeFinset_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) :
    G.edgeFinset.card + 3 ≤ 2 * Fintype.card V := by
  classical
  have := edges_aux _ G Finset.univ rfl (by rwa [Finset.card_univ])
    (fun _ _ _ => Finset.mem_univ _) h
  convert this using 3
  · ext e; simp
  · exact Finset.card_univ.symm

/-- **Hadwiger's conjecture for `t = 3`.** A finite graph without a `K₃` minor (a forest) is
2-colourable. -/
theorem colorable_two_of_not_isMinor_K3 [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 3)) G) : G.Colorable 2 := by
  have := Fintype.ofFinite V
  exact color_aux 2 (by norm_num) (fun G => ¬ IsMinor (⊤ : SimpleGraph (Fin 3)) G)
    (fun _ _ hle hG h' => hG (isMinor_mono hle h')) exists_low_deg_K3 _ G Finset.univ rfl
    (fun _ _ _ => Finset.mem_univ _) h

/-- **Hadwiger's conjecture for `t = 4` (Hadwiger 1943, Dirac 1952).** A finite graph without a
`K₄` minor is 3-colourable. -/
theorem colorable_three_of_not_isMinor_K4 [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) : G.Colorable 3 := by
  have := Fintype.ofFinite V
  exact color_aux 3 (by norm_num) (fun G => ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G)
    (fun _ _ hle hG h' => hG (isMinor_mono hle h')) exists_low_deg_K4 _ G Finset.univ rfl
    (fun _ _ _ => Finset.mem_univ _) h

end CliqueMinors
