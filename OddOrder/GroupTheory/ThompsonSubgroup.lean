/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import OddOrder.GroupTheory.ElementaryAbelian

/-!
# Thompson Subgroup `J(P)`

`OddOrder.GroupTheory` shared module: Thompson subgroup `J(P)` の定義と基本性質.

Isaacs, *Finite Group Theory* (2008), Chapter 7 (pp. 201-202) の中核 def.
mathlib v4.29.1 に未収載 (`Thompson` 名はゼロ件). Ch.7, BG App.A, BG App.B (Puig 代替),
BG §6, §8, §9 (Uniqueness Theorem) で繰り返し使われる shared concept として独立 module 化.

## Main definitions

* `Subgroup.maxElemAbelianIn P p`: 部分群 `P` 内の `p`-elementary abelian 部分群のうち
  最大位数のものの集合 (Isaacs L3727 の `E(P)`).
* `Subgroup.thompsonJ P p`: Thompson subgroup `J(P) = ⟨E(P)⟩`
  (Isaacs L3727, Aschbacher §32, BG L5586 の記法).

## Design notes

* Isaacs の `J(P)` は **largest order** の elementary abelian (Aschbacher 系). Thompson
  原版は **largest rank** (元の Thompson 1968) で、両者は P が abelian non-elementary
  のとき異なりうる. 本 module は Isaacs/Aschbacher 版を採用.
* `p` は引数で取る (`P ∈ Syl_p(G)` 文脈で外側固定が自然).
* `[Finite G]` は def 段階では不要だが, 主要結果 (Thm 7.2 等) では必須.

## Forward references

* `Subgroup.thompsonJ_le`: `J(P) ≤ P`.
* **Isaacs Thm 7.2** (`thompsonJ_eq_of_le_of_le`): `J(P) ≤ Q ≤ P ⇒ J(Q) = J(P)`.
  特に `J(P)` は `Q` 内 characteristic.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- `[Finite G]` のとき, `Subgroup G` 自体も有限. `Subgroup G ↪ Set G` 経由. -/
instance instFiniteSubgroupOfFinite [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

/-- The trivial subgroup `⊥` is `p`-elementary abelian for any `p`. -/
theorem bot_isElementaryAbelian (p : ℕ) :
    (⊥ : Subgroup G).IsElementaryAbelian p := by
  refine ⟨?_, ?_⟩
  · intro x y
    exact Subsingleton.elim _ _
  · intro x
    have hx : x = 1 := Subsingleton.elim x 1
    rw [hx, one_pow]

/-- **Maximum-order elementary abelian subgroups of `P`** (Isaacs Ch.7 L3727 の `E(P)`).

`E(P) = {E ≤ P | E は p-elementary abelian で, 任意の elem-ab subgroup F ≤ P について
|F| ≤ |E|}`. -/
def maxElemAbelianIn (P : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {E | E ≤ P ∧ E.IsElementaryAbelian p ∧
       ∀ F : Subgroup G, F ≤ P → F.IsElementaryAbelian p → Nat.card F ≤ Nat.card E}

/-- **Thompson subgroup** `J(P) = ⟨E(P)⟩` (Isaacs Ch.7 def, p.201).

`P` 内の最大位数 elementary abelian 部分群すべての (Subgroup G 内での) 上限. -/
def thompsonJ (P : Subgroup G) (p : ℕ) : Subgroup G :=
  ⨆ E ∈ maxElemAbelianIn P p, E

/-- `J(P) ≤ P`: Thompson subgroup は `P` の部分群. -/
theorem thompsonJ_le (P : Subgroup G) (p : ℕ) : thompsonJ P p ≤ P := by
  refine iSup_le fun E => iSup_le fun hE => ?_
  exact hE.1

/-- `E ∈ maxElemAbelianIn P p` の生成元は `J(P)` に含まれる. -/
theorem le_thompsonJ_of_mem_maxElemAbelianIn {P E : Subgroup G} {p : ℕ}
    (hE : E ∈ maxElemAbelianIn P p) : E ≤ thompsonJ P p :=
  le_iSup_of_le E (le_iSup_of_le hE le_rfl)

/-- `maxElemAbelianIn` の単調性 (片方向): max-order subgroup の "最大値" は
`P` を縮める方向と整合しない一般論はないが, **「`J(P) ≤ Q ≤ P` ⇒ Q 内 max は P 内 max
と一致」** という Isaacs Thm 7.2 の核となる性質を別途 `thompsonJ_eq_of_le_of_le` で示す. -/
theorem mem_maxElemAbelianIn_of_le {P Q E : Subgroup G} {p : ℕ}
    (hQP : Q ≤ P) (hE : E ∈ maxElemAbelianIn Q p) :
    E.IsElementaryAbelian p ∧ E ≤ P :=
  ⟨hE.2.1, hE.1.trans hQP⟩

/-- `[Finite G]` のもとで `maxElemAbelianIn P p` は非空 (`⊥` が常に元). -/
theorem maxElemAbelianIn_nonempty [Finite G] (P : Subgroup G) (p : ℕ) :
    (maxElemAbelianIn P p).Nonempty := by
  -- S = {F ≤ P | F elem ab} は有限・非空 (⊥ ∈ S).
  have hUniv : (Set.univ : Set (Subgroup G)).Finite := Set.finite_univ
  have hS_fin : {F : Subgroup G | F ≤ P ∧ F.IsElementaryAbelian p}.Finite :=
    hUniv.subset (fun _ _ => Set.mem_univ _)
  have hS_ne : {F : Subgroup G | F ≤ P ∧ F.IsElementaryAbelian p}.Nonempty :=
    ⟨⊥, bot_le, bot_isElementaryAbelian p⟩
  -- 最大位数の元 E を取得.
  obtain ⟨E, hE_S, hE_max⟩ :=
    Set.exists_max_image
      {F : Subgroup G | F ≤ P ∧ F.IsElementaryAbelian p}
      (fun F => Nat.card F) hS_fin hS_ne
  refine ⟨E, hE_S.1, hE_S.2, ?_⟩
  intro F hF_P hF_el
  exact hE_max F ⟨hF_P, hF_el⟩

/-- **Isaacs Thm 7.2** (J(P) は Q 内でも変わらない).

`J(P) ≤ Q ≤ P` のとき `J(Q) = J(P)`. 系として **`J(P)` は `Q` 内 characteristic**
(`J(Q)` は Q 内 characteristic で自動的に従う性質, 別途).

証明: `maxElemAbelianIn Q p = maxElemAbelianIn P p` を示す.
- `Q ⊆ P` 側: `E ∈ maxElemAbelianIn P p` ⇒ `E ≤ J(P) ≤ Q`, `Q` 内でも max (任意の
  `F ≤ Q ≤ P` elem ab で `|F| ≤ |E|`).
- `P ⊆ Q` 側: `E₀ ∈ maxElemAbelianIn P p` を fix し `E₀ ≤ Q`. `E ∈ maxElemAbelianIn Q p`
  なら `|E₀| ≤ |E|` (E max in Q) かつ `|E| ≤ |E₀|` (E ≤ P, E₀ max in P) で位数一致.
  位数一致から `E` も `P` 内 max. -/
theorem thompsonJ_eq_of_le_of_le [Finite G] {P Q : Subgroup G} {p : ℕ}
    (hJQ : thompsonJ P p ≤ Q) (hQP : Q ≤ P) :
    thompsonJ Q p = thompsonJ P p := by
  apply le_antisymm
  · -- J(Q) ≤ J(P)
    refine iSup_le fun E => iSup_le fun hE_Q => ?_
    -- E max in Q.  E ∈ maxElemAbelianIn P p を示す.
    obtain ⟨E₀, hE₀_P, hE₀_el, hE₀_max⟩ := maxElemAbelianIn_nonempty P p
    have hE₀_le_J : E₀ ≤ thompsonJ P p :=
      le_thompsonJ_of_mem_maxElemAbelianIn ⟨hE₀_P, hE₀_el, hE₀_max⟩
    have hE₀_Q : E₀ ≤ Q := hE₀_le_J.trans hJQ
    have hcard_E₀_le_E : Nat.card E₀ ≤ Nat.card E := hE_Q.2.2 E₀ hE₀_Q hE₀_el
    have hE_P : E ≤ P := hE_Q.1.trans hQP
    have hcard_E_le_E₀ : Nat.card E ≤ Nat.card E₀ := hE₀_max E hE_P hE_Q.2.1
    have hcard_eq : Nat.card E = Nat.card E₀ := le_antisymm hcard_E_le_E₀ hcard_E₀_le_E
    apply le_thompsonJ_of_mem_maxElemAbelianIn
    refine ⟨hE_P, hE_Q.2.1, ?_⟩
    intro F hF_P hF_el
    calc Nat.card F
        ≤ Nat.card E₀ := hE₀_max F hF_P hF_el
      _ = Nat.card E := hcard_eq.symm
  · -- J(P) ≤ J(Q)
    refine iSup_le fun E => iSup_le fun hE_P => ?_
    have hE_le_J : E ≤ thompsonJ P p :=
      le_thompsonJ_of_mem_maxElemAbelianIn hE_P
    have hE_Q : E ≤ Q := hE_le_J.trans hJQ
    apply le_thompsonJ_of_mem_maxElemAbelianIn
    refine ⟨hE_Q, hE_P.2.1, ?_⟩
    intro F hF_Q hF_el
    exact hE_P.2.2 F (hF_Q.trans hQP) hF_el

/-- **`J(P) ≠ ⊥` for a nontrivial finite `p`-group `P`**.

A nontrivial `p`-group contains an element of order `p` (Cauchy), generating a
cyclic — hence `p`-elementary abelian — subgroup of order `p`.  Thus the
maximum-order elementary abelian subgroup of `P` has order `≥ p > 1`, so
`J(P) ≠ ⊥`. -/
theorem thompsonJ_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP_pgroup : IsPGroup p ↥P) (hP_ne_bot : P ≠ ⊥) :
    thompsonJ P p ≠ ⊥ := by
  classical
  -- A maximum-order elementary abelian subgroup `E` of `P` exists.
  obtain ⟨E, hE_le, hE_el, hE_max⟩ := maxElemAbelianIn_nonempty P p
  -- `p ∣ |P|` (nontrivial `p`-group), so there is an order-`p` element `x ∈ P`.
  have hp_dvd : p ∣ Nat.card ↥P := by
    obtain ⟨n, hn⟩ := hP_pgroup.exists_card_eq
    have hn_pos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h
      · exfalso
        rw [h0, pow_zero] at hn
        exact hP_ne_bot (Subgroup.card_eq_one.mp hn)
      · exact h
    rw [hn]; exact dvd_pow_self p hn_pos.ne'
  obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  -- `C := zpowers x.val ≤ P` is `p`-elementary abelian of order `p`.
  set C : Subgroup G := Subgroup.zpowers (x : G) with hC_def
  have hxG_ord : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx_ord]
  have hC_le_P : C ≤ P := by
    rw [hC_def]
    exact (Subgroup.zpowers_le).mpr x.2
  have hC_card : Nat.card ↥C = p := by rw [hC_def, Nat.card_zpowers, hxG_ord]
  have hC_el : C.IsElementaryAbelian p := by
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · -- `C = zpowers x` is commutative: `↑a, ↑b` are powers of `x`, which commute.
      apply Subtype.ext
      have ha : (a : G) ∈ Subgroup.zpowers (x : G) := a.2
      have hb : (b : G) ∈ Subgroup.zpowers (x : G) := b.2
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
      simp only [Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, add_comm]
    · -- every element of `C` has order dividing `p`, so `a ^ p = 1`.
      have hdvd : orderOf a ∣ p := by
        rw [← hC_card]; exact _root_.orderOf_dvd_natCard a
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
  -- `|C| = p ≤ |E|`, so `E ≠ ⊥`, and `E ≤ J(P)`.
  have hp_le_E : p ≤ Nat.card ↥E := hC_card ▸ hE_max C hC_le_P hC_el
  have hE_ne_bot : E ≠ ⊥ := by
    intro hbot
    rw [hbot] at hp_le_E
    simp only [Subgroup.card_bot] at hp_le_E
    exact (Fact.out (p := p.Prime)).one_lt.not_ge hp_le_E
  have hE_le_J : E ≤ thompsonJ P p :=
    le_thompsonJ_of_mem_maxElemAbelianIn ⟨hE_le, hE_el, hE_max⟩
  intro hJ_bot
  rw [hJ_bot, le_bot_iff] at hE_le_J
  exact hE_ne_bot hE_le_J

/-- **`J` commutes with injective images**: for an injective homomorphism
`f : G →* N` and a subgroup `P ≤ G`, `J(f(P)) = f(J(P))`.

The maximum-order elementary abelian subgroups of `f(P)` are exactly the
`f`-images of those of `P` (injectivity preserves both the elementary-abelian
property and cardinality, and every subgroup of `f(P)` is `f(its preimage)`).

Used in §7D Step 8 (Isaacs Thm 7.8) to relate `J` of a Sylow of `M` computed
inside `↥M` versus inside the ambient group. -/
theorem thompsonJ_map_of_injective [Finite G] {N : Type*} [Group N]
    {f : G →* N} (hf : Function.Injective f) (P : Subgroup G) (p : ℕ) :
    thompsonJ (P.map f) p = (thompsonJ P p).map f := by
  -- A subgroup `E ≤ P.map f` is the image of `E.comap f ≤ P`, with equal card and
  -- elementary-abelian status preserved.
  have key_comap : ∀ E : Subgroup N, E ∈ maxElemAbelianIn (P.map f) p →
      E.comap f ∈ maxElemAbelianIn P p ∧ (E.comap f).map f = E := by
    intro E hE
    obtain ⟨hE_le, hE_el, hE_max⟩ := hE
    -- `E ≤ P.map f ≤ range f`, so `(E.comap f).map f = E`.
    have hE_le_range : E ≤ f.range := hE_le.trans (Subgroup.map_le_range f P)
    have hmap_comap : (E.comap f).map f = E :=
      Subgroup.map_comap_eq_self hE_le_range
    refine ⟨⟨?_, ?_, ?_⟩, hmap_comap⟩
    · -- `E.comap f ≤ P`.
      rw [← Subgroup.comap_map_eq_self_of_injective hf P]
      exact Subgroup.comap_mono hE_le
    · -- `E.comap f` elementary abelian: its image `E` is, and `f` injective.
      have hmap_el : ((E.comap f).map f).IsElementaryAbelian p := by
        rw [hmap_comap]; exact hE_el
      exact hmap_el.of_map hf
    · -- Max-order: any elem-ab `F ≤ P` has `|F| = |F.map f| ≤ |E| = |E.comap f|`.
      intro F hF_P hF_el
      have hFmap_le : F.map f ≤ P.map f := Subgroup.map_mono hF_P
      have hFmap_el : (F.map f).IsElementaryAbelian p :=
        Subgroup.IsElementaryAbelian.map hf hF_el
      have hcard_F : Nat.card (F.map f) = Nat.card F := Subgroup.card_map_of_injective hf
      have hcard_E : Nat.card E = Nat.card (E.comap f) := by
        conv_lhs => rw [← hmap_comap]
        exact Subgroup.card_map_of_injective hf
      have hstep : Nat.card (F.map f) ≤ Nat.card E := hE_max (F.map f) hFmap_le hFmap_el
      rw [← hcard_E, ← hcard_F]; exact hstep
  -- The image of a max elem-ab subgroup of `P` is a max elem-ab subgroup of `P.map f`.
  have key_map : ∀ E : Subgroup G, E ∈ maxElemAbelianIn P p →
      E.map f ∈ maxElemAbelianIn (P.map f) p := by
    intro E hE
    obtain ⟨hE_le, hE_el, hE_max⟩ := hE
    refine ⟨Subgroup.map_mono hE_le, Subgroup.IsElementaryAbelian.map hf hE_el, ?_⟩
    -- Max-order in `P.map f`: any elem-ab `F ≤ P.map f` is `(F.comap f).map f`,
    -- and `F.comap f ≤ P` elem-ab, so `|F| = |F.comap f| ≤ |E| = |E.map f|`.
    intro F hF_le hF_el
    have hF_le_range : F ≤ f.range := hF_le.trans (Subgroup.map_le_range f P)
    have hF_mapcomap : (F.comap f).map f = F := Subgroup.map_comap_eq_self hF_le_range
    have hFcomap_le : F.comap f ≤ P := by
      rw [← Subgroup.comap_map_eq_self_of_injective hf P]; exact Subgroup.comap_mono hF_le
    have hFcomap_el : (F.comap f).IsElementaryAbelian p := by
      have hmap_el : ((F.comap f).map f).IsElementaryAbelian p := by
        rw [hF_mapcomap]; exact hF_el
      exact hmap_el.of_map hf
    have hcard_F : Nat.card F = Nat.card (F.comap f) := by
      conv_lhs => rw [← hF_mapcomap]
      exact Subgroup.card_map_of_injective hf
    have hcard_E : Nat.card (E.map f) = Nat.card E := Subgroup.card_map_of_injective hf
    calc Nat.card F = Nat.card (F.comap f) := hcard_F
      _ ≤ Nat.card E := hE_max (F.comap f) hFcomap_le hFcomap_el
      _ = Nat.card (E.map f) := hcard_E.symm
  -- Combine the two correspondences.
  apply le_antisymm
  · -- `J(P.map f) ≤ (J P).map f`.
    refine iSup_le fun E => iSup_le fun hE => ?_
    obtain ⟨hEcomap_mem, hmapcomap⟩ := key_comap E hE
    rw [← hmapcomap]
    exact Subgroup.map_mono (le_thompsonJ_of_mem_maxElemAbelianIn hEcomap_mem)
  · -- `(J P).map f ≤ J(P.map f)`: flip to `J P ≤ comap` and use `iSup_le`.
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun E => iSup_le fun hE => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_thompsonJ_of_mem_maxElemAbelianIn (key_map E hE)

/-- **Conjugation by a normalizing element fixes `J(P)`**: if `g ∈ N(P)`, then
`g · J(P) · g⁻¹ = J(P)` (as `(thompsonJ P p).map (conj g) = thompsonJ P p`).

`J` commutes with the injective automorphism `conj g` (`thompsonJ_map_of_injective`),
and `g ∈ N(P)` gives `P.map (conj g) = P`. -/
theorem thompsonJ_map_conj_eq_of_mem_normalizer [Finite G] {p : ℕ} {P : Subgroup G}
    {g : G} (hg : g ∈ Subgroup.normalizer P) :
    (thompsonJ P p).map (MulAut.conj g).toMonoidHom = thompsonJ P p := by
  have hg_iff : ∀ n, n ∈ P ↔ g * n * g⁻¹ ∈ P := Subgroup.mem_normalizer_iff.mp hg
  have hP_conj : P.map (MulAut.conj g).toMonoidHom = P := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hg_iff z).mp hz
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, ?_⟩
      · have hmem : g * (g⁻¹ * y * g) * g⁻¹ ∈ P := by
          have heq : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
          rw [heq]; exact hy
        exact (hg_iff (g⁻¹ * y * g)).mpr hmem
      · change g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  rw [← thompsonJ_map_of_injective hinj P p, hP_conj]

/-! ### `J(P)` is characteristic in `P`

Isaacs Thm 7.2 (`thompsonJ_eq_of_le_of_le`) gives the stronger statement that `J(P)` is
characteristic in every intermediate `J(P) ≤ Q ≤ P`; the bare characteristic-in-`P`
property is what the local hypotheses of Isaacs Thm 6.23 quantify over, so it is recorded
here in the `Subgroup ↥P` form that `Subgroup.Characteristic` expects. -/

/-- Computing `J` inside `↥P` and pushing forward along `P.subtype` agrees with computing
`J(P)` in the ambient group. -/
theorem thompsonJ_top_map_subtype [Finite G] (P : Subgroup G) (p : ℕ) :
    (thompsonJ (⊤ : Subgroup ↥P) p).map P.subtype = thompsonJ P p := by
  rw [← thompsonJ_map_of_injective P.subtype_injective (⊤ : Subgroup ↥P) p,
    ← MonoidHom.range_eq_map, P.range_subtype]

/-- `J(P)`, viewed inside `↥P`, is `J` of the whole group `↥P`. -/
theorem thompsonJ_subgroupOf_self [Finite G] (P : Subgroup G) (p : ℕ) :
    (thompsonJ P p).subgroupOf P = thompsonJ (⊤ : Subgroup ↥P) p := by
  rw [← thompsonJ_top_map_subtype P p, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective]

/-- **`J(H)` is characteristic** (top form): every automorphism of `H` permutes the
maximum-order elementary abelian subgroups of `H`, hence fixes their join. -/
instance thompsonJ_top_characteristic [Finite G] (p : ℕ) :
    (thompsonJ (⊤ : Subgroup G) p).Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun ϕ => ?_
  rw [← thompsonJ_map_of_injective ϕ.injective (⊤ : Subgroup G) p]
  congr 1
  simp

/-- **`J(P)` is characteristic in `P`** (Isaacs Ch.7, p. 201): a special case of Thm 7.2,
stated in the `Subgroup ↥P` form used by the local hypotheses of Isaacs Thm 6.23. -/
instance thompsonJ_subgroupOf_characteristic [Finite G] (P : Subgroup G) (p : ℕ) :
    ((thompsonJ P p).subgroupOf P).Characteristic := by
  rw [thompsonJ_subgroupOf_self]
  infer_instance

end Subgroup
