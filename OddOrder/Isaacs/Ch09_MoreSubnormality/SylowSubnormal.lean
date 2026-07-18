/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IsSubnormal
import Mathlib.GroupTheory.Sylow

/-!
# Isaacs Ch. 9 — Lemma 9.31: Sylow subgroups meet subnormal subgroups in Sylow subgroups (p. 291)

Isaacs, *Finite Group Theory* (AMS GSM 92), §9D, **Lemma 9.31**:

> `S ◁◁ G` (subnormal) と `P ∈ Syl_p(G)` に対し `P ∩ S ∈ Syl_p(S)`.

⚠ 仮定は **subnormal** (`S ◁◁ G`)。Nougat 抽出 (`.mmd`) は `⊲⊲` を `⊲` に潰すので
原文では normal に見えるが, PDF p.291 で `S \lhd\lhd G` を確認済
(証明が「`S ⊆ M < G` with `M ◁ G` をとって `|G|` の帰納」であることとも整合).

## 実装方針

「`P ∩ S` が `S` の Sylow」は `IsPGroup` 部分が自明なので, 内容は**指数が `p` と互いに素**
の一点に集約される。よって主張を

`¬ p ∣ (↑P ⊓ S).relIndex S`

の形で証明し, 束ねた `Sylow p ↥S` は `IsPGroup.toSylow` で作る。

証明は書籍の `|G|`-帰納ではなく **`IsSubnormal` の帰納型そのものに沿った構造帰納**
(`induction hS with | top | step`) で行う — mathlib の `Subgroup.IsSubnormal` は
「`⊤` か, または subnormal な `K` があって `H ◁ K`」という inductive predicate なので,
書籍の「`S ⊆ M ◁ G` をとって降りる」がそのまま constructor になっている。
各段は normal 段 (`not_dvd_relIndex_inf_of_normal`) に帰着する。

normal 段は第二同型定理の指数版:
`|N : N ∩ P| = |NP : P|` が `|G : P|` を割る, を mathlib の `relIndex` 算術
(`inf_relIndex_left`, `relIndex_sup_left`, `relIndex_mul_relIndex`,
`relIndex_dvd_index_of_le`) で組む。
-/

namespace OddOrder.Isaacs.Ch09

variable {G : Type*} [Group G]

section /- 9D: Lemma 9.31 (p. 291) -/

/-- **Isaacs Lemma 9.31 の normal 段**: `N ⊴ G`, `P ∈ Syl_p(G)` ⇒ `|N : N ∩ P|` は `p` と互いに素.

第二同型定理の指数版. `J = N ⊔ P` とおくと
`|N : N ∩ P| · |J : N| = |J : N ∩ P| = |P : N ∩ P| · |J : P|` で,
`|J : N| = |P : N ∩ P|` (`relIndex_sup_left`, `N` 正規) を約せば
`|N : N ∩ P| = |J : P|`. これは `|G : P|` を割るので `p` と互いに素. -/
theorem not_dvd_relIndex_inf_of_normal [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (P : Sylow p G) :
    ¬ p ∣ ((P : Subgroup G) ⊓ N).relIndex N := by
  set Q : Subgroup G := (P : Subgroup G) with hQ
  set J : Subgroup G := N ⊔ Q with hJ
  -- (Q ⊓ N).relIndex N = J.relIndex Q, then divide |G : Q|.
  have hNJ : N ≤ J := le_sup_left
  have hQJ : Q ≤ J := le_sup_right
  have hinfN : (Q ⊓ N) ≤ N := inf_le_right
  have hinfQ : (Q ⊓ N) ≤ Q := inf_le_left
  -- Chain 1: |Q ⊓ N : ?| through N.
  have c1 : (Q ⊓ N).relIndex N * N.relIndex J = (Q ⊓ N).relIndex J :=
    Subgroup.relIndex_mul_relIndex _ _ _ hinfN hNJ
  -- Chain 2: through Q.
  have c2 : (Q ⊓ N).relIndex Q * Q.relIndex J = (Q ⊓ N).relIndex J :=
    Subgroup.relIndex_mul_relIndex _ _ _ hinfQ hQJ
  -- Second isomorphism theorem, index form: |J : N| = |Q : Q ⊓ N|.
  have hsup : N.relIndex J = N.relIndex Q := by
    rw [hJ]; exact Subgroup.relIndex_sup_left Q N
  have hinf : (Q ⊓ N).relIndex Q = N.relIndex Q := Subgroup.inf_relIndex_left Q N
  rw [hsup] at c1
  rw [hinf] at c2
  -- Cancel the common (nonzero) factor N.relIndex Q.
  have hne : N.relIndex Q ≠ 0 := by
    have : N.relIndex Q ∣ Nat.card Q := Subgroup.relIndex_dvd_card N Q
    exact fun h0 => (Nat.card_pos (α := Q)).ne' (Nat.eq_zero_of_zero_dvd (h0 ▸ this))
  have key : (Q ⊓ N).relIndex N = Q.relIndex J := by
    have := c1.trans c2.symm
    -- (Q ⊓ N).relIndex N * (N.relIndex Q) = (N.relIndex Q) * (Q.relIndex J)
    rw [mul_comm (N.relIndex Q)] at this
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) this
  rw [key]
  exact fun hdvd => P.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hQJ))

/-- **Isaacs Lemma 9.31** (p. 291): `S ◁◁ G` (subnormal), `P ∈ Syl_p(G)` ⇒
`|S : S ∩ P|` は `p` と互いに素 (すなわち `P ∩ S ∈ Syl_p(S)`).

`Subgroup.IsSubnormal` の構造帰納. `top` 段は `Sylow.not_dvd_index` そのもの,
`step` 段は帰納法の仮定で得た `↥K` の Sylow に normal 段を適用する. -/
theorem not_dvd_relIndex_inf_of_isSubnormal [Finite G] {p : ℕ} [Fact p.Prime]
    {S : Subgroup G} (hS : S.IsSubnormal) (P : Sylow p G) :
    ¬ p ∣ ((P : Subgroup G) ⊓ S).relIndex S := by
  induction hS with
  | top =>
    simpa [Subgroup.relIndex_top_right] using P.not_dvd_index
  | step H K hle hKsub hHnorm ih =>
    -- Inside ↥K: `Q := (P ⊓ K).subgroupOf K` is a Sylow p-subgroup (ih gives the index).
    have hQ_pg : IsPGroup p ↥(((P : Subgroup G) ⊓ K).subgroupOf K) := by
      have : IsPGroup p ↥((P : Subgroup G) ⊓ K) :=
        P.isPGroup'.of_injective (Subgroup.inclusion inf_le_left)
          (Subgroup.inclusion_injective _)
      exact this.comap_subtype
    have hQ_idx : ¬ p ∣ (((P : Subgroup G) ⊓ K).subgroupOf K).index := ih
    set Q : Sylow p ↥K := hQ_pg.toSylow hQ_idx with hQdef
    have hQ_coe : (Q : Subgroup ↥K) = ((P : Subgroup G) ⊓ K).subgroupOf K :=
      hQ_pg.toSylow_coe hQ_idx
    -- Apply the normal step inside ↥K to the normal subgroup `H.subgroupOf K`.
    haveI : (H.subgroupOf K).Normal := hHnorm
    have hnormal := not_dvd_relIndex_inf_of_normal (H.subgroupOf K) Q
    rw [hQ_coe] at hnormal
    -- Identify `(P ⊓ K).subgroupOf K ⊓ H.subgroupOf K` with `(P ⊓ H).subgroupOf K`.
    have hmeet : ((P : Subgroup G) ⊓ K).subgroupOf K ⊓ H.subgroupOf K
        = ((P : Subgroup G) ⊓ H).subgroupOf K := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hle h.2⟩, h.2⟩⟩
    rw [hmeet, Subgroup.relIndex_subgroupOf hle] at hnormal
    exact hnormal

/-- **Isaacs Lemma 9.31** (束ねた形): `S ◁◁ G`, `P ∈ Syl_p(G)` ⇒ `P ∩ S` は `S` の
Sylow `p`-部分群. -/
noncomputable def sylowInfOfIsSubnormal [Finite G] {p : ℕ} [Fact p.Prime]
    {S : Subgroup G} (hS : S.IsSubnormal) (P : Sylow p G) : Sylow p ↥S :=
  (show IsPGroup p ↥(((P : Subgroup G) ⊓ S).subgroupOf S) from
    (P.isPGroup'.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective _)).comap_subtype).toSylow
    (not_dvd_relIndex_inf_of_isSubnormal hS P)

@[simp]
theorem sylowInfOfIsSubnormal_coe [Finite G] {p : ℕ} [Fact p.Prime]
    {S : Subgroup G} (hS : S.IsSubnormal) (P : Sylow p G) :
    (sylowInfOfIsSubnormal hS P : Subgroup ↥S) = ((P : Subgroup G) ⊓ S).subgroupOf S :=
  IsPGroup.toSylow_coe _ _

end

end OddOrder.Isaacs.Ch09
