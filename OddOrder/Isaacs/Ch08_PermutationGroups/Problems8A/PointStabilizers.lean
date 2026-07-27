/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import OddOrder.Isaacs.Ch08_PermutationGroups.HalfTransitive

/-!
# Isaacs Problems 8A (pp. 235–236) — 点安定化群・正規部分群の軌道

**Problems 8A.5–8A.9**。点安定化群 `G_α` の固定点集合 `Δ = Fix(G_α)` と
その正規化群の作用、`p`-Sylow 版、可換 half-transitive 作用、正規部分群の軌道。

## Main results

- `smul_mem_fixedPoints_of_mem_normalizer`,
  `exists_mem_normalizer_stabilizer_smul_eq`,
  `eq_of_mem_fixedPoints_stabilizer_of_transitive_on_compl` — **Problem 8A.5**:
  `Δ = Fix(G_α)` は `N_G(G_α)` で保たれ, その上で `N_G(G_α)` は推移的。`k ≥ 2` かつ
  `|Δ| ≥ 2` は `|Ω| = 2` を強制するので, `r = min(k, |Δ|)` の主張はこの推移性に尽きる。
- `exists_mem_conj_eq_of_sylow_le`, `exists_mem_normalizer_sylow_smul_eq` —
  **Problem 8A.6**: `Q ∈ Syl_p(G_α)` について `N_G(Q)` は `Fix(Q)` に推移的。
- `isFrobeniusAction_of_comm_of_half_transitive`,
  `isFrobeniusAction_and_isCyclic_of_comm_of_half_transitive` — **Problem 8A.7**:
  可換群の忠実 half-transitive 作用は Frobenius で, その群は巡回。
- `smul_orbit_eq_orbit_smul`, `card_orbit_eq_of_normal` — **Problem 8A.8**:
  transitive な `G` の正規部分群 `N` について `G` は `N`-軌道を推移的に置換し,
  したがって `N` は half-transitive (すべての `N`-軌道が同じ濃度)。
- `isPretransitive_of_normal_of_two_transitive` — **Problem 8A.9**: 2-transitive な `G` の
  非自明に作用する正規部分群は推移的。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

section /- Problems 8A (pp. 235-236) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-! ### Problem 8A.5 — 点安定化群の固定点集合 -/

/-- 有限群では `H ≤ K` と位数の一致から `H = K`。 -/
private theorem eq_of_le_of_card_eq [Finite G] {H K : Subgroup G} (hle : H ≤ K)
    (hcard : Nat.card ↥K = Nat.card ↥H) : H = K := by
  refine le_antisymm hle (Subgroup.subgroupOf_eq_top.mp (Subgroup.eq_top_of_card_eq _ ?_))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]

/-- `Δ = Fix(H)` は `N_G(H)` で保たれる: `h • (n • β) = n • ((n⁻¹hn) • β) = n • β`。 -/
theorem smul_mem_fixedPoints_of_mem_normalizer {H : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (H : Set G)) {β : Ω}
    (hβ : β ∈ MulAction.fixedPoints ↥H Ω) : n • β ∈ MulAction.fixedPoints ↥H Ω := by
  intro h
  have hmem : n⁻¹ * (h : G) * n ∈ H := (Subgroup.mem_normalizer_iff''.mp hn (h : G)).mp h.2
  have := hβ ⟨n⁻¹ * (h : G) * n, hmem⟩
  rw [subgroup_smul_def] at this
  calc (h : G) • (n • β) = (n * (n⁻¹ * (h : G) * n)) • β := by rw [← mul_smul]; group
    _ = n • ((n⁻¹ * (h : G) * n) • β) := mul_smul _ _ _
    _ = n • β := by rw [this]

/-- **Isaacs Problem 8A.5** (p. 235) の主内容: `G` が `Ω` に推移的で `H = G_α` のとき,
`N_G(H)` は `Δ = Fix(H)` に**推移的**に作用する。

`β ∈ Δ` は `H ≤ G_β` を意味する。`G` の推移性で `β = g • α` と書くと
`G_β = gHg⁻¹` なので `H ≤ gHg⁻¹`, 有限性から `H = gHg⁻¹`, すなわち `g ∈ N_G(H)`。 -/
theorem exists_mem_normalizer_stabilizer_smul_eq [Finite G] [IsPretransitive G Ω] {α β : Ω}
    (hβ : β ∈ MulAction.fixedPoints ↥(stabilizer G α) Ω) :
    ∃ n ∈ Subgroup.normalizer ((stabilizer G α : Subgroup G) : Set G), n • α = β := by
  obtain ⟨g, hg⟩ := exists_smul_eq G α β
  refine ⟨g, ?_, hg⟩
  have hle : stabilizer G α ≤ (stabilizer G α).map (MulAut.conj g).toMonoidHom := by
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hg]
    exact fun h hh => hβ ⟨h, hh⟩
  have hcard : Nat.card ↥((stabilizer G α).map (MulAut.conj g).toMonoidHom) =
      Nat.card ↥(stabilizer G α) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq := eq_of_le_of_card_eq hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [heq]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [heq] at hh
    obtain ⟨y, hy, hyeq⟩ := hh
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at hyeq
    exact (mul_left_cancel (mul_right_cancel hyeq)) ▸ hy

/-- **Isaacs Problem 8A.5** の退化部分: `G` が 2-transitive (= `G_α` が `Ω ∖ {α}` に推移的)
で `Δ = Fix(G_α)` が `α` 以外の点 `β` をもつなら, `Ω` は 2 点しかもたない。

したがって `r = min(k, |Δ|)` は `k ≥ 2` かつ `|Δ| ≥ 2` のとき `Ω` が 2 点集合の場合に限られ,
そこでは `N_G(H) = G` が `Δ = Ω` に `k`-transitive に作用する。一般には `|Δ| ≥ 3` なら
`k ≤ 1` で `r = 1`, すなわち上の推移性が主張のすべて。 -/
theorem eq_of_mem_fixedPoints_stabilizer_of_transitive_on_compl {α β : Ω}
    (hβ : β ∈ MulAction.fixedPoints ↥(stabilizer G α) Ω)
    (htwo : ∀ γ : Ω, γ ≠ α → ∃ h : ↥(stabilizer G α), h • β = γ) :
    ∀ γ : Ω, γ ≠ α → γ = β := by
  intro γ hγ
  obtain ⟨h, hh⟩ := htwo γ hγ
  exact (hh ▸ hβ h).symm ▸ rfl

/-! ### Problem 8A.6 — Sylow 版 -/

/-- 共役で部分群が保たれれば正規化群の元。 -/
private theorem mem_normalizer_of_map_conj_eq {Q : Subgroup G} {n : G}
    (h : Q.map (MulAut.conj n).toMonoidHom = Q) : n ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    rw [← h]
    exact ⟨q, hq, rfl⟩
  · intro hq
    rw [← h] at hq
    obtain ⟨y, hy, hyeq⟩ := hq
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at hyeq
    exact (mul_left_cancel (mul_right_cancel hyeq)) ▸ hy

/-- `Q ≤ K` のとき `Nat.card Q * [K : Q] = Nat.card K`。 -/
private theorem card_mul_relIndex [Finite G] {Q K : Subgroup G} (h : Q ≤ K) :
    Nat.card ↥Q * Q.relIndex K = Nat.card ↥K := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
  exact Subgroup.card_mul_index (Q.subgroupOf K)

/-- `Q ≤ K` のとき `↥K` の中で見た `Q` も `p`-群。 -/
private theorem isPGroup_subgroupOf {p : ℕ} {Q K : Subgroup G} (hQK : Q ≤ K)
    (hp : IsPGroup p ↥Q) : IsPGroup p ↥(Q.subgroupOf K) :=
  hp.of_injective (Subgroup.subgroupOfEquivOfLe hQK).toMonoidHom (MulEquiv.injective _)

/-- **部分群 `K` の中の 2 つの `p`-Sylow は `K` の元で共役** (ambient `Subgroup G` の言葉)。

`Sylow p ↥K` へ持ち上げて mathlib の共役性 (`MulAction.exists_smul_eq`) を使い,
`K.subtype` で押し出して戻す。 -/
theorem exists_mem_conj_eq_of_sylow_le [Finite G] {p : ℕ} [Fact p.Prime]
    {K Q₁ Q₂ : Subgroup G} (h₁ : Q₁ ≤ K) (h₂ : Q₂ ≤ K)
    (hp₁ : IsPGroup p ↥Q₁) (hp₂ : IsPGroup p ↥Q₂)
    (hi₁ : ¬ p ∣ Q₁.relIndex K) (hi₂ : ¬ p ∣ Q₂.relIndex K) :
    ∃ x ∈ K, Q₁.map (MulAut.conj x).toMonoidHom = Q₂ := by
  classical
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (↥K)
    ((isPGroup_subgroupOf h₁ hp₁).toSylow hi₁) ((isPGroup_subgroupOf h₂ hp₂).toSylow hi₂)
  have hcoe : (Q₁.subgroupOf K).map (MulAut.conj x).toMonoidHom = Q₂.subgroupOf K := by
    have h0 := congrArg (fun S : Sylow p ↥K => (S : Subgroup ↥K)) hx
    simp only [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h0
    exact h0
  have hcomp : K.subtype.comp (MulAut.conj x).toMonoidHom
      = (MulAut.conj (x : G)).toMonoidHom.comp K.subtype := by
    ext y; simp
  refine ⟨(x : G), x.2, ?_⟩
  calc Q₁.map (MulAut.conj (x : G)).toMonoidHom
      = ((Q₁.subgroupOf K).map K.subtype).map (MulAut.conj (x : G)).toMonoidHom := by
        rw [Subgroup.map_subgroupOf_eq_of_le h₁]
    _ = (Q₁.subgroupOf K).map (K.subtype.comp (MulAut.conj x).toMonoidHom) := by
        rw [Subgroup.map_map, hcomp]
    _ = ((Q₁.subgroupOf K).map (MulAut.conj x).toMonoidHom).map K.subtype := by
        rw [Subgroup.map_map]
    _ = Q₂ := by rw [hcoe, Subgroup.map_subgroupOf_eq_of_le h₂]

/-- **Isaacs Problem 8A.6** (p. 235): `G` が `Ω` に推移的で `H = G_α`, `Q ∈ Syl_p(H)` のとき,
`N_G(Q)` は `Δ = Fix(Q)` に推移的に作用する。

`β = g • α` と書くと `G_β = gHg⁻¹` で, `Q` と `gQg⁻¹` はともに `G_β` の `p`-Sylow。
`G_β` の元 `x` で `xQx⁻¹ = gQg⁻¹` を取ると `n := x⁻¹g` が `Q` を正規化し,
`n • α = x⁻¹ • β = β`。 -/
theorem exists_mem_normalizer_sylow_smul_eq [Finite G] [IsPretransitive G Ω] {p : ℕ}
    [Fact p.Prime] {α β : Ω} {Q : Subgroup G} (hQH : Q ≤ stabilizer G α)
    (hp : IsPGroup p ↥Q) (hi : ¬ p ∣ Q.relIndex (stabilizer G α))
    (hβ : β ∈ MulAction.fixedPoints ↥Q Ω) :
    ∃ n ∈ Subgroup.normalizer (Q : Set G), n • α = β := by
  classical
  obtain ⟨g, hg⟩ := exists_smul_eq G α β
  have hKeq : stabilizer G β = (stabilizer G α).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have hQK : Q ≤ stabilizer G β := fun q hq => hβ ⟨q, hq⟩
  have hQ'K : Q.map (MulAut.conj g).toMonoidHom ≤ stabilizer G β := by
    rw [hKeq]; exact Subgroup.map_mono hQH
  have hcardQ' : Nat.card ↥(Q.map (MulAut.conj g).toMonoidHom) = Nat.card ↥Q :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcardK : Nat.card ↥(stabilizer G β) = Nat.card ↥(stabilizer G α) := by
    rw [hKeq]; exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hpos : 0 < Nat.card ↥Q := Nat.card_pos
  have hrel : Q.relIndex (stabilizer G β) = Q.relIndex (stabilizer G α) :=
    Nat.eq_of_mul_eq_mul_left hpos
      ((card_mul_relIndex hQK).trans (hcardK.trans (card_mul_relIndex hQH).symm))
  have hrel' : (Q.map (MulAut.conj g).toMonoidHom).relIndex (stabilizer G β)
      = Q.relIndex (stabilizer G α) := by
    refine Nat.eq_of_mul_eq_mul_left
      (show 0 < Nat.card ↥(Q.map (MulAut.conj g).toMonoidHom) from Nat.card_pos) ?_
    rw [card_mul_relIndex hQ'K, hcardQ', card_mul_relIndex hQH]
    exact hcardK
  have hpQ' : IsPGroup p ↥(Q.map (MulAut.conj g).toMonoidHom) :=
    hp.of_injective
      (Subgroup.equivMapOfInjective Q (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm.toMonoidHom (MulEquiv.injective _)
  obtain ⟨x, hxK, hxeq⟩ := exists_mem_conj_eq_of_sylow_le hQK hQ'K hp hpQ'
    (by rw [hrel]; exact hi) (by rw [hrel']; exact hi)
  have hsplit : ∀ a b : G, (MulAut.conj (a * b)).toMonoidHom
      = (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
    intro a b; ext y; simp [mul_assoc]
  refine ⟨x⁻¹ * g, mem_normalizer_of_map_conj_eq ?_, ?_⟩
  · rw [hsplit, ← Subgroup.map_map, ← hxeq, Subgroup.map_map, ← hsplit]
    simp only [inv_mul_cancel, map_one]
    ext y
    simp
  · rw [mul_smul, hg, inv_smul_eq_iff]
    exact (mem_stabilizer_iff.mp hxK).symm

/-! ### Problem 8A.7 — 可換群の half-transitive 作用は Frobenius -/

section AbelianHalfTransitive

variable {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]

/-- 可換な `A` が作用するとき, 一つの元 `a` の固定部分群は `A`-不変。 -/
theorem smul_mem_fixedBy_of_comm (hcomm : ∀ x y : A, x * y = y * x) (a b : A) {n : N}
    (hn : a • n = n) : a • (b • n) = b • n := by
  rw [smul_smul, hcomm, ← smul_smul, hn]

/-- **Isaacs Problem 8A.7** (p. 235), 前半: **可換群 `A` が `N` に忠実に作用し, 非単位元上の
作用が half-transitive なら, その作用は Frobenius**。

Thm 8.9 (`isFrobeniusAction_or_isElementaryAbelian_of_half_transitive`) の例外肢を
可換性で潰す: `a ≠ 1` が `n ≠ 1` を固定するなら, `a` の固定部分群 `Fix(a)` は
(`A` が可換なので) `A`-不変で `⊥` でない。例外肢は「`⊥` 以外の真の `A`-不変部分群は無い」
と言うので `Fix(a) = ⊤`, すなわち `a` は自明に作用し忠実性に反する。 -/
theorem isFrobeniusAction_of_comm_of_half_transitive [Finite A] [Finite N] [FaithfulSMul A N]
    (hcomm : ∀ x y : A, x * y = y * x)
    (hhalf : ∀ x y : N, x ≠ 1 → y ≠ 1 →
      Nat.card (MulAction.orbit A x) = Nat.card (MulAction.orbit A y)) :
    Ch06.IsFrobeniusAction A N := by
  rcases isFrobeniusAction_or_isElementaryAbelian_of_half_transitive A N hhalf with h | ⟨-, hirr⟩
  · exact h
  intro a ha n hn hfix
  -- `Fix(a)` は `A`-不変な非自明部分群
  let F : Subgroup N :=
    { carrier := {x : N | a • x = x}
      one_mem' := smul_one a
      mul_mem' := fun {u v} hu hv => by
        simp only [Set.mem_setOf_eq] at hu hv ⊢
        rw [smul_mul', hu, hv]
      inv_mem' := fun {u} hu => by
        simp only [Set.mem_setOf_eq] at hu ⊢
        rw [smul_inv', hu] }
  have hFinv : ∀ b : A, ∀ x ∈ F, b • x ∈ F := fun b x hx =>
    smul_mem_fixedBy_of_comm hcomm a b hx
  have hFtop : F = ⊤ := by
    by_contra hne
    have := hirr F hne hFinv
    have hnF : n ∈ F := hfix
    rw [this, Subgroup.mem_bot] at hnF
    exact hn hnF
  refine ha (FaithfulSMul.eq_of_smul_eq_smul (α := N) fun x => ?_)
  have : x ∈ F := hFtop ▸ Subgroup.mem_top x
  rw [one_smul]
  exact this

/-- **Isaacs Problem 8A.7** (p. 235): 可換群 `A` が非自明な `N` に忠実に作用し, 非単位元上の
作用が half-transitive なら, その作用は Frobenius で **`A` は巡回群**。

`A` が巡回であることは前半 (Frobenius) と Isaacs Cor 6.17 の可換分岐
(`Ch06.isCyclic_of_frobeniusAction_of_isMulCommutative`, 可換な Frobenius 補群は巡回) から。 -/
theorem isFrobeniusAction_and_isCyclic_of_comm_of_half_transitive [Finite A] [Finite N]
    [Nontrivial N] [FaithfulSMul A N] [IsMulCommutative A]
    (hhalf : ∀ x y : N, x ≠ 1 → y ≠ 1 →
      Nat.card (MulAction.orbit A x) = Nat.card (MulAction.orbit A y)) :
    Ch06.IsFrobeniusAction A N ∧ IsCyclic A := by
  have hfrob := isFrobeniusAction_of_comm_of_half_transitive
    (fun x y => (IsMulCommutative.is_comm (M := A)).comm x y) hhalf
  exact ⟨hfrob, Ch06.isCyclic_of_frobeniusAction_of_isMulCommutative hfrob⟩

end AbelianHalfTransitive

/-! ### Problem 8A.8 — 正規部分群の軌道は推移的に置換される -/

/-- **Isaacs Problem 8A.8** (p. 235): `N ⊴ G` のとき `g` は `N`-軌道を `N`-軌道へ写す:
`g • orbit N α = orbit N (g • α)`。

`N` が正規なので `g * n = (g n g⁻¹) * g` と書き換えられる。 -/
theorem smul_orbit_eq_orbit_smul {N : Subgroup G} [N.Normal] (g : G) (α : Ω) :
    g • orbit N α = orbit N (g • α) := by
  ext x
  constructor
  · rintro ⟨-, ⟨n, rfl⟩, rfl⟩
    refine ⟨⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem ‹N.Normal› (n : G) n.2 g⟩, ?_⟩
    simp only [subgroup_smul_def, ← mul_smul]
    group
  · rintro ⟨n, rfl⟩
    refine ⟨(g⁻¹ * (n : G) * g) • α, ⟨⟨g⁻¹ * (n : G) * g, ?_⟩, rfl⟩, ?_⟩
    · simpa using Subgroup.Normal.conj_mem ‹N.Normal› (n : G) n.2 g⁻¹
    · simp only [subgroup_smul_def, ← mul_smul]
      group

/-- **Isaacs Problem 8A.8** (p. 235) の帰結: `G` が推移的で `N ⊴ G` なら `N` は
**half-transitive** — すべての `N`-軌道が同じ濃度をもつ。

`G` の推移性で `β = g • α` と書き, `g • orbit N α = orbit N β` が全単射を与える。 -/
theorem card_orbit_eq_of_normal [IsPretransitive G Ω] {N : Subgroup G} [N.Normal] (α β : Ω) :
    Nat.card (orbit N α) = Nat.card (orbit N β) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G α β
  rw [← smul_orbit_eq_orbit_smul g α]
  exact Nat.card_congr ((Equiv.Set.image (fun x : Ω => g • x) (orbit N α)
    (MulAction.injective g)).trans (Equiv.setCongr Set.image_smul))

/-! ### Problem 8A.9 — 2-transitive 群の非自明な正規部分群は推移的 -/

/-- **Isaacs Problem 8A.9** (p. 236): `G` が `Ω` に 2-transitive で `N ⊴ G` が非自明に
作用するなら, `N` は推移的。

2-transitivity は「推移的 (`IsPretransitive G Ω`) かつ各点安定化群 `G_α` が `Ω ∖ {α}` に
推移的」の形で仮定する (`h2`)。

`N ⊴ G` なので `g • orbit N α = orbit N (g • α)` (8A.8)。非自明性から `orbit N α` には
`α` 以外の点 `γ` があり, `G_α` の推移性で任意の `β ≠ α` を `γ` から得る `g` を取れば
`β = g • γ ∈ g • orbit N α = orbit N α`。 -/
theorem isPretransitive_of_normal_of_two_transitive [IsPretransitive G Ω]
    (h2 : ∀ α β γ : Ω, β ≠ α → γ ≠ α → ∃ g : G, g • α = α ∧ g • β = γ)
    {N : Subgroup G} [N.Normal] {x : Ω} {n : ↥N} (hn : (n : G) • x ≠ x) :
    IsPretransitive N Ω := by
  refine ⟨fun a b => ?_⟩
  -- `orbit N a` には `a` 以外の点 `γ` がある
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq G x a
  have horb : g₀ • orbit N x = orbit N a := by rw [smul_orbit_eq_orbit_smul, hg₀]
  have hγmem : g₀ • ((n : G) • x) ∈ orbit N a := by
    rw [← horb]
    exact ⟨(n : G) • x, ⟨n, rfl⟩, rfl⟩
  have hγne : g₀ • ((n : G) • x) ≠ a := by
    rw [← hg₀]
    exact fun hc => hn (MulAction.injective g₀ hc)
  -- `b = a` なら自明, そうでなければ `G_a` の推移性で移す
  rcases eq_or_ne b a with rfl | hba
  · exact ⟨1, one_smul _ _⟩
  obtain ⟨g, hga, hgγ⟩ := h2 a (g₀ • ((n : G) • x)) b hγne hba
  have : b ∈ orbit N a := by
    rw [← hgγ, ← hga, ← smul_orbit_eq_orbit_smul]
    exact ⟨_, hγmem, rfl⟩
  obtain ⟨m, hm⟩ := this
  exact ⟨m, hm⟩

end

end OddOrder.Isaacs.Ch08
