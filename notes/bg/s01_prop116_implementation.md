# BG Prop 1.16 (coprime action generation) — 実装計画

> **出典**: BG mmd L501-507。**scope**: Prop 1.16 第2式の形式化。第1式 = Isaacs 6.21 は
> 既に repo にある (`OddOrder.Isaacs.Ch06.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic`)。

## ステートメント (BG Prop 1.16)

`p` prime, `G` が `p'`-群, `A` が `G` の自己同型のなす noncyclic abelian `p`-群。すると

1. `G = ⟨ C_G(x) | x ∈ A^# ⟩`  ← **Isaacs Thm 6.21 = G Thm 6.2.4 (済)**
2. `G = ⟨ C_G(Y) | Y ⊆ A, A/Y cyclic ⟩`  ← **本実装の対象**

> BG: 「第1式は **G** Thm 6.2.4, p.225。第2式は |G| 帰納で従う」。

repo では一般の coprime 設定で十分 (p, p'-群でなく `Nat.Coprime |A| |G|` + `¬IsCyclic A`)。

## 既存インフラ

- **Isaacs 6.21**: `[CommGroup A]` (`IsMulCommutative`) `[Finite A]` `[Group N]` `[Finite N]`
  `[MulDistribMulAction A N]` `(hCop : Coprime |A| |N|)` `(hNC : ¬IsCyclic A)` ⟹
  `nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A N) = ⊤`。
  - `nontrivialActionFixedByClosure φ = closure {u | ∃ a≠1, u ∈ actionFixedBy φ a}` (= ⟨C_N(a)|a≠1⟩)。
  - `actionFixedBy φ a = {u | φ a u = u}` (= C_N(a))。`mem_actionFixedBy`。
- **商作用** (mathlib `GroupTheory/GroupAction/OfQuotient.lean`):
  `MulDistribMulAction (A ⧸ H) (FixedPoints.submonoid H G)` — A/H が H の固定点に作用。
  H = `zpowers a` で A/⟨a⟩ が `C_G(a)` に作用。
- **不変部分群への作用制限** (Ch06): `IsFrobeniusAction.invariantSubgroupMulDistribMulAction`。

## 「A/Y cyclic」の符号化 (商型回避)

`A/Y cyclic ⟺ ∃ a : A, Y ⊔ Subgroup.zpowers a = ⊤` (A を Y と1元 a で生成)。
abelian なら `Y.Normal` は自動だが、商型 `A ⧸ Y` を statement に出さずに済むこの形を使う。

`C_G(Y)` (Y ≤ A の固定点) = `{g | ∀ y ∈ Y, φ y g = g}` を subgroup として定義 (`actionFixedBySubgroup φ Y`)。

## 証明 (card A の強帰納)

`motive n := ∀ (A : Type) [CommGroup A][Finite A], card A = n → ¬IsCyclic A →
  ∀ (G : Type) [Group G][Finite G][MulDistribMulAction A G], Coprime |A| |G| → 結論`。

1. Isaacs 6.21 で `⊤ = ⟨C_G(a) | a≠1⟩`。各 `C_G(a) ⊆ H := cocyclicClosure` を示せば十分。
2. `a ≠ 1` 固定:
   - **A/⟨a⟩ cyclic** (`∃b, ⟨a⟩⊔zpowers b = ⊤`): `Y = ⟨a⟩` は co-cyclic, `C_G(a) = C_G(⟨a⟩) ⊆ H`。
   - **A/⟨a⟩ noncyclic**: `Ā = A⧸zpowers a` は noncyclic, `card Ā < card A`。`Ā` が `C_G(a)`
     (= `FixedPoints (zpowers a) G`) に作用 (mathlib OfQuotient)。IH で
     `C_G(a) = ⟨C_{C_G(a)}(Z̄) | Z̄ co-cyclic in Ā⟩`。`C_{C_G(a)}(Z̄) = C_G(⟨a⟩⊔Z)` (Z=preimage),
     `⟨a⟩⊔Z` co-cyclic in A (同じ b で witness)。ゆえ `C_G(a) ⊆ H`。

## Lean 罠 (予想)

- 商作用インスタンスは `letI` で局所供給 (Y 可変)。`FixedPoints.submonoid` ↔ `actionFixedBy` subgroup
  の橋渡しが必要 (submonoid vs subgroup; group 作用なので一致)。
- card A の type-quantified 強帰納 (Isaacs 6.21 の N-帰納と同パターン, A も変える)。
- preimage `Z̄ ≤ Ā` → `Z ≤ A` と `⟨a⟩ ⊔ Z` の co-cyclic 性は `QuotientGroup.mk'` の像/原像で。

## 配置

新 leaf file `OddOrder/BG/Ch1_Preliminary/S01b_Prop116.lean` (Isaacs Ch06 import; S01 編集は
dependents 再ビルドが重いので回避)。S07 の Thm 7.2/7.3 がこれを import して消費。
第1式 (Isaacs 6.21) は **no-wrapper 方針**で直接呼ぶ — 本 file には第2式のみ。

## ✅ 完成 (2026-06-03, axiom-clean)

`S01b_Prop116.lean` (235行, sorry 0, AxiomsCheck 登録済, 3 標準公理のみ)。
- `cocyclicFixedByClosure φ` (= ⟨C_G(Y)|A/Y cyclic⟩, A/Y cyclic = `∃a, Y⊔zpowers a=⊤` で商型回避)。
- `cocyclicFixedByClosure_eq_top_of_not_isCyclic` (= **Prop 1.16(2)**): card A 強帰納。
- `nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'` (= **Prop 1.16(1)** φ 形,
  6.21 を compHom で interface 適応; `toMulAut(compHom φ)=φ` は `ext;rfl`)。
- 部品: `isAInvariant_actionFixedBy` (C_G(a) A-不変, 可換) / `quotAction` (A⧸⟨a⟩ の C_G(a) 作用,
  `IsAInvariant.restrict`→`QuotientGroup.lift`) / `quotAction_mk_apply_val` (互換性)。
- 罠記録: 結合マクロン `ḡ`/`b̄`/`Z̄` は Lean 識別子に不正→ASCII (gbar/bbar/Zbar)。
  `Subgroup.normal_of_isMulCommutative` は instance (自動)。`Subgroup.closure_le` は明示引数要
  (`apply .mpr` 不可→`rw`)。`ker_mk' ▸` は過剰書換→`rw...at hkc`。`Subgroup.card_quotient_dvd_card`/
  `comap_map_eq`/`map_comap_eq_self_of_surjective`/`MonoidHom.map_closure`/`range_eq_map`。
  `IsMulCommutative` 商 instance なし→`IsMulCommutative.of_comm`+`QuotientGroup.induction_on`。
