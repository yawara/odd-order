---
id: 36
slug: stuck-7-6-step-7
title: "Discharge Isaacs Thm 7.6 Step 7 axiom"
created: 2026-05-27
---

# Discharge Isaacs Thm 7.6 Step 7 axiom

## 背景

§7B Steps 2-6 + Step 8 のブリッジ補題は landed (commits a5ff31c, ed9a9ab).
Step 7 (mmd L3884-3892 = Isaacs p.213-214 の最終 contradiction 引数) だけが
未着で, `OddOrder.Isaacs.Ch07_ThompsonSubgroup.Main` に
`thompsonJ_le_opCore_of_normal_J_hypotheses` という `axiom` で placeholder.

これを discharge することで `normal_J` (Isaacs Thm 7.6) は完全 axiom-free
(`#assert_only_allowed_axioms` を通る) になる.

## 2026-05-27 セッション進捗

1. **`axiom thompsonJ_le_opCore_of_normal_J_hypotheses` を `theorem` に変換**
   (commit 7d0b3fb). `Nat.card G` の strong induction で再構造化, Step 2
   抽出 (`thompsonJ_le_iff`) と IH を持つ closing axiom にまとめた.
2. **closing axiom を Step 4-5 + Step 8 に分割** (commit 819067d):
   - `step4_5_normal_J_hypotheses` (private axiom): `P = UA ∧ A.relIndex U = p`
   - `step8_normal_J_closure` (private axiom): Step 7 bound から `False`
3. **Step 8 を Step 8a (axiom) + Step 8b (theorem) に分割** (commit 6a71ca3):
   - `step8a_PBar_normal_GBar` (private axiom): Thm 7.5 適用 → `P̄ ⊴ Ḡ`
   - `step8b_pullback_normal_P` (**theorem**, 約 30 LOC): correspondence
     theorem で `P ⊴ G` を引き出し, `normal_pgroup_le_opCore` で `P ≤ U` を
     得て `A ≤ P ≤ U` で矛盾.

**現在の axiom 状況** (`OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean`):
- `step4_5_normal_J_hypotheses` (textbook Steps 4-5, Lem 6.20 + Step 3 IH)
- `step8a_PBar_normal_GBar` (textbook Step 8 Thm 7.5 application)
- `noNonsolvableSimplePaQb` (§7D の別議題, Burnside)

両方の Step 4-5 / 8a axiom は前 axiom よりも狭い範囲を扱い, 独立に discharge
可能.

## 次のセッションで取り組むべきこと

### Step 8a discharge (~200-300 LOC)

Thm 7.5 (`sylow_normal_of_elementary_normal_P_theorem`) を `Ḡ ↷ V` に適用する
ためのハイポセシス降下 + action setup:
1. `φ : Ḡ →* MulAut V` を construct (V = `omega1ZCenterOpCore G p`).
2. `φ` が injective を Step 6 (`...map_eq_bot_of_le_opCore`) から導出.
3. Ḡ-Sylow `P̄` を G の Sylow `P` の image として取得.
4. `∀ Sylow p Q̄ of Ḡ, (actionCentralizer φ Q̄).index ≤ p` を Step 7 + Step 5
   から推論. 共役対称性 (`actionCentralizer_map_conj_index`) を使う.
5. Thm 7.5 を呼んで `P̄ ⊴ Ḡ` を得る.

### Step 4-5 discharge (~600-800 LOC)

最も大規模. 内部で Step 3 を使うので, 先に Step 3 を分離するか, 一気に
書き下すか戦略選択. Step 5 の "Lemma 6.20 適用" 部分が肝.

## 書籍での議論

Isaacs FGT p.213-214 (mmd L3884-3892):

設定:
- (i)-(v) の Thm 7.6 仮説.
- `L := O_p(G)`, `V := Z(L)`, `A ∈ E(P)` で `A ⊄ L` (反証用).
- Step 1: `Z(P) ≤ L`, `C_G(L) ≤ L`.
- Step 2-3: `D := A ⊓ L`, `|A : D| = p` (elementary abelian + L = O_p で
  Hall-Higman 3.21 から `G/L` の p-成分が自明).
- Step 4: `D` は `V` に自明に作用 (Step 5-6 で landed).
- Step 5-6: `A/D` の `V` への作用が自明 (Ch.6 Thm 6.20 + Ch.4 Cor 4.35).

Step 7 の中身 (axiom):
- Step 5-6 の結論「A が V 全体に自明作用」⇒ `A ≤ C_G(V) = C_G(Z(L))`.
- `Z(P) ≤ Z(L)` (Step 1 で `Z(P) ≤ L` かつ Z(P) は全 P と可換, ゆえに L と可換).
- ゆえに `C_G(Z(L)) ≤ C_G(Z(P)) = P` (hypothesis v).
- A ≤ P (既知) かつ A が V に自明作用を組合せて, `A · Ω₁(V)` を E(P) の元
  として再構成し maxElemAbelianIn の最大性に矛盾.

## やること

- [ ] **Step infrastructure (新規)**: `V := Ω₁(Z(O_p(G)))` の subgroup 化.
      既存 `OddOrder.GroupTheory.Omega G p 1 = ⟨{g : g^p = 1}⟩` (closure 形) は
      G 全体の Ω₁ で V := Ω₁(Z(L)) と異なる. Z(L) 上で `g^p = 1` を満たす
      pointwise predicate を Z(L) の subgroup として明示構成 (abelian 内なら
      `{g | g^p = 1}` は subgroup, mathlib `Subgroup.mk` で具体化) 要 ~80-150 LOC.
- [ ] **Step 6 (Q-trivial on Z(U))**: `K = C_G(V)` の Sylow q (q ≠ p) `Q` が
      `Z(U)` に自明作用を示す.
      Cor 4.35 (`actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`)
      を適用するため Q の Z(U) への共役作用 `Q →* MulAut Z(U)` を構成 (~100-150 LOC).
- [ ] **Step 6 (K = p-group)**: 各 q ≠ p で Sylow q が trivial, hence K is p-group.
      Cauchy / Sylow 経由 (~50 LOC).
- [ ] **Step 6 (K ≤ U)**: `K ⊴ G ∧ K p-group ⇒ K ≤ O_p(G)` (mathlib 既存
      `Subgroup.normal_le_opCore` 系) (~20 LOC).
- [ ] **Step 6 (Ḡ ↷ V faithful)**: `K̄ = 1` from `K̄ = K/U = ⊥` since `K ≤ U`.
      φ : Ḡ → MulAut V faithful (~50-100 LOC).
- [ ] **Step 7 counting**: `D = U ∩ A`, `E = V ∩ A`. `D` elementary abelian,
      `V` central elementary abelian ⇒ `VD` elementary abelian.
      `|VD| ≤ |A|` (maximality) ⇒ `|VD : D| ≤ |A : D| = p`.
      `|V : E| = |VD : D| ≤ p` (~150-200 LOC).
- [ ] **Step 8 (centralizer index ≤ p)**: `P̄ = Ā` (since P = UA), `Ā` abelian
      centralizes `V ∩ A = E`, so `|V : C_V(P̄)| ≤ |V : E| ≤ p` (~50 LOC).
- [ ] **Step 8 (Thm 7.5 application)**: `P̄ ⊴ Ḡ` via
      `sylow_normal_of_elementary_normal_P_theorem` (Main.lean:2516) (~80 LOC).
- [ ] **Step 8 (pull back)**: `P̄ ⊴ Ḡ ⇒ P ⊴ G` via correspondence theorem,
      then `A ⊆ P ⊆ O_p(G) = U` contradicts `A ⊄ U` (~50 LOC).
- [ ] **Step 4-5 重要 missing**: `G = LA` と `P = UA` (mmd L3870) と
      `|Ā| = p` (mmd L3874) も Step 7-8 で必要.
      Hall-Higman 3.21 + Lemma 6.20 (`isCyclic_of_faithful_trivial_on_proper_invariant`)
      適用 (~200-300 LOC).
- [ ] **A ∈ E(P) extraction**: `J(P) ⊄ U ⇒ ∃ A ∈ maxElemAbelianIn P p, A ⊄ U`.
      `Subgroup.thompsonJ` def 展開 + iSup_le_iff (~30-50 LOC).
- [ ] `axiom thompsonJ_le_opCore_of_normal_J_hypotheses` を `theorem` に格上げ
- [ ] `OddOrder/AxiomsCheck.lean` に `normal_J` を追加して axiom-free を CI gate

## 着手見積もり (2026-05-27)

- **総 LOC**: ~900-1300 (新規 bridge lemmas + 主証明).
- **必要 build iterations**: 各 bridge lemma あたり 2-3 iter で 25+ iter 必要.
- 単一セッション 8 iter 制限内では closure 不可. **複数セッションに分割必須**.
- 推奨分割: (A) V subgroup 構成 + Cor 4.35 wrapper, (B) Step 4 (G=LA) +
  Step 5 (|Ā|=p), (C) Step 6 faithful action, (D) Step 7 counting + Step 8 closure.

## 完了条件

- `axiom thompsonJ_le_opCore_of_normal_J_hypotheses` が `theorem` に置換され
  `lake build OddOrder` が通る
- `OddOrder.Isaacs.Ch07.normal_J` が `#assert_only_allowed_axioms` で通る

## 参照

- commits a5ff31c (Step 2-4 structural bridges), ed9a9ab (Step 5-6 + Step 8)
- `OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean` §7B section
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean:3437` Cor 4.35
- `OddOrder/Isaacs/Ch06_FrobeniusActions/Main.lean:3015` Thm 6.20
- `OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean:2516` Thm 7.5
- Isaacs FGT pp.209-214, mmd L3832-3896
