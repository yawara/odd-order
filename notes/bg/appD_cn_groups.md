# BG App.D: Cn-Groups of Odd Order — mini-roadmap

**スコープ**: BG Appendix D (pp.153-156), mmd L5006-5073, 2 結果 (Lem D.1, D.2) + ガイド本文.
形式化先 (予定): `OddOrder/BG/AppD_CNGroups.lean` (Phase 2 必須ではない).
ROADMAP 上の位置: Phase 2 本筋外 (歴史的価値, optional).
役割: **Feit-Hall-Thompson 1960 CN-theorem の短縮ルート**. Gorenstein 1968 本書 (G) Ch.14 を BG §1-§9 + Lem D.1/D.2 で大幅短縮.

**更新 (2026-07-02)**: 3-decl skeleton `OddOrder/BG/AppD_CNGroups.lean` が存在 (sorried 3 theorems: `sylow_eq_of_nontrivial_inter` / `sylow_le_commutator_normalizer` / `cnTheorem_reduction`)。off-spine・consumer 0・凍結 (memory [[ft-settled-findings]])。

## ✅ 完了 (2026-07-19) — D.1 / D.2 とも証明済 (sorry-free / axiom-clean)

**下の 2026-07-02 までの記述 (「skip 推奨」「凍結」「sorried skeleton」) はすべて無効**。
2026-07-16 の全 3 冊フェーズ移行で App.D は正規のスコープ内になり、issue 3020 / 9133 の
経路で完了した。現在の構成 (`AppD_CNGroups.lean` は pure re-export hub):

| leaf | 内容 |
|---|---|
| `AppD_CNGroups/Basic.lean` | `IsCNGroup` / `MinimalSimpleCNHypothesis` / CN の部分群継承 / `O_p(G)=⊥` |
| `AppD_CNGroups/MaximalSylowIntersection.lean` | BG p.153-154 の局所解析全ステップ |
| `AppD_CNGroups/SylowTI.lean` | **Lemma D.1** + **Lemma D.2** |

上流: Gorenstein Ch.12 §1 Cor 1.6 (`GroupTheory.CNGroupStructure`, issue 9133) /
3-step 群の Sylow 交わり定理 (`GroupTheory.ThreeStepGroup.IsThreeStepGroup.inf_sylow_eq_oPiCore`) /
BG Thm 6.2 の `L(P)` 版 (`AppB.zCenter_lOdd_sup_oPiCore_normal`) /
mathlib の焦点部分群定理。

**書籍の行間 2 件** (詳細は issue 3020):
1. BG は `M` に Thm 6.2 を当てて `Z(J(P)) ⊴ M` とするが、これは `P ≤ M` を前提しており、
   その時点では未証明。`S = P ∩ M` に当ててから `M = N_G(Z(L(S)))` → `N_P(S) = S` → `S = P`
   と補修した (`sylow_le_and_eq_normalizer`)。
2. 終盤が「別の極大 `Q'`」に (D.2) を再適用できるのは `N_G(Z(L(P)))` が `P` だけで決まるから。
   `inf_le_oPiCore_normalizer_zCenterLOdd` として明示化した。

⚠ **`feitThompson` からの vacuous discharge は依然として禁止** (CN 定理は FT の *入力*)。
本形式化はその経路を使っていない。

---

## TL;DR — FT 本筋外、CN-theorem を BG 機械で短縮 (⚠ 2026-07-02 時点の評価、上記で無効)

CN-condition は「∀ x ≠ 1, C_G(x) nilpotent」. Feit, Hall, Thompson (1960) が CN-group of odd order は solvable を証明 (FT 1963 の予兆). BG App.D はその局所解析部を BG §1-§9 (特に **Thm 6.2 normal-J**) と Focal Subgroup Theorem (Thm 1.17) で短縮する **ガイド節**.

**FT 本筋との関係**: △ (本筋外). CN は FT の strict 特殊化で、Phase 4 メイン定理は CN を経由しない. App.D は **歴史的・教育的価値** のみで Phase 2 形式化 skip 推奨.

## App.D 全結果

| # | mmd 行 | 種別 | statement 要約 | 役割 |
|---|--------|------|-----------------|------|
| **Lem D.1** | L5012 | Lemma | G minimal simple CN-group of odd order, P, Q Sylow p, `P ∩ Q ≠ 1` ⇒ `P = Q` (TI-Sylow) | Sylow の TI property を導出 |
| **Lem D.2** | L5062 | Lemma | G minimal simple CN-group of odd order, P nontrivial Sylow, N = N_G(P) ⇒ `P ⊆ N'` | Focal Subgroup Theorem 経由 |

加えて App.D の本文は:
- Gorenstein (G) Ch.7, 8, 10 の **代替** を BG §1-§9 + §10 + §11-§14 (= Sections 1-4) + Lem 10.1.3 で提供
- Thm 7.6.1, 10.2.1 (G) ⇒ BG Thm 4.18(b), 3.7
- Thm 7.6.2, 10.3.1 (G) は 1 段落・1 文に短縮
- (G) Ch.14 introduction + §14.1 を odd-order 下で容易化
- Lem D.1 を挿入 (Feit _Characters of Finite Groups_ (27.6) からの示唆)

## CN-condition の定義

**CN-group** (Centralizer-Nilpotent):
```
G is a CN-group :⇔ ∀ x ∈ G with x ≠ 1, C_G(x) is nilpotent
```

**Lean 表現候補**:
```lean
def IsCNGroup (G : Type*) [Group G] : Prop :=
  ∀ x : G, x ≠ 1 → IsNilpotent (Subgroup.centralizer {x})
```

mathlib では `IsNilpotent` (Subgroup.lean) と `centralizer` は既存だが、CN 概念は完全未収載.

## Lem D.1 (Sylow TI property) 詳細

**Statement** (L5012):
```
G : minimal simple CN-group of odd order
p : prime
P, Q : Sylow p-subgroups of G
P ∩ Q ≠ 1
⇒ P = Q
```

**証明戦略** (L5014-5058):
1. 反例 P, Q を最大 P ∩ Q で取り、N = N_G(Z(J(P))) (or L(P) substitute) を定義
2. M = N_G(P ∩ Q) を含む subgroup で O_p(M) ≠ 1 を維持しつつ maximal なものを取る
3. P_1 ⊆ P, Q_1 ⊆ Q を含む各 Sylow 構造を解析
4. (D.1): P ∩ Q ⊂ P ∩ M, P ∩ M and Q ∩ M Sylow p-subgroups of M
5. (G) Cor 14.1.6: M は 3-step group w.r.t. p
6. (D.2): P ∩ Q = O_p(M)
7. **Thm 6.2 適用** (L5030): `Z(J(P)) = Z(J(P))·O_{p'}(M) ⊴ M` ⇒ M ⊆ N, M maximal で M = N
8. N/O_{p,p'}(N) が p-group, K = O_{p,p'}(N), N/K ⊃ (N/K)'
9. (D.3): P ∩ N'K ⊂ P
10. Focal Subgroup Theorem (Thm 1.17) を P, G に適用: `P ∩ G' = ⟨x^{-1}y | x, y ∈ P conjugate in G⟩ ⊆ P ∩ N'K ⊂ P`
11. G' = G (G simple) ⇒ 矛盾 ⊥

**鍵となる BG 結果**:
- **Thm 6.2** (normal-J) — Z(J(P)) ⊴ M
- **Thm 1.17** (Focal Subgroup Theorem) — P ∩ G' characterization
- **(G) Cor 14.1.6** — 3-step group property (Gorenstein 1968 経由)

## Lem D.2 (P ⊆ N') 詳細

**Statement** (L5062):
```
G : minimal simple CN-group of odd order
P : nontrivial Sylow subgroup
N := N_G(P)
⇒ P ⊆ N'
```

**証明** (L5064-5068):
1. ∀ x, y ∈ P, t ∈ G, x^t = y を仮定
2. x = y = 1 case は trivial
3. x ≠ 1 case: `P ∩ P^t ≠ 1`, **Lem D.1** で `P = P^t`
4. ⇒ t ∈ N, x^{-1}y = x^{-1}t^{-1}xt ∈ P ∩ N'
5. Focal Subgroup Theorem: `P ∩ G' ⊆ P ∩ N'`
6. G' = G (simple) ⇒ P ⊆ N'

## Feit-Hall-Thompson 1960 paper との関係

- **1960 Feit-Hall-Thompson** paper: "Finite groups in which the centralizer of any non-identity element is nilpotent" — Pacific J. Math.
- **FT 1963 paper** で CN を一般化, BG 1994 が局所解析部の clean re-presentation
- **BG App.D** = 1960 の CN-theorem を BG §1-§9 framework で 4 ページに短縮するガイド (Gorenstein 14 章全体の代替)

## Suzuki 1957 との関係

Suzuki 1957 ("The nonexistence of a certain type of simple groups of odd order"): CN-groups の特殊 case (centralizer of involution = cyclic) を扱う先駆的論文. BG App.D は Suzuki path ではなく Feit-Hall-Thompson path を採る.

注: Peterfalvi 付録 D "On Suzuki 2-Groups" は別物 (Higman 分類, FT 本筋外).

## FT 本筋との関係

```
Phase 1-4 (FT 本流):
  Isaacs → BG §1-§16 → Peterfalvi §1-§16 → FeitThompson メイン

App.D (オフトピック):
  BG §1-§9 + Lem D.1, D.2 + (G) Ch.14 → CN-theorem (1960)
```

**App.D は Phase 4 メイン定理に経由しない**. FeitThompson メイン定理は CN 仮定を使わない一般 odd order ⇒ solvable を確立する.

## mathlib カバレッジ

| 概念 | mathlib | 新規 |
|------|---------|------|
| `IsCNGroup` 定義 | 未収載 | 新規 |
| `IsNilpotent (Subgroup.centralizer)` | 既存 (`Subgroup.lean`) | OK |
| **Lem D.1 (TI-Sylow for min simple CN)** | 完全新規 | 新規 |
| **Lem D.2 (P ⊆ N')** | 完全新規 | 新規 |
| 3-step group (Gorenstein 14.1.6) | mathlib 未収載 | 新規 (大規模) |
| Thm 6.2 (Phase 2a §6 経由) | Phase 2a 完了で OK | OK |
| Thm 1.17 Focal Subgroup | mathlib `Focal.lean` | OK |

**結論**: App.D 形式化は **Lem D.1, D.2 + 3-step group 概念** が新規実装の柱. CN-condition + Lem D.1/D.2 で合計 ~300-400 行 Lean 推定. ただし 3-step group は (G) Ch.14 の翻訳を要し、形式化コスト高い.

## Phase 2 形式化着手順 (skip 推奨)

| 段階 | 内容 | 時間 | 必須? |
|------|------|------|-------|
| - | `IsCNGroup` 定義 + 基本性質 | 1 日 | No (skip) |
| - | Lem D.1 (TI-Sylow) | 3-5 日 | No |
| - | Lem D.2 (P ⊆ N') | 1-2 日 | No |
| - | 3-step group + (G) 14.1.6 翻訳 | 2-3 週間 | No (大規模) |
| - | CN-theorem 完成 | 1 週間 | No |

**Phase 2 推奨**: **完全 skip**. Phase 4 (FeitThompson メイン定理完成) 後の発展材料として保留. CN-theorem 自体は FT より弱い結果なので、FT 完成後に独立 module として実装する選択もある.

## 未解決 / TODO

1. **3-step group の定義**: Gorenstein 14.1.6 を直接形式化するか、BG App.D 内 inline 展開するか
2. **L5072 MISSING_PAGE_EMPTY:169**: App.D 末尾の 1 ページ blank, 内容は L5070 で完結している模様
3. **(G) Lem 10.1.3 への依存**: Gorenstein 経由の補助補題, mathlib or Isaacs での対応物確認要
4. **App.B Puig L(S) 経路**: Lem D.1 で「one may substitute L(P) for J(P)」と App.B 代替経路を提示, 形式化時にどちらを採るか
5. **Feit _Characters of Finite Groups_ (27.6) との対応**: Lem D.1 のオリジン引用, FT 形式化では不要だが歴史的興味あり

---

**作成**: 2026-05-22. **出典**: `references/bg/local-analysis.mmd` L5006-5073, `notes/bg/_overview.md`, `notes/bg/s06_additional.md` (Thm 6.2 参照).

**判定**: Phase 2 形式化スコープ外. Phase 4 完了後の発展材料として archive.
