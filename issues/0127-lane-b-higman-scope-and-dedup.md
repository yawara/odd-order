---
id: 127
slug: lane-b-higman-scope-and-dedup
title: "HUB: lane b の Higman プログラム — 方針判断 (保留) + 審査で確定した重複 2 件・空 scaffold 4 件"
created: 2026-07-19
owner: hub (①② 実施) / ユーザー裁定待ち (③)
---

# lane b の Higman プログラム — 審査結果と保留中の方針判断

2026-07-19 の hub tick で lane b の新規 1905 行 (`HigmanLowerCentralGraded.lean` 982 /
`HigmanFinalCase.lean` 894) を 4 観点で審査した (honesty / 教科書強度 / 重複 / 粒度、
各指摘は敵対的検証エージェントで再確認)。

## 前提: b の新規コード自体は本物 (問題なし)

- 実 sorry 0。**`structure`/`class` の新規導入が 0** ⟹ opaque-Prop scaffold の隠れ場所が構造上無い
- 仮説パラメータ化した補題は**全て呼び出し側で discharge 済**。hoist パターンではない
- 消費する `HigmanEndomorphismFamily` は `chosenHigmanEndomorphismFamily`
  (`HigmanIdempotentFamily.lean:49`) が存在定理から `choose` で**実構成**している
- **教科書原文と照合済**: 検証エージェントが `references/higman/p83_84_lemmas_1_3.layout.txt` を読み、
  Lemma 3 の主張が仮説単位で一致すると確認。むしろ Lean 側が Higman の暗黙前提 (A の rank ≥ 2) を明示

⟹ **doneness 基準を満たしている**。以下の指摘は「b の新規証明が偽物」という話ではない。

## ① 重複 2 件 (b の新規ファイルが導入) — hub が処理する

issue 9161 を直した 1 コミット後に同じパターンが再発した。

| 新規 | 既存 | 備考 |
|---|---|---|
| `cyclic_finite_unique_order_two` (`HigmanFinalCase.lean:538`) | `Isaacs/Ch05_Transfer/Basic.lean:751` | 名前・signature・証明スクリプトが**完全一致** |
| `lowerCentral_commutatorElement_mul_right_of_class_le_two` (`HigmanLowerCentralGraded.lean:408`) | `Isaacs/Ch04_Commutators/.../BaerTrick.lean:143` (`commutatorElement_mul_right_of_class_le_two`) | statement 逐語一致・証明も局所仮説名の差のみ。**3 コピー目** |

⚠ **両方とも双方が `private`** ゆえ再利用不能で、4 コピー目を構造的に誘発する。
cross-lane (Isaacs = lane a 領域) ゆえ 9161 と同じく **hub が atomic に実施**する。

**着手前に必ず**修飾形の内訳を確定すること (9161 で部分修飾 `S10.` 形を取りこぼしてビルドを落とした):
```bash
grep -rno "[A-Za-z0-9_.]*<名前>" OddOrder/ --include=*.lean | awk -F: '{print $3}' | sort | uniq -c
```

- [ ] `cyclic_finite_unique_order_two` を shared leaf へ集約 (両方 private ゆえ新規 public 化が要る)
- [ ] `lowerCentral_commutatorElement_mul_right_of_class_le_two` を Ch04 BaerTrick の既存版へ repoint
- [ ] full build gate (cross-file ゆえ leaf build では検出不能)

## ② `Suzuki2Groups.lean` (hub file) の 4 sorry は**中身が空** — 削除対象

**b の新規分ではなく既存 debt** だが、実害があるので記録する。

- `SuzukiTypeData (P) [Group P]` は 3 つの `Prop` フィールドを持つだけで、**パラメータ `P` を一度も使わない**
- ⟹ `higman_classification` (`:81`、docstring は「**Peterfalvi Appendix III, Higman theorem**」) は
  `⟨⟨True, True, True⟩, Or.inl trivial⟩` で証明できる**論理的に空虚な命題**
- `typeB_field_model (hB : Prop) : hB → ∃ f : Prop, f` / `typeB_automorphism_structure` も同型のトートロジー
- 4 sorry (`:61, 83, 89, 95`) がここに座っている

**実害** = 教科書引用の docstring + sorry が付いているため、**「あと 4 sorry で Appendix III 完成」に見える**。
CLAUDE.md「opaque-Prop scaffold は形式化と数えない」に該当。

**緩和材料**: file 内コメント (`:43-45`) が「これらは coverage に数えない・cite するな」と明記しており、
grep でも**どの leaf も cite していない**ことを確認済 ⟹ 不健全な土台ではなく死んだ scaffold。

- [ ] issue 2048 / 9160 の統合時に削除する (今すぐ消すと b の active frontier と衝突するため保留)

## ③ ⏸ 保留中の方針判断 — **ユーザー裁定待ち**

**論点**: Peterfalvi は Higman の定理を「it is proved in [Hi]」と**引用しているだけ**で、本文に証明が無い。
CLAUDE.md は「文献引用のみで本文に証明が無い結果・open problem は**恒久対象外にせず低優先繰延**」と
定めている。lane b は現在この Higman の Lemma 1-12 プログラム (実質**4 冊目の原典**) に全能力を投じ、
既に ~24 leaf。一方 3 冊本体には ~90 項目が残っている。

⟹ 規約に照らすと **b は「低優先繰延」対象を最優先で回している**状態。

| 選択肢 | 内容 |
|---|---|
| **継続** | b はこのまま Higman を完遂。仕事の質は審査済みで本物、教科書原文とも照合済み |
| **再配分** | b を 3 冊本体の残項目へ移し、Higman は現状凍結して繰延 |

**hub の見立て**: 規約に従えば**再配分が筋**。ただし (i) b の 24 leaf は sorry-free の実証明で
捨てるのではなく凍結・後日再開になる、(ii) Peterfalvi Appendix III を honest に閉じるには
(axiom 禁止ゆえ) 結局いつか必要になる — の 2 点で判断が割れうるため、レーン 1 本の方向を
変える決定として保留し、ユーザーに提示した (2026-07-19)。**未回答**。

⚠ b は 2026-07-19 に 4 回セッション停止している (自作業 commit が 11:34 → 12:37 → 13:19 → 14:19
で以後途絶)。**再開前に本項を決めるのが効率的** — 再配分なら Higman の途中から復帰させる意味が無い。

## ④ 粒度 (参考、action なし)

Higman* が 10 → **14 ファイル**。[issue 9160](9160-lane-b-leaf-granularity.md) の統合対象が **39% 増**。
新規 2 leaf 自体は 982 / 894 行で 300-1500 の帯に収まり規約準拠。9160 自身が統合を issue 2048 の
完了時まで繰延しているので違反ではないが、「放置すれば解決」ではないことを記録しておく。

## 完了条件

① の重複 2 件が解消し full build green、② が 2048/9160 統合時に削除され、③ が裁定される。

## 参照
- issue 2048 (Suzuki Lemma 5 = b の frontier) / 9160 (leaf 粒度) / 9161 (同型の dedup、実施済)
- CLAUDE.md「進捗の測り方」(opaque-Prop scaffold / 特殊化債務 / 低優先繰延)
