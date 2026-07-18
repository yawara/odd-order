---
id: 1037
slug: wielandt-aut-tower-9-10
title: "Theorem 9.10 Wielandt automorphism tower"
created: 2026-07-18
---

# Theorem 9.10 Wielandt automorphism tower

## 背景

Isaacs §9B の capstone (p. 271, mmd L5006)。`Z(G) = 1` ⇒ automorphism tower
`G_1 = G`, `G_{i+1} = Aut(G_i)` は同型を除いて有限種。§9B の解析補題は 2026-07-18 に
全て landed (レーン a):

- 9.11 (`InnerAutomorphisms.lean`): Inn(G) ◁ Aut(G), Z(G)=1 ⇒ C_{Aut}(Inn)=1, Z(Aut)=1。
- 9.12 (`AutTowerBounds.lean` `centralizer_eq_bot_of_chain`): chain の centralizer 消失。
- 9.13 (`OrderBound.lean` `card_le_of_normal_of_centralizer_eq_bot`):
  **S ◁ G**, C_G(S)=1 ⇒ |G| ≤ |Z(S^∞)|·|Aut(S^∞)| (normal 版, divisibility も)。
- 9.14 (`AutTowerBounds.lean`): N ◁ G, C_G(N)≤N ⇒ |G| ∣ |Z(N)||Aut(N)| / |N|!。
- 9.21/9.22 (`Schenkman.lean`): Schenkman **S ◁ G**, C_G(S)=1 ⇒ C_G(S^∞) ≤ S^∞。
- 9.16/9.18 (`NilpotentResidual.lean`/`SubnormalSocle.lean`): **S ◁◁ G** ⇒
  F(G), E(G) ≤ N_G(S^∞) (subnormal 版, F* 経由 bound 用)。

## ✅ 「normal/subnormal ギャップ」の正体 = mmd の OCR 崩れ (2026-07-18 決着)

**旧記述は誤りだった**: 「書籍 9.13 は `S ◁ G` を要求するが tower では `G_1` は
subnormal 止まりなので橋渡しが行間」という分析は、**mmd の抽出ミスに基づく誤診**。

**PDF (原典) を直接確認した結果 (p. 281 / p. 283, PDF page 294 / 296)**:

- **9.13 Theorem**: _Let `S ⊲⊲ G`_ … ← **subnormal**
- **9.21 Theorem (Schenkman)**: _Let `S ⊲⊲ G`_ … ← **subnormal**
- 対照: 9.15 は _`S ⊲⊲ G` and `F ⊲ G`_ と **両方の記号が並ぶ**ので誤読の余地なし。
  9.20 proof の `M ⊲ G`、9.22 proof の `C ⊲ G` は単一 `⊲` (normal)。

⚠ **`references/isaacs/finite-group-theory.mmd` は subnormal `⊲⊲` を単一の
`\triangleleft` に潰している** (Nougat の抽出崩れ)。`pdftotext` では `⊲⊲` が `«`、
`⊲` が `<` に落ちるので、**grep で区別する場合は `«` を見る**のが早い。

裏付け: 9.16/9.18 も mmd では `S \triangleleft G` だが、地の文が
"if `S` is an arbitrary **subnormal** subgroup of `G`" / "normalizes the **subnormal**
subgroup `S̄`" と明言しているため、本 repo では正しく `IsSubnormal` で形式化されている。
**地の文が曖昧だった 9.13 / 9.21 だけが normal 版になった** — これが唯一の齟齬。

→ **数学的ギャップは存在しない**。tower は書籍どおり 9.13 (subnormal 版) を
`S = G_1`, ambient `G_i` で当てれば閉じる (`C_{G_i}(G_1) = 1` は 9.12)。
やるべきは **9.21 と 9.13 の subnormal 版への一般化**。

## やること

- [x] normal/subnormal ギャップを原文精読で確定 → **OCR 崩れと判明** (上記)。
- [ ] **(A) 9.21 (Schenkman) を subnormal 版に一般化** (`Schenkman.lean` `schenkman_aux`)。
      現行の帰納核は `S.Normal` を要求。書籍 p. 283 の proof は元々 subnormal 用で、
      本 repo が normal に落としたことで下記のステップが**消えて**いる:

      > "It follows that there are no subgroups `H` with `S < H < G`, and
      >  **since `S ⊲⊲ G`, we conclude that `S ◁ G`**"

      改修点:
      1. 仮説 `S.Normal` → `S.IsSubnormal`。
      2. `hSnormal.subgroupOf H` (2 箇所) → mathlib `Subgroup.IsSubnormal.subgroupOf`。
      3. **`hRnormal`/`hCnormal` (現行 L372-373) は前倒しできない**:
         `R = S^∞` は `S` に characteristic ゆえ `S ◁◁ G` では `R ◁ G` が出ない。
         ただし `S` は `R` を正規化し `C = C_G(R)` も正規化するので、
         **`R`,`C` は `G₀ = S ⊔ C` に normal**。現行proof は既に
         `by_cases hSC : S ⊔ C = ⊤` で分岐し else 側は `G₀` へ再帰しているので、
         normality 宣言を **`S ⊔ C = ⊤` 分岐の中へ移す**だけでよい (その分岐では
         `G₀ = ⊤ = G` ゆえ両者 normal)。
      4. `hinterval` (中間部分群なし, 現行 L405) の後に **`S.Normal` を導出**:
         `S = ⊤` なら自明。さもなくば mathlib
         `Subgroup.IsSubnormal.exists_normal_and_le_and_lt_top_of_ne` で
         `K` normal, `S ≤ K`, `K < ⊤` を取り、`hinterval K` から `K = S`。
         以降 (L428 `IsCyclic (G ⧸ S)` 〜 L478) は**現行のまま通る**。
      5. Dedekind (`OddOrder/Mathlib/Subgroup.lean`
         `inf_sup_eq_sup_inf_of_normal_of_le`, `[E.Normal]` を要求) は現行
         `(E := S)` で呼んでいる → `S` がまだ normal でない時点なので
         **`(E := C)` 版に組み替える**か、`S ≤ H` のみで済む Dedekind
         (`H ⊓ (S·C) = S·(H ⊓ C)`、集合積では normality 不要) を別途用意する。
         ※ この分岐では `C ◁ G` は言える (`S` も `C` も `C` を正規化し `S ⊔ C = ⊤`)。

- [ ] **(B) 9.13 を subnormal 版で証明** (`OrderBound.lean`)。
      現行 `card_le_of_normal_of_centralizer_eq_bot` は 9.14 を `N = S^∞` に**直接**当てる
      近道 (`S^∞ ◁ G` が要る) なので normal 専用。**現行版はより鋭い bound
      (`|G| ≤ |Z(S^∞)||Aut(S^∞)|`, 階乗なし) なので残す**。
      subnormal 版は書籍 p. 281 の F* 経由ルートで別途:
      1. `|N_G(S^∞)| ≤ |Z(S^∞)|·|Aut(S^∞)|` — `N_G(S^∞)` の中で 9.14
         (`S^∞` はそこで normal) + (A) の subnormal 9.21
         (`S ◁◁ N_G(S^∞)`, `C_{N_G(S^∞)}(S) = 1`)。
      2. `F*(G) = F(G)E(G) ≤ N_G(S^∞)` — **既存の subnormal 版 9.16/9.18**。
      3. `C_G(F*(G)) ≤ F*(G)` (9.8) + 9.14 ⇒ `|G| ≤ |F*(G)|!`。
      ⇒ `|G| ≤ (|Z(S^∞)|·|Aut(S^∞)|)!` (階乗付き, `S` の同型型のみに依存)。

- [ ] **(C) tower 本体 9.10**:
      - recursive type family `autTowerType : ℕ → Type u` (`0 ↦ G`, `n+1 ↦ MulAut (·)`)
        + 各段の `Group` instance (再帰) + centerless の伝播 (9.11d)。
      - 埋め込み鎖 `G_i ↪ G_{i+1}` (Inn) と `G_1 ◁◁ G_i`、`C_{G_i}(G_1) = 1` (9.12)。
      - (B) を `S = G_1`, ambient `G_i` で当てて `|G_i| ≤ (|Z(G_1^∞)||Aut(G_1^∞)|)!`
        (i に依らない一様上界) → `∃ n, ∀ i, Nat.card (autTowerType G i) ≤ n`。
      - leaf 例: `AutTower.lean` (import OrderBound + InnerAutomorphisms)。

## 完了条件

`Theorem 9.10` を sorry-free/axiom-clean で landing (`∃ n, ∀ i, |G_i| ≤ n` 形)。
full build green + AxiomsCheck OK。

## 参照

- references/isaacs/finite-group-theory.pdf **PDF p.294 (書籍 p.281) = 9.13/9.15**,
  **PDF p.296 (書籍 p.283) = 9.21/9.22** — ⚠ mmd でなく PDF を見ること (上記 OCR 崩れ)
- PDF ページ = 書籍ページ + 13
- OddOrder/Isaacs/Ch09_MoreSubnormality/{Schenkman,OrderBound,AutTowerBounds,
  NilpotentResidual,SubnormalSocle}.lean
- mathlib `Mathlib/GroupTheory/IsSubnormal.lean` (`subgroupOf`, `trans`,
  `exists_normal_and_le_and_lt_top_of_ne`)
