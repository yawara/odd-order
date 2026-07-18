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
- 9.13 (`OrderBound.lean`): **S ◁◁ G** (原典どおり), C_G(S)=1 ⇒
  |G| ≤ (|Z(S^∞)|·|Aut(S^∞)|)! (`card_le_factorial_of_isSubnormal`, 2026-07-18)。
  normal 特殊化 `card_le_of_normal_of_centralizer_eq_bot` は階乗なしでより鋭い。
- 9.14 (`AutTowerBounds.lean`): N ◁ G, C_G(N)≤N ⇒ |G| ∣ |Z(N)||Aut(N)| / |N|!。
- 9.21/9.22 (`Schenkman.lean`): Schenkman **S ◁◁ G** (原典どおり), C_G(S)=1 ⇒
  C_G(S^∞) ≤ S^∞ (`centralizer_nilpotentResidual_le_of_isSubnormal`, 2026-07-18)。
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
- [x] **(A) 9.21 (Schenkman) を subnormal 版に一般化 — 完了 (2026-07-18)**
      `centralizer_nilpotentResidual_le_of_isSubnormal`. 実装は下記の見込みどおり
      (normality を `S ⊔ C = ⊤` 分岐へ移動 / `hinterval` から `S.Normal` を導出 /
      Dedekind は `C` 側 normal の姉妹形 `inf_sup_eq_sup_inf_of_normal_right_of_le` を新設)。
      normal 版は特殊化として残置。

  <details><summary>当初の実装計画 (記録)</summary>

- [x] ~~**(A) 9.21 (Schenkman) を subnormal 版に一般化**~~ (`Schenkman.lean` `schenkman_aux`)。
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

  </details>

- [x] **(B) 9.13 を subnormal 版で証明 — 完了 (2026-07-18)**:
      `card_le_factorial_of_isSubnormal` (`OrderBound.lean`)。
      `S ◁◁ G`, `C_G(S) = 1` ⇒ `|G| ≤ (|Z(S^∞)|·|Aut(S^∞)|)!`。
      中間段 `card_normalizer_nilpotentResidual_le` (`|N_G(S^∞)| ≤ |Z(S^∞)|·|Aut(S^∞)|`)
      を分けて置いた。書籍 p.281 の F* 経由ルートそのまま:
      subnormal 9.21 を `↥N_G(S^∞)` で適用 → 9.14 → 9.16/9.18 で `F*(G) ≤ N_G(S^∞)`
      → 9.8 + 9.14 階乗形。
      副産物: `mulAutEquivCongr` (`AutTowerBounds.lean`) — `e : A ≃* B` から
      `Aut(A) ≃ Aut(B)` (mathlib に `MulAut` の同型同変性が無い; 9.10 でも使う)。
      `centralizer_subgroupOf_eq_bot` を `private` から public 化 (ファイル跨ぎ利用)。
      **normal 版 `card_le_of_normal_of_centralizer_eq_bot` は階乗なしでより鋭いので残置。**

  <details><summary>当初の実装計画 (記録)</summary>

- [x] ~~**(B) 9.13 を subnormal 版で証明**~~ (`OrderBound.lean`)。
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

  </details>

- [x] **(C) tower 本体 9.10 — 完了 (2026-07-18)**: `AutTower.lean`
      `exists_card_autTowerType_le`。`Z(G)=1` の有限群で `∃ n, ∀ i, |G_i| ≤ n`
      (上界 `(|Z(G^∞)|·|Aut(G^∞)|)!`)。full build green (4426 jobs), axiom-clean。

      構成の要点:
      - `GroupPkg` で型と `Group` instance を**同時再帰** (型だけの再帰では
        `MulAut (G_n)` が形成できない)。`autTowerType_zero/_succ` は共に `rfl`。
      - 鎖は `chainAux G m k j` (環境を `m+k` に固定し `j` はパラメータ)。
        `(autTowerEmbLe (j ≤ r)).range` 版だと `m+(k+1)` ↔ `(m+1)+k` の付け替えが
        4 条件すべてに波及するため不採用 (`autTowerEmbLe` 自体は残置)。
      - 9.12 の 4 仮説はいずれも「上端 = 9.11 そのもの / 帰納段 = map で押す」。
        帰納段用に `map_le_normalizer_map` と `centralizer_map_inf_map_eq_bot` を新設。
      - `IsSubnormal` は `IsSubnormal.step` が上から降ろす形なので `j + d = k` の
        `d` で帰納。
      - 一様上界は subnormal 版 9.13 + `nilpotentResidualChainAuxEquiv` で `k` を消す。
        `|Z|`/`|Aut|` の読み替えは 9.13 で作った `centerCongr`/`mulAutEquivCongr`。

  <details><summary>当初の実装計画 (記録)</summary>

- [x] ~~**(C) tower 本体 9.10**~~:
      - recursive type family `autTowerType : ℕ → Type u` (`0 ↦ G`, `n+1 ↦ MulAut (·)`)
        + 各段の `Group` instance (再帰) + centerless の伝播 (9.11d)。
      - 埋め込み鎖 `G_i ↪ G_{i+1}` (Inn) と `G_1 ◁◁ G_i`、`C_{G_i}(G_1) = 1` (9.12)。
      - (B) を `S = G_1`, ambient `G_i` で当てて `|G_i| ≤ (|Z(G_1^∞)||Aut(G_1^∞)|)!`
        (i に依らない一様上界) → `∃ n, ∀ i, Nat.card (autTowerType G i) ≤ n`。
      - leaf 例: `AutTower.lean` (import OrderBound + InnerAutomorphisms)。

### (C) 鎖の作り方 — 設計メモ (2026-07-18, 実装前に確定)

⚠ **素朴な `S i := (autTowerEmbLe (i ≤ r)).range` は筋が悪い**。
`S m ◁ S (m+1)` を出すには
`embLe (m ≤ r) = embLe (m+1 ≤ r) ∘ autTowerStep m` の分解が要るが、
これは `m + (k+1)` と `(m+1) + k` の付け替えを含む。Lean の `Nat.add` は
第 2 引数で再帰するので前者は定義的簡約するが後者はしない (`Nat.succ_add` は帰納法)。
結果として分解補題ごとに transport が要り、鎖の 4 条件すべてに波及する。

**採る形: 環境そのものを再帰で作り、`j` はパラメータのまま持つ**。

```
def chainAux (m : ℕ) : ∀ k : ℕ, ℕ → Subgroup (autTowerType G (m + k))
  | 0,     _ => ⊤
  | k + 1, j => if k + 1 ≤ j then ⊤
                else (chainAux m k j).map (autTowerStep G (m + k))
```

`chainAux 0 r j` = `G_j` の `G_r` での像 (`j ≥ r` なら `⊤`)。検算:
`chainAux 0 1 0 = ⊤.map(step 0) = innAut(G_0)`、`chainAux 0 1 1 = ⊤`、
`chainAux 0 2 1 = ⊤.map(step 1) = innAut(G_1)`、`chainAux 0 2 2 = ⊤`。
**添字の付け替えが一切出ない** (ambient は常に `m + k` の形のまま)。

9.12 の 4 条件は `k` の帰納法で出る。各々、上端 `j + 1 = k + 1` が base、
`j + 1 ≤ k` が帰納段 (`map` で押す):

- `S j ≤ S (j+1)`: 帰納段は `Subgroup.map_mono`、上端は `S (k+1) = ⊤` で自明。
- `S (j+1) ≤ N(S j)`: 上端は `S k = ⊤.map (step (m+k)) = innAut(G_{m+k})` が
  ambient `G_{m+k+1}` に normal (`innAut.normal`)。帰納段は像の正規性の押し出し。
- `C(S j) ⊓ S (j+1) = ⊥`: 上端は `centralizer_innAut_eq_bot` (9.11(c)) そのもの。
  帰納段には **単射 hom の補題**が要る:
  `f` 単射, `C_G(A) ⊓ B = ⊥` ⇒ `C_H(A.map f) ⊓ B.map f = ⊥`。
  (`x = f b` が `f a` 全てと可換 ⟺ `f (b*a) = f (a*b)` ⟺ `b*a = a*b`、単射性より。)
- `S r = ⊤`: `chainAux 0 r r` は `r ≤ r` 側なので定義から `⊤`。

その後 `S 0 ◁◁ G_r` を鎖から `IsSubnormal` に変換 (mathlib `isSubnormal_iff` か
`IsSubnormal.step` の反復) し、`card_le_factorial_of_isSubnormal` を当てる。
`S 0 ≃* G` (単射 hom の像) なので `(S 0)^∞ ≃* G^∞`、上界は `r` に依らない。

## 完了条件

`Theorem 9.10` を sorry-free/axiom-clean で landing (`∃ n, ∀ i, |G_i| ≤ n` 形)。
full build green + AxiomsCheck OK。
→ **達成 (2026-07-18)**。full build 4426 jobs / 0 errors、
`card_autTowerType_add_le` / `exists_card_autTowerType_le` とも 3 axiom (allowlist)。
副産物の 9.21/9.13 subnormal 一般化も axiom-clean。

## 参照

- references/isaacs/finite-group-theory.pdf **PDF p.294 (書籍 p.281) = 9.13/9.15**,
  **PDF p.296 (書籍 p.283) = 9.21/9.22** — ⚠ mmd でなく PDF を見ること (上記 OCR 崩れ)
- PDF ページ = 書籍ページ + 13
- OddOrder/Isaacs/Ch09_MoreSubnormality/{Schenkman,OrderBound,AutTowerBounds,
  NilpotentResidual,SubnormalSocle}.lean
- mathlib `Mathlib/GroupTheory/IsSubnormal.lean` (`subgroupOf`, `trans`,
  `exists_normal_and_le_and_lt_top_of_ne`)
