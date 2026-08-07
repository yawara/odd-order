# Isaacs 完全形式化 — 番号 census と逐条監査 (2026-08-08 開始)

tracker = [issue 0176](../../issues/0176-isaacs-full-formalization.md)。
前身 = [issue 0172](../../issues/closed/0172-peterfalvi-full-formalization.md) (Peterfalvi 全 284 件、完了)。

## 1. 書籍側の番号 census

`references/isaacs/finite-group-theory.pdftotext.txt` から機械抽出。

⚠ **OCR が文字も数字も分解する** (`T h e o r e m` / `2 . 1 4 .`)。素朴な
`^\d+\.\d+\.\s*(Theorem|Lemma|Corollary)` では **29 件取りこぼす**。空白許容の正規表現:

```python
def sp(w): return r'\s*'.join(w)
kinds = "|".join(sp(w) for w in ["Theorem","Lemma","Corollary","Definition","Example","Notation"])
pat = re.compile(r'^\s*(\d(?:\s*\d)?)\s*\.\s*(\d(?:\s*\d)?)\s*\.\s*(' + kinds + r')\b', re.M)
```

| 章 | 件数 | 欠番 |
|---|---|---|
| Ch.1 Sylow | 46 | なし |
| Ch.2 Subnormality | 20 | なし |
| Ch.3 Split Extensions | 36 | なし |
| Ch.4 Commutators | 38 | なし |
| Ch.5 Transfer | 30 | なし |
| Ch.6 Frobenius Actions | 24 | なし |
| Ch.7 Thompson Subgroup | 8 | なし |
| Ch.8 Permutation Groups | 44 | なし |
| Ch.9 More on Subnormality | 31 | なし |
| Ch.10 More Transfer | 28 | なし |
| **合計** | **305** | **各章 1..max が連続** |

種別は全件 Theorem (135) / Lemma (105) / Corollary (65)。

## 2. ⚠ Isaacs 特有の第 4 の残債型 — 「mathlib 被覆の未記録」

Peterfalvi には無かった型。書籍の結果が **mathlib にそのまま在る**とき、repo に実体が無くても
被覆済だが、対応が記録されていないと監査で「未形式化」に誤分類される。

Isaacs Ch.1/Ch.8 のような**標準的な有限群論**では**これが主役**になる。Peterfalvi で効いた
3 型 (番号表記の揺れ / assembly を endpoint と誤認 / stale な自己注記) に加えて、
**「mathlib に在るか」を必ず確認する**。

⟹ 対処は CLAUDE.md のラッパー方針どおり: **薄いラッパーを書かず、対応を記録する**
(section docstring か `notes/` の対応表)。

## 3. 逐条監査

### Ch.8 = 先行実施 (ステップ 1、cite ゼロ 13 件)

正本 = [`ch08_permutation.md`](ch08_permutation.md) の対応表。
**12 件が mathlib 被覆 / 1 件 (8.28) が真の未形式化 → 2026-08-08 に形式化済**
(`Ch08.normal_perm_eq_bot_or_alternating_or_top` + 支持補題 `Ch08.center_perm_eq_bot`;
⚠ `Z(Sym Ω) = 1` も mathlib に無かった)。
⭐ 8.20 は mathlib のほうが一般 / ⚠ 8.21 は mathlib のほうが狭い (translate 限定)。

### Ch.1 (46 件、書籍 pp.1-30) — **進行中**

repo の cite は **46/46 に存在**。うち **docstring のアンカー位置** (`**Isaacs Thm 1.N**`) に
cite があるのは 37 件で、残り 9 件 (**1.1, 1.5, 1.6, 1.7, 1.10, 1.11, 1.17, 1.24, 1.25**) は
アンカー cite なし。実体を確認した結果、**9 件すべて mathlib 被覆**:

| Isaacs | 書籍の主張 | mathlib |
|---|---|---|
| **1.1** | `H ≤ G`、`Ω` = 右剰余類 ⟹ `G/core_G(H) ↪ Sym(Ω)`; `[G:H] = n` なら `↪ Sₙ` | `Subgroup.normalCore_eq_ker` (`Index.lean:818`) + 第 1 同型定理。系の `[G : core] ∣ n!` は repo の `Ch01.normalCore_index_dvd_factorial` |
| **1.5** | 共役類の大きさ `\|K\| = [G : C_G(x)]` | `MulAction.orbitEquivQuotientStabilizer` (`GroupAction/Quotient.lean:174`) を共役作用に適用 |
| **1.6** | `H` の共役の個数 = `[G : N_G(H)]` | 同上 (部分集合への共役作用; Sylow 版は `Sylow.card_eq_index_normalizer`) |
| **1.7** | **Sylow E** — Sylow `p`-部分群の存在 | `Sylow.exists_subgroup_card_pow_prime` (`Sylow.lean:671`) / `Sylow p G` の `Nonempty` |
| **1.10** | `K char N ⊴ G ⟹ K ⊴ G` | `ConjAct.normal_of_characteristic_of_normal` (`ConjAct.lean:270`) — repo も既に使用中 |
| **1.11** | 任意の `p`-部分群 `P` は或る Sylow の共役に含まれる | `IsPGroup.exists_le_sylow` (`Sylow.lean:167`) |
| **1.17** | `n_p(G) ≡ 1 (mod p)` | `card_sylow_modEq_one` (`Sylow.lean:344`) |
| **1.24** | 位数 `p^a` の `p`-群は各 `0 ≤ b ≤ a` で位数 `p^b` の**正規**部分群を持つ | `Sylow.exists_subgroup_card_pow_prime` の `p`-群版 |
| **1.25** | `p^b ∣ \|G\|` ⟹ 位数 `p^b` の部分群が在る | `Sylow.exists_subgroup_card_pow_prime` (`Sylow.lean:671`) |

⚠ **1.24 の「正規」条項は要確認** — 書籍は `L ⊴ P` を主張する。mathlib の
`exists_subgroup_card_pow_prime` が正規性まで返すかは未確認 (返さないなら部分被覆)。

⬜ **残り 37 件の条項ごとの突合は未実施**。とくに 1.12-1.15 / 1.18-1.22 / 1.30-1.31 は
**1 つの file-header docstring が複数番号を列挙**しているだけで、番号ごとの statement が
在るかは個別確認が要る (Peterfalvi の「file docstring の散文が定理の代わり」型)。

### Ch.2-Ch.7, Ch.9-Ch.10 — 未着手
