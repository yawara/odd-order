# BG 完全形式化 — 番号 census と逐条監査 (2026-08-08 開始)

tracker = [issue 0177](../../issues/0177-bg-full-formalization.md)。
前身 = [0172 Peterfalvi (284 件)](../../issues/closed/0172-peterfalvi-full-formalization.md)
/ [0176 Isaacs (305 件)](../../issues/closed/0176-isaacs-full-formalization.md)、いずれも完了。

## 1. ⚠ BG は番号体系が前 2 冊と違う

Isaacs / Peterfalvi は `N.M.` を行頭に置く形式だったが、**BG は 2 系統ある**:

1. **`(N.M)` を単独行に置くラベル** — **証明内の主張ラベル**であって定理番号ではない。
   §3 の証明中に `(3.6)` `(3.7)` `(3.8)` が並び、後段が「by (3.6)」と参照する。
   ⚠ **これを定理番号と取り違えると件数が数倍に膨らむ**。
2. **`Kind N.M.` / `Kind N.M (帰属).`** — こちらが番号付き結果。
   `Theorem` / `Proposition` / `Lemma` / `Corollary` の 4 種。

さらに **Theorems A–E** (章番号を持たない主定理、`Theorem A` のように単独行) と
**Appendix A–E** (`Kind X.N` 形式) を持つ。

### 抽出パターン

```python
def sp(w): return r'\s*'.join(w)          # OCR が T h e o r e m と分解するため
kinds = "|".join(sp(w) for w in ["Theorem","Proposition","Lemma","Corollary"])
pat = re.compile(r'^\s*(' + kinds + r')\s+(\d(?:\s*\d)?)\s*\.\s*(\d(?:\s*\d)?)(?!\s*\.\s*\d)')
```

⚠ **`(?!\s*\.\s*\d)` が必須** — `Theorem 6.4.1` のような **Gorenstein の引用**を除外する
(BG は "**G**, Thm X.Y.Z" 形式で Gorenstein を多用する)。

## 2. 実測ベースライン (2026-08-08)

| 節 | 件数 | 備考 |
|---|---|---|
| §1 | 22 | |
| §2 | 7 | |
| §3 | 10 | |
| §4 | **20** | ⚠ 4.1 は OCR が `Lemma-4.1.` (ハイフン) と書き出しており空白許容パターンでも漏れる |
| §5 | 7 | |
| §6 | 7 | |
| §7 | 6 | ⚠ 7.1 は OCR が `L e m m a 7.1.` (文字分解) |
| §8 | 1 | |
| §9 | 6 | |
| §10 | 14 | |
| §11 | 7 | |
| §12 | 19 | |
| §13 | 13 | |
| §14 | 12 (+1?) | ⬜ **14.11 が未発見** — ページ画像で要確認 |
| §15 | 9 | |
| §16 | 1 | |
| **小計** | **161** | (14.11 を入れると 162) |

**Theorems A–E**: 5 件 (`Theorem A` L6615 / `B` L6602 / `C` L6653 / `D` L6669 / `E` L6692)。

**補章**: `Kind X.N` が 14 件 (A: 2-5 / B: 2-4 / C: 2-3 / D: 2 / E: 2-5)。
⬜ **各補章の `.1` が未発見** — 補章の第 1 結果は別形式 (章タイトル直後など) の可能性。要確認。

⟹ **暫定合計 ≈ 180 件** (§1-§16 の 161-162 + Theorems A-E の 5 + 補章 14+)。

## 3. ⚠ この census が測っていないもの (0172 / 0176 と同じ)

1. **特殊化債務** — 書籍より狭い仮説
2. **部分被覆** — 多条項の一部だけ / TFAE の条項数不足
3. **packaging 差** — 条項はすべて在るが書籍の statement の形になっていない
4. **mathlib 被覆の未記録** — Isaacs で主役だった型。BG は FT 固有の内容が多いので前 2 冊より
   少ないと予想されるが、**§1 (Preliminary Results) は標準的な有限群論**なので要確認。

## 4. 逐条監査

### §1 Preliminary Results (22 件、書籍 pp.1-30) — **監査完了 (2026-08-08)**、補充ゼロ

**22/22 参照あり**。`S01_FrattiniBurnside.lean` の file header が §1A-§1G の全番号を
Isaacs / mathlib / 本 repo の 3 列で対応づける**マスター対応表**を持っており、それを
実体で裏取りした。

⚠ **stale 注記を 2 件訂正** — 対応表に「**Phase 1 待ち**」のまま残っていた:

| 番号 | 表の記載 | 実体 |
|---|---|---|
| **Thm 1.8** (Burnside, operator on `p`-group) | 「mathlib: (Ch.1 §1B TODO) / 本ファイル: **Phase 1 待ち**」 | ✅ `S01_BurnsideOperator.burnside_operator` (元形も :153) |
| **Thm 1.11** | 「mathlib: Phase 1 Ch.4 §4D / 本ファイル: **Phase 1 待ち**」 | ✅ `Isaacs/Ch04_Commutators/Main/BaerTrick.lean:254` (docstring が「= BG Thm 1.11」と明記) |

🚨 **1.8 は同一ファイル内で矛盾していた** — :63 の表が「Phase 1 待ち」なのに、
**同じファイルの :152** が `Thm 1.8` `burnside_operator` ⭐ sorry-free` と記録していた。
⟹ **1 つの file 内でも注記どうしが食い違う**。Isaacs 監査で「注記は判定の証拠ではない」を
確立したが、BG ではさらに強く「**同じ file の別の注記とすら一致しない**」ことがある。

⚠ **1.11 は Isaacs 側のディレクトリに在る** — owner chapter 規則。BG のディレクトリだけ
見ると「未形式化」と誤判定する (Isaacs 2.20 / 3.15 / 3.23 と同じ型で通算 4 回目)。

その他の §1 は mathlib 被覆と repo 実装が対応表どおり:
`Lem 1.7` は 4 条項 (a)/(b)(c⇒)(d⊇)/(c⇐)/(d⇐) に分けて全て sorry-free、
`Thm 1.13` = `GroupTheory.CriticalSubgroup` の `thompson_critical_omega`、
§1F (`Thm 1.17`/`1.18`/`Cor 1.19`/`Thm 1.20`) は **mathlib 直接**。

⟹ **§1 全 22 件被覆・補充ゼロ**。

### §2-§16 + Theorems A-E + 補章 — 未着手 (次の入口 = §2、7 件)
