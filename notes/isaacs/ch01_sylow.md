# Isaacs Ch.1: Sylow Theory — mini-roadmap

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Ch.1 (pp. 1-44).
形式化先: [`OddOrder/Isaacs/Ch01_Sylow.lean`](../../OddOrder/Isaacs/Ch01_Sylow.lean).

## 全 46 定理の分布

| § | 内容 | Isaacs 番号 | 行 (mmd) |
|---|---|---|---|
| 1A | 群作用と Fundamental Counting Principle | Thm 1.1–1.6 (6 件) | 116-187 |
| 1B | Sylow E, Cauchy | Thm 1.7–1.10 (4 件) | 242-? |
| 1C | Sylow C / D, Frattini argument | Thm 1.11–1.18 (8 件) | ?-? |
| 1D | 冪零群, Fitting 部分群 `F(G)` | Thm 1.19–1.29 (11 件) | ?-? |
| 1E | 小位数群, 指数 2 正規部分群 | Thm 1.30–1.36 (7 件) | ?-? |
| 1F | Brodkey (abelian Sylow) | Thm 1.37–1.40 (4 件) | ?-? |
| 1G | Chermak–Delgado | Thm 1.41–1.46 (6 件) | ?-? |

## mathlib 対応表

直接ラッパー可能 (薄い再述で済む):

| Isaacs | mathlib | 備考 |
|---|---|---|
| Thm 1.1  | `Subgroup.normalCore_eq_ker` | perm action `G → Sym(G⧸H)` の核 = `H.normalCore` |
| Thm 1.4  | `MulAction.orbitEquivQuotientStabilizer` | orbit ≃ G ⧸ stabilizer |
| Cor 1.5  | `ConjClasses.card_carrier` | 共役類サイズ = `|G|/|C_G(x)|` (= `[G:C_G(x)]`) |
| Thm 1.7  | `Sylow.nonempty` | Sylow E |
| Cor 1.9  | `exists_prime_orderOf_dvd_card` | Cauchy |
| Thm 1.12 | `Sylow.orbit_eq_top` + `Sylow.equiv` | Sylow C (共役) |
| Lemma 1.13 | (探索: `Subgroup.normalizer_sup_eq_top` ?) | Frattini argument |
| Cor 1.17 | `card_sylow_modEq_one` | n_p ≡ 1 (mod p) |
| Cor 1.25 | (Cor 1.24 の系) | p^b ∣ |G| ⇒ |L|=p^b 部分群存在 |
| Thm 1.26 | mathlib `Group.IsNilpotent` の特性化と既存補題で組む | 冪零 ⇔ Sylow 全正規 |

新規実装が必要な主要項目 (mathlib 未収載 — Phase 1 の山場):

* **§1D Def + Thm 1.28** Fitting 部分群 `Fit(G)` — 最大正規冪零部分群.
  全冪零正規部分群の sup として定義し, sup が再び冪零であることを示す.
  Lemma 1.27 (互いに素な位数の正規部分群の積は直積) → Cor 1.28 (F(G) の冪零性).
* **§1E Thm 1.35** `|G|=2n` (n 奇) ⇒ 指数 2 正規部分群.
  → Feit-Thompson の "p=2 の最易 case".  Lemma 1.34 ("奇に作用する元" の存在) + 正則表現を経由.
* **§1G Chermak–Delgado** measure `m_G(H) = |H|·|C_G(H)|` と最大値部分群族 `L(G)`.
  これは Isaacs 独立の話題で BG/Peterfalvi 直依存はない可能性が高い (要確認).
  優先度低めで後回し可.

## 着手順 (案)

依存と Phase 1 全体 (Ch.1 → Ch.2 → ... → Ch.9) を考えると:

1. **1A 完了** (1.1, 1.4 ラッパー済, 1.2/1.3/1.5/1.6 を仕上げる) — ConjAct 周辺の練習
2. **1B 完了** (Sylow E, Cauchy ラッパー) — mathlib 直
3. **1C 完了** (Sylow C/D, Frattini) — mathlib 直 + 小工夫
4. **1D の前半 1.19-1.27** (冪零群の基本) — mathlib 既存と擦り合わせ
5. **1D の Fitting `F(G)`** — 本章の主要新規実装. ここで時間を使う.
6. **1E 1.30-1.34, 1.36** — 小位数の構造定理 (FT に必須ではないが Isaacs 本文流に揃える)
7. **1E Thm 1.35** — FT の "2-part" の予兆として面白い
8. **1F, 1G** — 後回し可  (FT 本筋の必須性が低い)

## 未解決の疑問

* Isaacs § 1F は明示的なセクションヘッダが mmd に無い (1E から 1G の間).
  本では p.31 付近で "1F" の表記がある可能性. 後で PDF 確認.
* §1G Chermak–Delgado は BG/Peterfalvi で参照されているか? 引用が見つからなければ
  Phase 1 から省略可.  → 後で BG/Peterfalvi の mmd を grep "Chermak" で確認.
* `core_G(H)` の Isaacs 表記 vs mathlib `Subgroup.normalCore` の対応は問題なさそう.
  ただし simp 補題が薄いかもしれない (要 lemma 拡充検討).
