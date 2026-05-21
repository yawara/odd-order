# Isaacs Ch.1: Sylow Theory — mini-roadmap

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Ch.1 (pp. 1-44).
形式化先: [`OddOrder/Isaacs/Ch01_Sylow.lean`](../../OddOrder/Isaacs/Ch01_Sylow.lean).

## 全 46 定理の分布 + 進捗

| § | 内容 | Isaacs 番号 | 進捗 |
|---|---|---|---|
| 1A | 群作用と Fundamental Counting Principle | Thm 1.1–1.6 (6 件) | 1.1, 1.2, 1.3, 1.4, 1.5, 1.6 ✅ |
| 1B | Sylow E, Cauchy | Thm 1.7–1.10 (4 件) | 1.7, 1.8, 1.9, 1.10 ✅ |
| 1C | Sylow C / D, Frattini argument | Thm 1.11–1.18 (8 件) | 1.11-1.15, 1.17, 1.18 ✅ / 1.16 TODO |
| 1D | 冪零群, Fitting 部分群 `F(G)` | Thm 1.19–1.29 (11 件) | 1.26 ✅, opCore + Problem 1B.2 + fitting + fitting.normal ✅, 1.28(b) ✅ / 1.19-1.25, 1.27, 1.28(a), 1.29 TODO |
| 1E | 小位数群, 指数 2 正規部分群 | Thm 1.30–1.36 (7 件) | 1.34, 1.35 ✅ / 1.30-1.33, 1.36 TODO |
| 1F | Brodkey (abelian Sylow) | Thm 1.37–1.40 (4 件) | TODO (低優先度) |
| 1G | Chermak–Delgado | Thm 1.41–1.46 (6 件) | TODO (BG/Peterfalvi 引用無ければ省略可) |

## mathlib 対応表

直接ラッパー可能 (薄い再述で済む):

| Isaacs | mathlib | 備考 |
|---|---|---|
| Thm 1.1   | `Subgroup.normalCore_eq_ker` | perm action `G → Sym(G⧸H)` の核 = `H.normalCore` (実装済) |
| Thm 1.4   | `MulAction.orbitEquivQuotientStabilizer` | orbit ≃ G ⧸ stabilizer (実装済) |
| Cor 1.5   | `ConjClasses.card_carrier` | 共役類サイズ = `|G|/|C_G(x)|` (= `[G:C_G(x)]`) |
| Thm 1.7   | `Sylow.nonempty` | Sylow E (実装済) |
| Lemma 1.8 | `Choose.choose_pow_mul_pow_mul_modEq_choose_nat` (b:=1) | `C(p^a m, p^a) ≡ m mod p` (実装済) |
| Cor 1.9   | `exists_prime_orderOf_dvd_card'` | Cauchy (実装済) |
| Lemma 1.10 | `Subgroup.normal_of_characteristic_of_normal` インスタンス | char in normal ⇒ normal (実装済) |
| Thm 1.12  | `Sylow.orbit_eq_top` + `Sylow.equiv` | Sylow C (共役) |
| Lemma 1.13 | (探索: `Subgroup.normalizer_sup_eq_top` ?) | Frattini argument |
| Cor 1.17  | `card_sylow_modEq_one` | n_p ≡ 1 (mod p) |
| Cor 1.25  | (Cor 1.24 の系) | p^b ∣ |G| ⇒ |L|=p^b 部分群存在 |
| Thm 1.26  | `Group.IsNilpotent` の特性化と既存補題で組む | 冪零 ⇔ Sylow 全正規 |
| Lemma 1.34 | 自前 (`MulAction.toPermHom` + `Equiv.Perm.sign` + `Int.units_eq_one_or` + `Subgroup.index_ker`) | 奇に作用 ⇒ index 2 (実装済) |
| Thm 1.35  | Lemma 1.34 + Cauchy + `Equiv.Perm.sign_of_pow_two_eq_one` | \|G\|=2n, n 奇 ⇒ index 2 (実装済) |

新規実装が必要な主要項目 (mathlib 未収載 — Phase 1 の山場):

* **§1D Def + Thm 1.28** Fitting 部分群 `Fit(G)` — 最大正規冪零部分群.
  全冪零正規部分群の sup として定義し, sup が再び冪零であることを示す.
  Lemma 1.27 (互いに素な位数の正規部分群の積は直積) → Cor 1.28 (F(G) の冪零性).
* **§1E Thm 1.35** `|G|=2n` (n 奇) ⇒ 指数 2 正規部分群.
  → Feit-Thompson の "p=2 の最易 case".  Lemma 1.34 ("奇に作用する元" の存在) + 正則表現を経由.
* **§1G Chermak–Delgado** measure `m_G(H) = |H|·|C_G(H)|` と最大値部分群族 `L(G)`.
  これは Isaacs 独立の話題で BG/Peterfalvi 直依存はない可能性が高い (要確認).
  優先度低めで後回し可.

## 着手順 (実績 + 案)

依存と Phase 1 全体 (Ch.1 → Ch.2 → ... → Ch.9) を考えると:

1. **§1A の Thm 1.1, 1.4** ✅ (2026-05-21, commit `dc21ce9`)
2. **§1B 全て (Thm 1.7, Lemma 1.8, Cor 1.9, Lemma 1.10)** ✅ — mathlib 直ラッパー
3. **§1E Lemma 1.34, Thm 1.35** ✅ — 符号写像 `G → Sym(G) → ℤˣ` 経由で実装
4. **§1A 残り (Cor 1.2, 1.3, 1.5, 1.6)** ← 次の候補. ConjAct 周辺の練習
5. **§1C (Thm 1.11-1.18: Sylow C/D, Frattini)** — mathlib 直 + 小工夫
6. **§1D 前半 (1.19-1.27: 冪零群の基本)** — mathlib `IsNilpotent` と擦り合わせ
7. **§1D Fitting `F(G)` (Def + Cor 1.28, 1.29)** — 本章の主要新規実装. 設計済み ([`ch01_sylow_d_fitting.md`](ch01_sylow_d_fitting.md))
8. **§1E 残り (Thm 1.30-1.33, 1.36)** — 小位数の構造定理
9. **§1F, §1G** — 後回し可 (FT 本筋の必須性が低い)

## 未解決の疑問

* Isaacs § 1F は明示的なセクションヘッダが mmd に無い (1E から 1G の間).
  本では p.31 付近で "1F" の表記がある可能性. 後で PDF 確認.
* §1G Chermak–Delgado は BG/Peterfalvi で参照されているか? 引用が見つからなければ
  Phase 1 から省略可.  → 後で BG/Peterfalvi の mmd を grep "Chermak" で確認.
* `core_G(H)` の Isaacs 表記 vs mathlib `Subgroup.normalCore` の対応は問題なさそう.
  ただし simp 補題が薄いかもしれない (要 lemma 拡充検討).
