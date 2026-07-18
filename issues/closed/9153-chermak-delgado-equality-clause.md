---
id: 9153
slug: chermak-delgado-equality-clause
title: "CLAIM: Isaacs Lem 1.43 の等号条件節 (J = HK かつ C_G(D) = C_G(H)C_G(K)) を standalone 化"
created: 2026-07-19
owner: lane a (Isaacs 全域)
---

# CLAIM: Isaacs Lem 1.43 の等号条件節を standalone 化

対象ファイル = `OddOrder/GroupTheory/ChermakDelgado.lean` (**shared infra、所有なし**)
ゆえに 9000 番台で claim する。

## 背景

2026-07-19 の Isaacs 全章監査 (Ch.6/8/10 の subagent 監査 + Ch.2/5/9 の実測) で、
**Isaacs 全体で唯一の未クローズ flag** が Lem 1.43 の等号条件節であることが確定した。
他章の「未形式化」記録はギャップ調査 note の stale であり、実体は全て存在していた。

**書籍 (p. 41、pdftotext で確認)**:
> **1.43. Lemma.** Let `H` and `K` be subgroups of a finite group `G`, and write
> `D = H ∩ K` and `J = ⟨H, K⟩`. Then `m_G(H) m_G(K) ≤ m_G(D) m_G(J)`
> **and if equality holds, then `J = HK` and `C_G(D) = C_G(H) C_G(K)`.**

**repo の現状**:
- 主不等式 = `chermakDelgadoMeasure_mul_le` (ChermakDelgado.lean:101) — 完成。
- 等号節は **standalone な statement が無い**。`chermakDelgadoLattice_sup_eq_mul`
  (同:223、Thm 1.44(b)) の中に、**lattice 所属仮定つき**でインラインに埋まっている。
- しかも `C_G(D) = C_G(H) C_G(K)` の節は**一度も述べられていない** — 証明内の
  `_eq_of_mul_eq_of_le` は `.1` と `.2` の両方を返すのに、`.2` (= `|C_H C_K| = |C_D|`)
  が捨てられている。

## やること

- [x] `chermakDelgadoMeasure_mul_eq_conditions` を新設: 仮説を
      `m_G(H)·m_G(K) = m_G(H⊓K)·m_G(H⊔K)` のみとし、結論を
      `↑(H⊔K) = ↑H * ↑K ∧ ↑C_G(H⊓K) = ↑C_G(H) * ↑C_G(K)` (いずれも集合等式) とする。
- [x] `chermakDelgadoLattice_sup_eq_mul` (Thm 1.44(b)) を、measure 等式を出してから
      新定理の `.1` を cite する形に書き換える (証明の重複を解消)。
- [x] AxiomsCheck に登録。

## 完了条件

書籍 Lem 1.43 の 2 つの結論が、lattice 仮定なしの standalone な定理として
sorry-free で存在し、`chermakDelgadoLattice_sup_eq_mul` がそれを cite している。

## 参照

- `OddOrder/GroupTheory/ChermakDelgado.lean:101` (主不等式) / `:223` (現在の埋め込み先)
- 私的補助 `_eq_of_mul_eq_of_le` (同:162) が既に両方の等号を返す
- ギャップ調査 note `notes/meta/three_books_full_survey_2026_07_16.md` の Isaacs Ch.1 節

## 完了 (2026-07-19)

`chermakDelgadoMeasure_mul_eq_conditions` (lattice 仮定なし、結論は 2 節の連言) を新設。
証明は書籍どおり「主不等式の緩みは `|HK| ≤ |J|` と `|C_H·C_K| ≤ |C_D|` の 2 箇所だけ
なので等号成立時は両方が等号」+ 有限集合の包含&濃度一致。

副次的な整理:
* `chermakDelgadoLattice_measure_mul_eq` — 「`H,K ∈ L` なら 1.43 は等号」を切り出し。
  Thm 1.44 (a)(b) が共通で使う入口になった。
* `_lattice_measure_inf_and_sup_eq` (private) — Thm 1.44(a) の 2 定理が重複して持っていた
  ~10 行の導出を 1 箇所に。`chermakDelgadoLattice_{inf,sup}_mem` は 3 行に縮小。
* `chermakDelgadoLattice_sup_eq_mul` (Thm 1.44(b)) は新定理の `.1` を cite する 4 行に
  (従来の ~85 行の独自証明を削除)。
* `chermakDelgadoLattice_centralizer_inf_eq_mul` — 等号条件のもう一方の節を lattice 版でも
  公開 (書籍 Thm 1.44 本文には無いが 1.43 が保証する内容)。

全て sorry-free / axiom-clean (AxiomsCheck 登録済)。ファイルは 597 → 614 行。

**これで Isaacs (Ch.1-Ch.10 + 付録) の未クローズ flag は解消**。
