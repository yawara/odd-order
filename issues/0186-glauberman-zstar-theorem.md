---
id: 186
slug: glauberman-zstar-theorem
title: "Glauberman Z*-定理 (Navarro (7.7)–(7.9))"
created: 2026-08-20
---

# Glauberman の `Z*`-定理 (Navarro Ch.7 の残り)

**ユーザー裁定 2026-08-20**: 3 冊の宣言スコープ完了後の次の対象として選択。

## 位置づけ

Navarro Ch.7 は **Brauer–Suzuki → `Z*`-定理**の順に進む。BS 側 (pp.139–146) は
issue 0147 / 9506 で完成し、そのとき **`Z*` 用の (7.7)–(7.9) は明示的にスコープ外**にした
(`AxiomsCheck.lean:20307`「p.145 後半の (7.7) と p.146 は Z\*-定理用で、issue 0147 のスコープ外」)。
本 issue はそこを埋める。

- `Z*(G)` は repo に**不在** (2026-08-20 grep)。
- 土台の modular 表現論は **150 leaf 既存** (`GroupTheory/RepresentationTheory/Modular/`)。
- 原文 = `references/navarro/pages/navarro-p145..149.png` (書籍 pp.145–149、PDF ページ = 書籍 + 10)。
  ⚠ Navarro の数式は OCR 崩れが重いので **statement はページ画像で確定**する。

## 教科書の statement (p.146 画像で確定)

**定義**: `Z*(G)/O_{2'}(G) = Z(G/O_{2'}(G))`。
⟹ repo では `QuotientGroup.mk' (oPiCore {p | p ≠ 2} G) u ∈ Subgroup.center (G ⧸ oPiCore …)`
と書く (既存の `brauerSuzuki_mk_mem_center` と同じ形)。

**(7.8) LEMMA**. `P ∈ Syl₂(G)`, `u ∈ P` 対合。次は同値:
(a) `u, u^g ∈ P` なる `g ∈ G` について常に `u = u^g`;
(b) 任意の `g ∈ G` で `[u, g]` の位数が奇。

**(7.9) Z\*-THEOREM (Glauberman)**. `u` を `P ∈ Syl₂(G)` の対合とし、
`u, u^g ∈ P` なる `g` について常に `u = u^g` とする。このとき `u ∈ Z*(G)`。

**(7.7) THEOREM**. `u ∈ G` が `p`-元、`v ∈ O_{p'}(C_G(u))`、`B₀` を `G` の主ブロックとする。
`χ ∈ Irr(B₀)` なら `χ(uv) = χ(u)`。

## 既存資産の実測 (2026-08-20)

(7.7) が引く feeder は**全て repo にある**:

| Navarro | repo |
|---|---|
| Cor (5.8) 第二主定理 | `Modular/SecondMainBlockOfIrr`, `SecondMainBlockForm` |
| 第三主定理 (逆向き) | `Modular/KulshammerThirdMain`, `SecondMainPrincipalBlock.eq_principalBlock_of_inducedBlockOfCentralizer_eq` |
| Thm (6.10) `O_{p'}(C) = ker(b₀)` | `Modular/BlockKernel`, `PrincipalBlockKernel` |
| Lemma (6.11) / Cor (6.12) | `Modular/BrauerCharacterKernel`, `BlockKernel` |
| Cor (5.11) ブロック直交 | `Modular/PrincipalBlockInvolution`, `BlockPartVanishing` |
| Brauer–Suzuki | `GroupTheory.brauerSuzuki_mk_mem_center` (issue 0184 で一般形化済) |

⚠ ただし `Modular/SecondMainPrincipalBlock.character_mul_eq_generalizedDecompositionNumber` は
**`C_G(x)` が正規 `p`-補群を持つ場合への特殊化** (BS が要ったのはその形)。(7.7) は
その仮説を落とした一般形が要る (和が単項に潰れず `IBr(b₀)` 上の和のまま)。
= CLAUDE.md「特殊化債務はできる限り一般化する」に該当。

## やること (上流優先 + 文書順)

- [x] **(7.7)** ✅ (commit `07a9b5869` + `a5c9cea9c`) — `Modular/PrincipalBlockPPrimeCore.lean`。
      特殊化を外した一般展開
      `χ(u w) = ∑_{μ ∈ IBr(b₀)} d^u_{χ μ} μ(w)` (`w ∈ C_G(u)⁰`) を出し、
      `O_{p'}(C_G(u)) = ker(b₀)` (6.10) と `μ(v) = μ(1)` (6.11)(6.12) を当てて
      `w = v` と `w = 1` の比較で `χ(uv) = χ(u)`。
      **repo 版は書籍より一般**: 使うのは「正規かつ位数が `p` と素」だけなので、
      `O_{p'}` でなく任意の正規 `p'`-部分群で述べた
      (`character_mul_eq_character_of_mem_normal_of_not_dvd`)
- [x] **(7.8)** ✅ (commit で `GroupTheory/IsolatedInvolution.lean`) —
      `forall_conj_eq_iff_forall_odd_orderOf_commutator`。
      ⚠ **二面体の構造論を使わない証明に置き換えた**: `w = u·u^g` の位数が偶なら
      `|w| = 2^a·m` (`m` 奇)、`c = w^m`、`k = (m+1)/2` として `w^k v (w^k)⁻¹ = c·u`。
      `u` と `G`-共役 `c·u` が 2-群 `⟨c⟩ ⊔ ⟨u⟩` に同居 ⟹ `c = 1` で `|c| = 2^a > 1` に矛盾。
      副産物 `conj_eq_of_mem_pGroup` (= 教科書 Step 5) は (7.9) でもそのまま使う
- [ ] **(7.9)** — `|G|` 帰納法 + 9 step + 最終矛盾。step の骨子は原文どおり:
      1 (`N ⊴ G`, `u ∉ N` ⟹ `uN ∈ Z*(G/N)`; ⟹ `O_{2'}(G) = 1` と仮定してよい) /
      2 (`u ∈ H < G` ⟹ `u ∈ Z*(H)`) / 3 (`u` は真の正規部分群に入らない) /
      4 (`Z(G) = 1`) / 5 (`u` を含む任意の 2-部分群の中心に `u` がある) /
      6–7 (`v^g u` の 2-部分 `z` と `2'`-部分 `x` の解析、`z` と `vu` が共役) /
      8 (`χ(v^g u h) = χ(vu)`、(7.7) を使う) / 9 (`a(u)a(v) = a(uv)` と `a(u)² = 1`) /
      最終矛盾 (ブロック直交 (5.11) を 2 回)
- [ ] `AxiomsCheck` 登録 + `OddOrder.lean` 配線 + `CLAUDE.md`/`ROADMAP.md` の scope 記述更新

## 完了条件

`u ∈ Z*(G)` の Lean statement が sorry-free・標準 3 公理のみで、`AxiomsCheck` 登録済。

## 参照

- 原文ページ画像: `references/navarro/pages/navarro-p145.png` … `navarro-p149.png`
- BS 側: [0147](closed/0147-q8-modular-char-theory-frozen.md) / [9506](closed/9506-modular-p-modular-system.md) / [0184](closed/0184-brauer-suzuki-eval-submit.md)
- project spec: `notes/meta/q8_modular_char_theory_frozen_project.md`
