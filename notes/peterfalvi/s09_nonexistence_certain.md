# Peterfalvi §9: Non-existence of a Certain Type of Group of Odd Order — mini-roadmap

**スコープ**: Peterfalvi §9 (pp. 38-43), mmd `04.9_pp_38_43_Non-existence_of_a_Certain_Type_of_Group_of_Odd_Order.mmd` (162 行).
形式化先: [`OddOrder/Peterfalvi/S09_NonexistenceCertain.lean`](../../OddOrder/Peterfalvi/S09_NonexistenceCertain.lean) (作成済 — statement scaffold).
ROADMAP 上の位置: **Phase 2b 第 4 波** (§3-§8 完成後着手).

> ⚠️ **2026-05-27 訂正**: 本ノートの旧版 (2026-05-22 作成, §3-§8 audit より前) は **§9 を BG App.C の有限体内容と取り違えていた**。原典 `04.9` を精読した結果, **§9 は純粋に指標論的** ((7.1)-(7.11)) であり, 旧版にあった「有限体 $F_{p^q}$ / Frobenius 群 $H=PU$ / norm 関数 / 条件 (A) / Hypothesis (B) / 結論 $p\le q$ / 集合 $E$ / Lemma C.1-C.3」は §9 に **一切登場しない**。それらは BG App.C (= Peterfalvi 1984 paper の Carlip-Wheeler 編集再録) 側の別定式化。両者は FT 最終矛盾を閉じる点で対応するが, **ステートメントとしては等価ではない** (旧版「論理的に同一内容」は overstate)。以下は訂正版。

---

## TL;DR — (7.11): Frobenius 族による非存在定理 (純指標論)

**§9 の主定理は (7.11)**:

> 奇数位数の有限群 $G$ が, $k \geq 2$ 個の Frobenius 部分群 $L_i$ (kernel $H_i$, $H_i^\#$ が正規化群 $L_i$ を持つ TI-subset, 位数 $h_i = |H_i|$ は pairwise coprime) を持ち, それらの共役の広がりが単位元以外を覆い尽くす — すなわち $G_0 = G - \bigcup_i (H_i^\#)^G = \{1\}$ — ことは **ありえない**。

証明は **(7.10) の数値不等式の (ほぼ自明な) 系**:

$$\frac{|G_0|-1}{|G|} \geq (e-1)\Big(\frac{h-2e-1}{eh} + \frac{2}{h(h+2)}\Big) \quad (\text{ある } i, \ e=e_i, h=h_i).$$

$G_0 = \{1\}$ なら左辺 $= 0$ だが, Frobenius complement 非自明 ($e \geq 2$) + $e \mid h-1$ + $|L|$ 奇 ($\Rightarrow e \leq (h-1)/2$, つまり $2e+1 \leq h$) から右辺 $> 0$ で矛盾。

**(7.10) 自体** は Dade isometry (§4) + Coherence (§7-§8) を用いた重い指標計算 ((7.1)-(7.9)) に依存する。

---

## §9 全 11 結果 (7.1)-(7.11)

| # | 行範囲 | 種別 | ステートメント要約 | 役割 |
|---|--------|------|-------------------|------|
| (7.1) | L3-7 | **Hypothesis** | (2.2) 仮説下で Dade isometry $\tau$, および $\chi^\rho(a)=\frac{1}{|H(a)|}\sum_{x\in H(a)}\chi(ax)$ で $\rho:{\rm CF}(G)\to{\rm CF}(L,A)$ を定義. $A^\tau=\bigcup_{a\in A}(aH(a))^G$. | 基本設定 |
| (7.2) | L9-19 | **Lemma** | (a) $\alpha\in{\rm CF}(L,A)\Rightarrow\alpha^{\tau\rho}=\alpha$. (b) $\|\chi^\rho\|^2\le\|\chi\|^2$, 等号 ⟺ $\chi\in{\rm im}\,\tau$. | $\rho$-$\tau$ 複合 |
| (7.3) | L20-35 | **Lemma** | $\frac{1}{|G|}\sum_{g\in A^\tau}\|\chi(g)\|^2\ge\|\chi^\rho\|^2$, 等号 ⟺ $\chi$ が $aH(a)$ 上定数. | 積分不等式 |
| (7.4) | L36 | **Hypothesis** | 部分群族 $(L_i)_{i\in I}$, 各々 (7.1), $A_i^{\tau_i}$ pairwise disjoint, $G_0=G-\bigcup A_i^{\tau_i}$. | 複数族の設定 |
| (7.5) | L38-51 | **Theorem** | $\frac{1}{|G|}(\sum_{G_0}\|\chi\|^2-|G_0|)+\sum_i(\|\chi^{\rho_i}\|^2-\frac{|A_i|}{|L_i|})\le 0$. | 主不等式 |
| (7.6) | L52- | **Hypothesis** | normal $H\triangleleft L$, $A=H^\#$, $|H|=h$, $|L:H|=e$, $\mathcal{T}=\{{\rm Ind}_H^L\theta\}$. | Coherence 応用設定 |
| (7.7) | L54-62 | **Lemma** | $\chi^\rho$ の explicit formula + $\|\chi^\rho\|^2$ の二重和表示. | 明示計算 |
| (7.8) | L63-106 | **Lemma** | $\mathcal{S}$ coherent, $\nu$ 拡張. $e\le\frac{h-1}{2}\Rightarrow\|\zeta^{\nu\rho}\|^2\ge1-\frac{e}{h}$, $\|\Gamma\|^2\le e-1$. | norm 評価 |
| (7.9) | L107-113 | **Key Lemma** | $I=\{1,2\}$, $G$ **奇数位数**, coherent ⟹ $(\beta_1,\zeta_2^{\nu_2})\ne0$ または $(\beta_2,\zeta_1^{\nu_1})\ne0$. | 2 族の非直交性 |
| (7.10) | L115-155 | **Theorem** | $k\ge2$ Frobenius $L_i$ (kernel $H_i$, $H_i^\#$ TI, $\gcd(h_i,h_j)=1$) ⟹ ある $i$ で $\frac{|G_0|-1}{|G|}\ge(e-1)(\frac{h-2e-1}{eh}+\frac{2}{h(h+2)})$. | 構造定理 (数値下界) |
| (7.11) | L157-163 | **THEOREM** | **(7.10) の仮説を満たし $G_0=\{1\}$ となる群は存在しない**. | **§9 主定理 = FT クローザー** |

証明での内部依存 (mmd 実測): (7.2)←(2.7),(2.6); (7.3)←(7.2); (7.5)←(7.3); (7.7)←(7.6); (7.8)←(7.7),(1.5),(2.7); (7.9)←(7.8),(5.9),(1.1),(4.1); (7.10)←(7.5),(7.8),(7.9),(6.8) + Thompson (kernel nilpotent); (7.11)←(7.10).

---

## BG App.C との関係 (別定式化, 非等価)

- **BG App.C** (mmd L4759-5005, = Peterfalvi 1984 paper [22] の Carlip-Wheeler 編集版) は **同じ FT 最終矛盾を有限体的に** 証明する: $F_{p^q}$ 上の Frobenius 群 $H=P\rtimes U$ (加法群 $P$, norm-1 群 $U$), Galois 理論 (Satz 90), 集合 $E=\{a: N(a)=N(2-a)=1\}$ を用い, **Theorem C: $p\le q$** を導く (Lemma C.1/C.2/C.3 経由)。詳細は [`notes/bg/appC_final_contradiction.md`](../bg/appC_final_contradiction.md) を参照 (App.C を直接扱うノート)。
- **これは (7.11) とは別の statement**。両者とも minimal simple group の最終矛盾を与えるが, (7.11) は character-theoretic な一般非存在, Theorem C は特定の有限体配置に対する数値結論 ($p\le q$) であって, **literally equivalent な定理ではない**。
- **形式化方針**: Peterfalvi §9 (7.11) を一次実装 (本ファイル)。BG App.C は (BG 側で実装するなら) 独自に書く。Phase 3 で「両者が同じ最終矛盾を閉じる」橋渡しを検討 (素朴な `≅` 同値補題は成立しない可能性が高い — 統合方法は要再設計)。
- ⚠️ **旧版にあった詳細な対応表** ((7.x) ↔ App.C Remark (I)-(XI) / Lemma C.1-C.3, 「等価な仮説体系」「同一の非存在定理」) は **未検証の推測**で, 信頼しないこと。App.C の正確な構造把握には App.C 側ノート + mmd 直読が必要。

---

## Lean 形式化 (実装済 scaffold)

[`S09_NonexistenceCertain.lean`](../../OddOrder/Peterfalvi/S09_NonexistenceCertain.lean) の構成:

```lean
namespace OddOrder.Peterfalvi.S09
open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)
open OddOrder.GroupTheory (IsTISubset)

/-- (7.10) 仮説 (a)-(c) + k≥2 を束ねる. -/
structure FrobeniusFamily (G : Type*) [Group G] (k : ℕ) where
  L : Fin k → Subgroup G
  H : Fin k → Subgroup G
  two_le : 2 ≤ k
  kernel_le : ∀ i, H i ≤ L i
  isFrobenius : ∀ i, ∃ C, IsFrobeniusGroup ↥(L i) ((H i).subgroupOf (L i)) C   -- (a)
  normalizer_eq : ∀ i, L i = Subgroup.normalizer (H i : Set G)                 -- (b) host
  isTI : ∀ i, IsTISubset ((H i : Set G) \ {1}) (L i)                           -- (b) TI
  coprime_kernel : ∀ ⦃i j⦄, i ≠ j → Nat.Coprime (Nat.card (H i)) (Nat.card (H j)) -- (c)

-- kernelSpread i = (H_i^#)^G ;  G0 = G - ⋃ kernelSpread ;  h i = |H_i| ;  e i = |L_i:H_i|
theorem card_G0_lower_bound (F) (hodd : Odd (Nat.card G)) :   -- (7.10), sorry
  ∃ i, (Nat.card F.G0 - 1)/|G| ≥ (e-1)((h-2e-1)/(eh) + 2/(h(h+2)))
theorem not_trivial_G0 (F) (hodd) (hG0 : F.G0 = {1}) : False  -- (7.11), 証明 = (7.10) の系
```

**設計上のポイント**: (7.10)/(7.11) の **ステートメントは純群論** (`IsFrobeniusGroup` + `IsTISubset` + 位数) で書け, 未完の Dade isometry sorry (`IsometryDifferencePair`) に **非依存**。依存するのは証明だけ。

---

## mathlib / repo インフラ

| 必要物 | 所在 | 状態 |
|--------|------|------|
| `IsFrobeniusGroup G N A` (kernel N, complement A) | `OddOrder.Isaacs.Ch06` (`Ch06_FrobeniusActions/FrobeniusGroup.lean`) | ✅ 既存 |
| `IsTISubset (A:Set G) (L:Subgroup G)`, `Subgroup.IsTI` | `OddOrder.GroupTheory.TISubset` | ✅ 既存 |
| `IsFrobeniusGroup.card_kernel_modEq_one` (\|H\|≡1 mod \|A\| ⇒ $e\mid h-1$) | 同上 | ✅ 既存 |
| `IsFrobeniusGroup.coprime_card_kernel_complement` | 同上 | ✅ 既存 |
| `IsFrobeniusGroup.ne_bot_complement` / `.isComplement` ($e=\|C\|\ge2$, $|L|=he$) | 同上 | ✅ 既存 |
| Dade isometry / Coherence (§4, §7-§8) — (7.10) 証明用 | `RepresentationTheory`, `S04`/`S07`/`S08` | 🔄 §4 に残 sorry 1 (`IsometryDifferencePair`) |
| `Subgroup.normalizer` — rc2 で `Set G → Subgroup G` (set 引数化) | mathlib v4.30.0-rc2 | ⚠️ 引数注意 |

---

## TODO / 着手順

1. **(7.11) の証明** (= (7.10) の系, **(7.10) と独立に着手可**): (7.10) を `sorry` のまま, 以下の純算術を Frobenius API から導いて矛盾を組む —
   - $G_0=\{1\}\Rightarrow|G_0|=1\Rightarrow$ 左辺 $=0$.
   - $e_i \geq 2$ (Frobenius complement 非自明; 奇位数なら実際 $e_i$ 奇 $\geq 3$).
   - $e_i \mid h_i - 1$ (`card_kernel_modEq_one`).
   - $|L_i|$ 奇 $\Rightarrow e_i$ 奇, $h_i-1$ 偶 $\Rightarrow (h_i-1)/e_i$ 偶 $\Rightarrow 2e_i \leq h_i-1$ (つまり $h_i-2e_i-1\geq0$).
   - 上記 $\Rightarrow$ 右辺 $>0$, 左辺 $=0$ と矛盾.
2. **(7.10) の証明**: (7.1)-(7.9) の指標計算 = **§4-§8 完成後** (特に Dade isometry の残 sorry 解消後)。(7.5) 主不等式 → (7.8) norm 評価 → (7.9) 2 族非直交 → (6.8) 直交族分解 + Thompson (kernel nilpotent) の合成。
3. **Phase 3**: BG App.C との橋渡し (両者が同じ最終矛盾を閉じることの定式化; 素朴 `≅` ではなく統合設計を要検討)。

---

*訂正版 作成: 2026-05-27 (原典 `04.9` 162 行 精読 + scaffold 実装に基づく). 旧版 2026-05-22 は App.C 混同のため破棄.*
