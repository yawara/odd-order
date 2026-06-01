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

## 2026-05-30 — (7.8.a)/(7.8.b)/(7.9) statement spec + blocker analysis (issue 0044)

調査タスク: 「(7.8.a)/(7.8.b)/(7.9) を **sorry-free + faithful** に Lean 化する、不可能なら spec + plan を記録」。
結論: **3 件とも現状 sorry-free では実装不能** (下記 blocker)。Lean には一切手を入れていない (revert 不要)。
本節に精密ステートメント (repo の実型に合わせて検証済) と各々の証明計画・blocker を記録する。

2026-06-02 update: proof は依然 blocker 待ちだが、`Hypothesis78` に仮定を足さない
standalone target として `Hypothesis78.BetaDecomp`, `Hypothesis78.NormEstimates`,
`Hypothesis79.conclusion` を Lean 側に追加済み。

### 重要な前提: §9 の証明書 (certificate) パターン

`S09_NonexistenceCertain.lean` の §9 は **「難所の pointwise 恒等式を構造体フィールドに hoist し、系のみ証明する」** 方式で書かれている (memory `scaffold-sorry-free-not-done` 参照):

- (7.7.a) = `Hypothesis76.chiRho_decomp` フィールド
- (7.8.c.i) = `Hypothesis78.chiRho_eq_inner_beta` フィールド
- (7.7.b) `chiRho_norm_sq_double_sum` / (7.8.c.ii) `chiRho_norm_sq_eq_card_ratio_mul` のみ **outright proof**

タスクの絶対ルールは「real mathematical content を hypothesis に hoist するな」。したがって
(7.8.a/b)/(7.9) を **新たな証明書フィールドとして追加するのは不可** (= 偽の進捗、かつ既存の green proof が依存する
`Hypothesis78` を肥大化させ回帰リスク)。**outright に証明できる場合のみ Lean に書く** べきだが、下記の通りどれも不能。

### (7.8.a) — β 分解 (整数係数 a + 残余 Γ)

教科書 (mmd L63-71): `S^ν ⊥ 1_G`、かつ整数 `a` と `Γ ⊥ S^ν ∪ {1_G}` が存在し
`β = 1_G − ζ^ν + a·Σ_{φ∈S} (φ(1)/(e‖φ‖²))·φ^ν + Γ`。係数決定式 `a_φ‖φ‖² − (φ(1)/e)(a_ζ−1) = φ(1)/e`
から全 `a_φ = a·φ(1)/(e‖φ‖²)`、`(β,ζ^ν) = a−1 ∈ ℤ`。

精密ステートメント (repo 型検証済; `S = T \ {Ind 1_H}` を `i ≠ ind1H` で表現):

```lean
namespace Hypothesis78
variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype L]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- **Peterfalvi (7.8.a)** 証明書 (構造体). `S^ν ⊥ 1_G`、整数 `a`・残余 `Γ` の存在 +
分解恒等式。`e = ζ_{ind1H}(1)`. -/
structure BetaDecomp (H78 : Hypothesis78 G A L) where
  a : ℤ
  Gamma : ClassFunction G ℂ
  /-- `S^ν ⊥ 1_G`: 各 `ν(ζ_i)` (i ≠ ind1H) は `1_G` に直交. -/
  nu_orth_one : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
    ClassFunction.inner (H78.nu (H78.hyp76.zeta i))
      (OddOrder.RepresentationTheory.trivialClassFunction G) = 0
  Gamma_orth_nu : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
    ClassFunction.inner Gamma (H78.nu (H78.hyp76.zeta i)) = 0
  Gamma_orth_one : ClassFunction.inner Gamma
    (OddOrder.RepresentationTheory.trivialClassFunction G) = 0
  beta_eq : H78.beta =
    OddOrder.RepresentationTheory.trivialClassFunction G
    - H78.nu (H78.hyp76.zeta H78.zetaDistinct)
    + ((a : ℂ) • ∑ i ∈ Finset.univ.filter (· ≠ H78.ind1H),
        (H78.hyp76.zeta i (1 : L) /
          (H78.hyp76.zeta H78.ind1H (1 : L) *
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)))
          • H78.nu (H78.hyp76.zeta i))
    + Gamma

theorem exists_betaDecomp (H78 : Hypothesis78 G A L) : Nonempty H78.BetaDecomp
```

**Blocker (7.8.a)**: 証明には (i) `β ∈ ZIrr G` (Dade 等距 `IsDadeIsometry` を `Ind 1_H − ζ ∈ ℤ[CF(L,A)]`
に適用)、(ii) 正規直交集合 `{1_G} ∪ {φ^ν/‖φ‖}` への **整数係数直交射影**で `a ∈ ℤ`・`Γ` を抽出、が必要。
(ii) は `ZIrr` 上の射影理論であり repo 未組立。さらに **`H78.nu` が `ZIrr(L) → ZIrr(G)` を保つ**事実
(整数性に必須) が `Hypothesis78` のフィールドに無い (`nu_isometry` のみ)。`S^ν ⊥ 1_G` 自体は
`nu_isometry` + `(2.7)` adjoint + `trivialClassFunction_isIrreducible` から導ける見込みだが、分解本体が射影理論待ち。

### (7.8.b) — ノルム評価 `‖ζ^{νρ}‖² ≥ 1−e/h`, `‖Γ‖² ≤ e−1`

教科書 (mmd L73-101): `e ≤ (h−1)/2` (= `2e+1 ≤ h`) の下で `‖ζ^{νρ}‖² = ua²−2va+w`
(`u=(1/e)(1−1/h)`, `v=1/h`, `w=1−e/h`、(7.7.b) を `ζ_0∈S∖{ζ}, ζ_1=Ind1_H, ζ_2=ζ, χ=ζ^ν` で適用)。
`2hv=2 ≤ (h−1)/e=hu ⇒ 0≤2v/u≤1 ⇒ ua²−2va≥0` (a∈ℤ) で下界 `w`。
`‖Γ‖² = e−1−h(ua²−2va) ≤ e−1` は `‖β‖²=e+1` と (1.5.d) `Σ_{θ≠1}θ(1)²=h−1` から。

精密ステートメント (実数化は `Complex.re`; `e,h` は `ℝ` cast):

```lean
/-- **Peterfalvi (7.8.b)** 下界. -/
theorem zetaNu_chiRho_norm_sq_ge (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (h_e_le : 2 * Nat.card H78.hyp76.H ≤ ... ) :  -- 2e+1 ≤ h を H/L の card で
    1 - (Nat.card H78.hyp76.H : ℝ)⁻¹ * ... ≤
      (ClassFunction.inner
        (H78.hyp76.hyp71.chiRhoCF (H78.nu (H78.hyp76.zeta H78.zetaDistinct)))
        (H78.hyp76.hyp71.chiRhoCF (H78.nu (H78.hyp76.zeta H78.zetaDistinct)))).re

/-- **Peterfalvi (7.8.b)** 上界 `‖Γ‖² ≤ e−1`. -/
theorem Gamma_norm_sq_le (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (h_e_le : ...) :
    (ClassFunction.inner hBD.Gamma hBD.Gamma).re ≤ (Nat.card ... : ℝ) - 1
```

注: prior pass の `(β,χ)²` は誤り。repo の (7.8.c.ii) は `inner β χ * star (inner β χ)` 形。
また `e = ζ_{ind1H}(1:L)` は `ℂ` 値なので `e ≤ (h−1)/2` は `Nat.card` ベース (`[L:H]=e`) で書くのが安全
(`.re.toNat` は避ける)。`(ν ζ)^ρ` のノルムは `chiRhoCF` over `L` 上の `ClassFunction.inner`。
Lean 実装では `kernelOrder`, `complementIndex`, `smallIndex`, `zetaNuRho`,
`zetaNuRhoNormSq`, `gammaNormSq`, `NormEstimates` としてこの target を名前付け済み。
また `quadraticTerm_nonneg_of_smallIndex` で、`a∈ℤ`, `2e+1≤h` から
`0 ≤ (1/e)(1-1/h)a² - 2(1/h)a` を出す純算術部分は sorry-free 化済み。
`beta_inner_self_eq_sourceDiff_inner_self` / `betaNormSq_eq_sourceDiffNormSq` により、
`‖β‖²` を Dade isometry で source 側 `‖Ind 1_H - ζ‖²` に移す bridge も済み。
さらに `sourceDiff_inner_self_expand` / `sourceDiffNormSq_expand` で source norm を
4 つの inner product に展開済み。`SourceDiffNormEvaluation` は残る source-side 評価
`sourceDiffNormSq = e+1` を standalone target として固定し、
`betaNormSq_eq_complementIndex_add_one` はそれを `‖β‖²=e+1` に戻す bridge。
`sourceDiffNormEvaluation_of_inner_values` /
`betaNormSq_eq_complementIndex_add_one_of_inner_values` により、残る source-side 評価は
`⟨Ind1H,Ind1H⟩=e`, `⟨ζ,Ind1H⟩=0`, `⟨Ind1H,ζ⟩=0`, `⟨ζ,ζ⟩=1` の 4 事実に局所化。
2026-06-02 追記: `zetaDistinct_inner_self_eq_one_of_irreducible` と
`*_of_zeta_irreducible` bridge を追加し、最後の `⟨ζ,ζ⟩=1` は
`IsIrreducibleCharacter ζ` から `irreducibleCharacter_inner_eq_ite` で即座に出せる形へ縮小。
さらに `sourceDiffNormEvaluation_of_zeta_ind_orthogonal` 系で
Hermitian symmetry から `⟨Ind1H,ζ⟩=0` を自動生成し、source-side 入力は
`⟨Ind1H,Ind1H⟩=e`, `⟨ζ,Ind1H⟩=0`, `IsIrreducibleCharacter ζ` に縮小。

**Blocker (7.8.b)**: (1) `‖β‖²=e+1` — `IsDadeIsometry.inner_eq` で source norm へ移す部分と、
4 source inner-product 評価から beta norm identity へ戻す部分は解消済み。
残りは `L` 上での source-side inner product 評価で、self term は
`IsIrreducibleCharacter ζ` へ、反対向き直交は Hermitian symmetry へ縮小済み
(`chiRho_norm_sq_double_sum` の素材だが shape 不一致)。(2) **(1.5.d)**
`Σ_{θ∈Irr H, θ≠1}θ(1)²=h−1` (Burnside/第二直交関係) が repo に named lemma として無い (issue 0048 は
`|Irr|=|ConjClasses|` で別物・未完)。(3) (7.7.b) を `ζ_1=Ind1_H` 配置で適用するには `c_1=a, c_2=1, c_{i>2}=0`
の計算が必要で、これは (7.8.a) の `BetaDecomp` (係数 `a`) に依存する。よって (7.8.a) が先。算術 `ua²−2va≥0`
自体は `quadraticTerm_nonneg_of_smallIndex` として解消済みだが、`u,v,w`・`‖β‖²` を構造から導く層が未組立。

### (7.9) — 2 族の非直交性

教科書 (mmd L107-113): `β_i=1_G−ζ_i^{ν_i}+Δ_i`。(5.9) で `Δ_i` 実、(7.8.a) で `(Δ_i,1_G)=0`、
(1.1)+`G` 奇位数で `(Δ_1,Δ_2)=Σ_χ(Δ_1,χ)(Δ_2,χ)` 偶、`A_1^{τ_1}∩A_2^{τ_2}=∅` で `(β_1,β_2)=0`、
(4.1) で `(ζ_1^{ν_1},ζ_2^{ν_2})=0`。展開
`0=(β_1,β_2)=1−(ζ_1^{ν_1},Δ_2)−(ζ_2^{ν_2},Δ_1)+(Δ_1,Δ_2)` ⇒ 和 ≡1 (mod 2) ⇒ 少なくとも一方≠0。

精密ステートメント (2 つの `Hypothesis78` + dadeSupport 互いに素):

```lean
theorem non_orthogonality_two_families
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hodd : Odd (Nat.card G))
    {A₁ A₂ : Set G} {L₁ L₂ : Subgroup G} [Fintype L₁] [Fintype L₂]
    [Invertible (Nat.card L₁ : ℂ)] [Invertible (Nat.card L₂ : ℂ)]
    (H78₁ : Hypothesis78 G A₁ L₁) (H78₂ : Hypothesis78 G A₂ L₂)
    (hBD₁ : H78₁.BetaDecomp) (hBD₂ : H78₂.BetaDecomp)
    (hDisjoint : Disjoint H78₁.hyp76.hyp71.hyp.dadeSupport
                          H78₂.hyp76.hyp71.hyp.dadeSupport) :
    ClassFunction.inner H78₁.beta (H78₂.nu (H78₂.hyp76.zeta H78₂.zetaDistinct)) ≠ 0 ∨
    ClassFunction.inner H78₂.beta (H78₁.nu (H78₁.hyp76.zeta H78₁.zetaDistinct)) ≠ 0
```

**Blocker (7.9)** (最重・多数):
1. ✅ **解消 (2026-05-30, issue 0044)**: **奇位数 ⇒ 非自明既約は実でない** — (1.1) parity の核を
   `BrauerPermutationUnconditional.lean` に `not_isReal_of_ne_trivial_of_odd_card'`
   (`Odd (Nat.card G) → χ ≠ 1 → ¬ IsReal (χ:CF G ℂ)`, unconditional) として sorry-free 実装。
   旧記述では「`IsReal.lean` は基盤のみで定理が存在しない」としていたが, 実際には Brauer permutation の
   **unconditional 系** `card_realIrreducibleCharacters_eq_one_of_odd_card'`
   (`# real Irr = 1`) が既に完成しており, そこから subsingleton 一意性
   (`Nat.card_eq_one_iff_exists`) で導出した (note の `g↦g²` Frobenius-Schur 構成より軽い経路で完了)。
   IsReal.lean は BrauerPermutation の上流のため, 定理は下流の Unconditional 側に置いた
   (循環 import 回避)。`(Δ_1,Δ_2)` parity の核はこれで unblock。 [旧記述↓は参考保持]
   `IsReal.lean` は `IsReal`/`conj` 基盤と
   `trivialClassFunction_isReal` のみで、**`Odd (Nat.card G) → χ≠1 → ¬IsReal χ` の定理は repo に存在しない**
   (grep 確認済)。これ無しに `(Δ_1,Δ_2)` 偶が言えない。
2. **(5.9) realness 接続** — `S07_Coherence.lean` の `CharacterDifferenceImage`
   (`τ(χ−χ.conj)=signedDifference`) を `H78.nu` 経由で適用する橋が無い (`H78.nu` ↔ `IsCoherent.extension`
   未接続 = Blocker B1)。これで `Δ_i` 実 (`Δ_i=Δ̄_i`) を得る。
3. ✅ **互いに素 support ⇒ inner=0 — 完了 (2026-05-30, issue 0044)**: `ClassFunction.lean` に
   `inner_eq_zero_of_disjoint_support` (`Disjoint φ.support ψ.support → inner φ ψ = 0`) + 補助
   `innerSum_eq_zero_of_disjoint_support` を sorry-free 実装。各 summand `φ g · star (ψ g)` が
   `Set.disjoint_left` で消える elementary proof。AxiomsCheck clean, full build green。
4. **(4.1) `nu` 像の support** — `(ν ζ_i).support ⊆ dadeSupport_i` が `Hypothesis78` のフィールドに無い。
5. **(7.8.a) 依存** — `BetaDecomp` (`Δ_i` の存在、`(Δ_i,1_G)=0`) が前提。

### 優先順位と次の一手 (plan)

1. ✅ **基盤 B3 (奇位数⇒非実) — 完了 (2026-05-30, issue 0044)**:
   `BrauerPermutationUnconditional.lean` に `not_isReal_of_ne_trivial_of_odd_card'`
   (`Odd (Nat.card G) → χ ≠ 1 → ¬ IsReal (χ:CF G ℂ)`) + 補助
   `realIrreducibleCharacter_eq_trivial_of_odd_card'` を sorry-free 実装。当初想定の
   `g↦g²` Frobenius-Schur 経路は不要だった: Brauer permutation lemma の unconditional 系
   `card_realIrreducibleCharacters_eq_one_of_odd_card'` から subsingleton 一意性で導出。
   (7.9) のみならず §3 (1.1) / 0022/0027 系の共通 unblocker が解消。AxiomsCheck clean。
2. ✅ **B-disjoint-support — 完了 (2026-05-30, issue 0044)**: `ClassFunction.inner_eq_zero_of_disjoint_support`
   を `inner_eq_inv_card_mul_innerSum` + `innerSum_eq_zero_of_disjoint_support` (各 summand を
   `Set.disjoint_left` で消す) から sorry-free 実装。
3. ✅ **Burnside (1.5.d) — 完了 (2026-05-30, issue 0044)**: `Σ_{θ∈Irr H, θ≠1}θ(1)²=|H|−1` を
   `ColumnOrthogonality.lean` に named lemma 化。`column_orthogonality_diagonal (1:G)` を `g=1` で評価し
   (`Subgroup.centralizer {1} = ⊤` ⇒ `card = |G|`), 各 `χ(1)·star(χ(1))` を
   `irreducibleCharacter_apply_one_eq_pos_natCast` + `star_natCast` で `χ(1)²` に置換。
   `sumIrreducibleDegreeSq` (`Σ χ(1)²=|G|`) + `sumNontrivialIrreducibleDegreeSq`
   (`Σ_{χ≠1} χ(1)²=|G|−1`, `Finset.add_sum_erase` で trivial 寄与 `1²` を分離) の 2 本。AxiomsCheck clean。
4. **B1 (nu ↔ coherence)**: `Hypothesis78` に 3 フィールド追加を検討 — `nu_maps_ZIrr`, `nu_conj`
   (共役保存), `nu_supp` (像の support ⊆ dadeSupport)。**ただしこれは証明書追加であり、追加するなら
   それらが `IsCoherent.extension` から構成可能であることを別途示す責務が伴う** (memory
   `scaffold-sorry-free-not-done`: 「hypothesis が構成可能か」で done を判定)。
5. 上記 1-4 が揃った後、(7.8.a) 射影 → (7.8.b) 算術 → (7.9) parity の順で outright 証明可能になる見込み。

### 2026-06-02 — (7.10) final assembly target

`FrobeniusFamily.CharacterEstimateData` を追加し、最終 `card_G0_lower_bound` の残りを
「minimal index + `𝓑`-set + unweighted `𝓑`-sum bound + base estimate」の data 構成に局所化。
`lowerBoundTerm_of_characterEstimateData` はその data から表示下界を sorry-free で返す。
したがって算術 bridge は閉じており、残る `sorry` は (7.5)(7.8)(7.9)(6.8)+Thompson から
`CharacterEstimateData` を作る指標論・coherence 側。

**現時点の判定**: plan 1/2/3 (奇位数⇒非実 / disjoint-support inner=0 / Burnside (1.5.d)) はすべて完了。
残る律速は plan 4 (B1: nu ↔ coherence、証明書追加に構成責務が伴う) で、これが未組立のため
(7.8.a/b)/(7.9) のいずれも outright sorry-free 化は依然不能。
証明書フィールド方式での「sorry-free」化はルール上の偽進捗 + 回帰リスクのため見送り。本 spec を実装の青写真とする。

---

*訂正版 作成: 2026-05-27 (原典 `04.9` 162 行 精読 + scaffold 実装に基づく). 旧版 2026-05-22 は App.C 混同のため破棄.*
*(7.8.a/b)/(7.9) spec + blocker 追記: 2026-05-30 (issue 0044, mmd L63-113 精読 + repo 型検証).*
*Burnside (1.5.d) `sumIrreducibleDegreeSq` / `sumNontrivialIrreducibleDegreeSq` 実装完了: 2026-05-30 (issue 0044, `ColumnOrthogonality.lean`).*
