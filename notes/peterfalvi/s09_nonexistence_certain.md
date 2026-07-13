# Peterfalvi §9: Non-existence of a Certain Type of Group of Odd Order — mini-roadmap

> 🔔 **2026-07-01 cross-lane 通知 (issue 0091)**: `Hypothesis78.nu_isometry` フィールドが
> lane b により **global (`∀ φ ψ`) → family (`∀ i j, i≠ind1H → j≠ind1H`)** に弱められ、
> ユーザー裁定で合流済 (family 版が Peterfalvi 忠実版; global 拡張は次元不整合で一般に不存在)。
> 派生 `nu_zeta_inner_self_eq_one(_of_irreducible)` は `hi : i ≠ ind1H` 引数を追加取得。field は
> 引き続き lane a 所有。今後の変更は HUB issue 経由。詳細 = issue 0091。

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


### 2026-06-04 pass: conditional (7.11) from `CharacterEstimateData`

S09 に `not_trivial_G0_of_characterEstimateData` を追加。これは未完の
`card_G0_lower_bound` を経由せず、既に完成している `lowerBoundTerm_of_characterEstimateData`
と `lowerBoundTerm_pos` だけから `G₀ = {1}` の矛盾を出す conditional terminal theorem。

これにより §9 の最終矛盾は「`CharacterEstimateData` の構成」へ完全に局所化された。`card_G0_lower_bound`
本体の sorry はその data 構成部分に残るが、下流は必要なら conditional theorem を使って
sorryAx を避けられる。AxiomsCheck に登録して axiom-clean にする。


### 2026-06-04 pass: raw final assembly to conditional (7.11)

S09 に `not_trivial_G0_of_real_reduced_family_inequality_and_decomposition` を追加。これは
(7.5)/(7.8)/(7.9) が供給する形に近い real reduced family inequality と orthogonal integer
`𝓑`-sum decomposition から `CharacterEstimateData` を内部構成し、`G₀ = {1}` の矛盾まで進める。

これで §9 の terminal contradiction は、named `CharacterEstimateData` だけでなく raw final-assembly
input からも `card_G0_lower_bound` の sorry を通らず axiom-clean に利用できる。


### 2026-06-04 pass: Bsum-bound input to conditional (7.11)

S09 に `not_trivial_G0_of_real_Bsum_bound` を追加。これは `CharacterEstimateData` を
明示的に渡す代わりに、既に得られた `𝓑`-sum bound と real reduced family inequality から
`G₀ = {1}` の矛盾へ進む入口。

raw orthogonal decomposition からの入口と named data からの入口の中間に置くことで、(7.8)/(7.9)
側が先に `Bsum_le` を作った場合にも `card_G0_lower_bound` の sorry を経由せず使える。


### 2026-06-04 pass: displayed (7.10) bound to (7.11)

S09 に `not_trivial_G0_of_lowerBoundTerm` を追加し、`card_G0_lower_bound` の結論型そのものから
`G₀ = {1}` の矛盾へ行く terminal arithmetic を独立化した。既存の
`not_trivial_G0_of_characterEstimateData` と本 theorem `not_trivial_G0` はこの lemma に委譲する。

これで (7.10) をどの conditional input から作っても、(7.11) 側の証明重複なしに同じ入口へ流せる。


### 2026-06-04 pass: raw consumers for (7.8.b) norm estimates

S09 に `Hypothesis78.zetaNuRho_inner_self_re_ge_of_normEstimates` と
`Hypothesis78.gamma_inner_self_re_le_of_normEstimates` を追加。`NormEstimates` の named field を
後段 assembly が使う `ClassFunction.inner _ _ .re` 形へ展開する consumer で、特に後者は
(7.10) の orthogonal-integer decomposition bridge が要求する `Γ` norm-bound input に直接合う。

`BetaDecomp`/`NormEstimates` の存在そのものは引き続き genuine proof target のままにし、証明書を
新たに外出しする変更はしていない。

### 2026-06-04 pass: existential final assembly to (7.11)

S09 に `not_trivial_G0_of_exists_penultimate`, `not_trivial_G0_of_exists_Bsum_bound`,
`not_trivial_G0_of_exists_real_Bsum_bound` を追加。`card_G0_lower_bound` の sorry を経由せず、
(7.10) assembly が存在形で返す penultimate / rational `𝓑`-sum / real reduced `𝓑`-sum input から
直接 `G₀ = {1}` の矛盾へ進む terminal consumer。

これにより downstream は fixed-index 形だけでなく、Peterfalvi (7.10) の自然な existential output 形でも
axiom-clean な (7.11) conditional theorem を使える。

### 2026-06-04 pass: S07 coherence witness to S09 `ν` ZIrr-codomain

S09 に `Hypothesis78.nu_mem_ZIrr_of_isCoherent` と
`Hypothesis78.nu_mem_ZIrr_of_isCoherent_of_mem` を追加。`Hypothesis78` に `nu_maps_ZIrr`
のような証明書フィールドを足さず、具体的な S07 `IsCoherent` witness と `H78.nu = hcoh.extension`
を明示引数にして、`IsCoherent.extension_mem_ZIrr` を S09 側で使える形に変換する。

これは (7.8.a)/(7.9) で必要になる `νζ ∈ ℤ[Irr G]` 系の入力を、実際の coherence 構成から
引き出すための入口。抽象 `Hypothesis78.nu` 自体に新しい仮定は追加していない。

### 2026-06-04 pass: indexed source set for S09 coherence

S09 に `Hypothesis78.sourceSet`, `zeta_mem_sourceSet`, `zetaDistinct_mem_sourceSet`,
`nu_zeta_mem_ZIrr_of_isCoherent`, `nu_zetaDistinct_mem_ZIrr_of_isCoherent` を追加。
Peterfalvi (7.8) の `S = T \ {Ind 1_H}` を S09 側で名前付けし、具体的な S07
`IsCoherent τ H78.sourceSet A_prime` witness と `H78.nu = hcoh.extension` から indexed
`ζ_i` の `νζ_i ∈ ℤ[Irr G]` を直接得られる入口にした。

これで (7.8.a)/(7.9) の downstream proof は、set membership の都度の組み立てではなく
H78 の indexed API から `νζ_i` の ZIrr-codomain を取り出せる。

### 2026-06-04 pass: signed irreducible images from S07 coherence

S09 に indexed `zeta_inner_self_eq_one_of_irreducible`, `nu_zeta_inner_self_eq_one`,
`nu_zeta_inner_self_eq_one_of_irreducible` と、coherence witness から `νζ_i` を signed
irreducible character として取り出す
`exists_zsmul_irreducibleCharacter_nu_zeta_of_isCoherent` / distinguished `ζ` 版を追加。

`νζ_i ∈ ZIrr` と `‖νζ_i‖² = 1` からは符号が残るので、正性を hidden assumption にせず
`ε = ±1` の存在形で公開した。後段で `νζ_i(1) > 0` が得られる場合のために、同じ入力から
`IsIrreducibleCharacter (νζ_i)` を返す positive-degree bridge も追加した。


### 2026-06-04 pass: AxiomsCheck coverage for S09 consumer sockets

Gibbs explorer pass の指摘に従い、既存証明済みの S09 consumer sockets を `AxiomsCheck`
に追加登録した。対象は `BetaDecomp` algebra (`weightedNuSum_orth_*`, `delta_*`,
`betaNormSq_eq_*`)、(7.8.b) norm-package consumers、(7.9) の residual cross-term reduction、
および (7.10) の `FrobeniusFamily.CharacterEstimateData` final-assembly constructors。

これは新しい仮定や wrapper を足す変更ではなく、すでに S09 にある conditional theorem を downstream が
axiom-clean な入口として参照できるようにする coverage pass。特に `card_G0_lower_bound` の残 sorry を
迂回するものではなく、(7.8)/(7.9)/(7.10) の witness 構成後に接続すべき socket を明示化した。


### 2026-06-04 pass: source-data bridges for the (7.8.a) distinguished coefficient

S09 に `sourceZeta_inner_zetaDistinct_eq_ite_of_irreducible_distinct`,
`weightedNuSum_inner_zetaImage_eq_one_of_irreducible_source_data`,
`beta_inner_zetaImage_eq_int_sub_one_of_irreducible_source_data` を追加した。

これにより、source family `S = T \ {Ind 1_H}` が irreducible/distinct で、distinguished `ζ` の degree が
`e` であるという自然な (7.8) 入力から、(7.8.a) の distinguished column computation
`⟨Σ, νζ⟩ = 1` と `(β, νζ) = a - 1` を直接取り出せる。新しい証明書フィールドは追加しておらず、既存の
source orthogonality / weighted-sum consumer を downstream が再構成しなくてよい形にした bridge pass。


### 2026-06-05 pass: raw zeta-rho bound from source data

S09 に `zetaNuRho_inner_self_re_ge_of_inner_values_irreducible_source_data_and_uv_formula`
を追加した。既存の
`normEstimates_of_inner_values_irreducible_source_data_and_uv_formula` と
`zetaNuRho_inner_self_re_ge_of_normEstimates` を合成し、自然な source-side 入力、(7.7.b) の
`u,v,w` formula、`smallIndex` から raw class-function form
`1 - e/h ≤ ⟨(ζ^ν)^ρ,(ζ^ν)^ρ⟩.re` を直接得る downstream socket にした。


### 2026-06-05 pass: family-notated zeta-rho bound

S09 に `FrobeniusFamily.zetaNuRho_inner_self_re_ge_of_family_source_data`
を追加した。local `H78` 側の
`zetaNuRho_inner_self_re_ge_of_inner_values_irreducible_source_data_and_uv_formula`
を `F.e i` / `F.h i` 表記で使えるようにし、(7.5) の reduced-family inequality を
組む前段で `1 - e_i/h_i ≤ ⟨(ζ^ν)^ρ,(ζ^ν)^ρ⟩.re` を直接供給する bridge にした。


### 2026-06-05 pass: source-data zeta-rho norm formulas

S09 に `Hypothesis78.zetaNuRhoNormSq_eq_kernelRatio_mul_int_sub_one_of_irreducible_source_data`
と `FrobeniusFamily.zetaNuRhoNormSq_eq_familyRatio_mul_int_sub_one_of_source_data`
を追加した。既存の
`Hypothesis78.beta_inner_zetaImage_eq_int_sub_one_of_irreducible_source_data`
で source-side の `(β, νζ) = a - 1` を作り、(7.8.c.ii) の
`(ζ^ν)^ρ` norm formula に接続する bridge。

これで downstream は `u,v,w` formula を作る前段で、local `h/e` 表記と family `h_i/e_i`
表記の両方から同じ norm identity を直接呼べる。新しい証明書フィールドは追加していない。


### 2026-06-05 pass: family-notated Gamma bound

S09 に `FrobeniusFamily.gamma_inner_self_re_le_of_family_source_data` を追加した。
local `H78` 側の
`gamma_inner_self_re_le_of_inner_values_irreducible_source_data_and_uv_formula`
を `F.e i` / `F.h i` 表記で使える standalone bridge。

これで final assembly の orthogonal integer decomposition が必要とする
`(Γ,Γ).re ≤ e_i - 1` も、`ζ` 下界と同じ family-notated source-data 入力列で直接供給できる。


### 2026-06-04 pass: residual ZIrr bridges for (7.9)

S09 に `Hypothesis78.delta_mem_ZIrr_of_beta_mem_ZIrr_of_isCoherent` と
`Hypothesis79.delta_cross_integral_of_ZIrr` を追加した。前者は `β ∈ ZIrr G` と concrete S07
coherence witness から `Δ = β - 1_G + νζ ∈ ZIrr G` を作る bridge。後者は `Δ₁`, `Δ₂`,
`ζ₁^ν`, `ζ₂^ν` が virtual character であることから、(7.9) の residual cross terms が整数値になることを
`ClassFunction.inner_mem_ZIrr_int` へ落とす。

これで (7.9) の parity consumer `conclusion_of_delta_cross_integral_parity` に渡す入力のうち、
整数性部分は ZIrr membership へ局所化された。残る実数学入力は `β ∈ ZIrr` の構成、`(Δ₁,Δ₂)` の偶性、
および source/coherence 由来の `ζ` cross-orthogonality。


### 2026-06-04 pass: `β ∈ ZIrr` bridge from §4 Dade preservation

S09 に `Hypothesis78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr` を追加した。これは S09 の
`β = τ (Ind 1_H - ζ)` を、§4 の `IsDadeMap.unique` で canonical `hyp.dadeMap` に戻し、構成済みの
`fullDadeIsometryData.maps_virtualCharacter` を適用する bridge。入力は source-side の
`Ind 1_H - ζ ∈ ZIrr L` のみに切り出しているので、後段の Peterfalvi (7.8) arithmetic は Dade API と混ぜずに
独立 obligation として残る。


### 2026-06-04 pass: source-difference `ZIrr` from irreducible source terms

S09 に `Hypothesis78.sourceDiff_mem_ZIrr_of_irreducible` と
`Hypothesis78.beta_mem_ZIrr_of_irreducible_sourceDiff` を追加した。前者は
`ζ_ind1H`, `ζ` がともに irreducible character なら `Submodule.sub_mem` で
`ζ_ind1H - ζ ∈ ZIrr L` を返す最小 bridge。後者は直前の §4 Dade bridge と合成して
`β ∈ ZIrr G` を返す consumer で、(7.8)/(7.9) 側は source-side の lattice membership を直接扱わずに済む。


### 2026-06-04 pass: composed residual integrality consumers

S09 に `Hypothesis78.delta_mem_ZIrr_of_irreducible_sourceDiff_and_isCoherent`、
`Hypothesis79.delta_cross_integral_of_irreducible_sourceDiff_and_isCoherent`、
`Hypothesis79.conclusion_of_irreducible_sourceDiff_and_isCoherent_parity` を追加した。
これらは直前の `β ∈ ZIrr` bridge、coherence 由来の `νζ ∈ ZIrr`、既存の
`delta_cross_integral_of_ZIrr` / parity consumer を合成するだけの S09-facing socket。
(7.9) の downstream では、source irreducibility と coherence witness、さらに `(Δ₁,Δ₂)` の偶整数性を渡せば
`H79.conclusion` まで接続できる。


### 2026-06-04 pass: weaker residual and parity consumers

Gibbs explorer の指摘に従い、`Hypothesis78.delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent`、
`Hypothesis79.zetaImages_mem_ZIrr_of_isCoherent`、
`Hypothesis79.conclusion_of_delta_cross_even_of_ZIrr` を追加した。これにより `ind1H` source term は
irreducible である必要がなく、`ζ_ind1H ∈ ZIrr L` から `Δ ∈ ZIrr G` へ接続できる。
また (7.9) 側では coherence から二つの distinguished `ζ^ν` の `ZIrr` membership をまとめて取り出し、
`ZIrr` residuals と `(Δ₁,Δ₂)` 偶整数性から parity conclusion に直接入れる。


### 2026-06-04 pass: weak two-family residual consumers

S09 に `Hypothesis79.delta_cross_integral_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent` と
`Hypothesis79.conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity` を追加した。
既存の irreducible-source 版はこれらの特殊化に戻し、二族の (7.9) consumer でも
`Ind 1_H` source term には irreducibility ではなく `ZIrr` membership だけを要求する形に弱化した。
これで H78 側の weak residual bridge と H79 側の parity conclusion が同じ入力粒度で接続できる。


### 2026-06-04 pass: residual membership package

S09 に `Hypothesis79.delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent`
を追加した。H79 の weak source input から `Δ₁`, `Δ₂`, `ζ₁^ν`, `ζ₂^ν` の 4 つの
`ZIrr` membership をまとめて返す package theorem で、直前に追加した residual integrality/parity
consumer はこの package を使う形へ整理した。downstream は整数性 lemma を使う前に membership だけを取り出せる。


### 2026-06-04 pass: weak source-difference beta bridges

S09 に `Hypothesis78.sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible` と
`Hypothesis78.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible` を追加した。
H78 単体でも `Ind 1_H` source term は irreducible ではなく `ZIrr` membership で十分な形になり、
既存の irreducible 版と `delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent` は
この weak bridge への特殊化/合成に整理された。


### 2026-06-04 pass: support-driven zeta cross socket

S09 に `Hypothesis79.zetaImage_cross_eq_zero_of_support_subset` と
`Hypothesis79.conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity_of_zeta_support`
を追加した。これで (7.9) の `⟨ζ₁^ν, ζ₂^ν⟩ = 0` 入力は raw equality だけでなく、
二つの distinguished coherent image の support が disjoint Dade supports に入ることから生成できる。
将来の (4.1) `ν`-image support bridge と H79 parity consumer の接続点になる。


### 2026-06-04 pass: raw gamma bound from source data

S09 に
`Hypothesis78.gamma_inner_self_re_le_of_inner_values_irreducible_source_data_and_uv_formula`
を追加した。source inner-product values / source irreducibility-distinctness / degree-sum / `u,v,w` formula / small-index
をまとめて、(7.10) の `Bsum_le_of_orthogonal_integer_decomposition` が要求する
`(Γ, Γ).re ≤ e - 1` へ直接渡せる形にする consumer。


### 2026-06-04 pass: source-data final assembly constructor

S09 に
`FrobeniusFamily.characterEstimateData_of_real_reduced_family_inequality_and_source_decomposition`
を追加した。`H78` 側の source-data / `u,v,w` formula / small-index から得た `Γ` bound を、
`CharacterEstimateData` の real reduced family inequality + orthogonal decomposition constructor に直接接続する。
局所データと family index の接続は `H78.complementIndex = F.e i` として明示的に残した。


### 2026-06-04 pass: family/local cardinality bridges

S09 に `FrobeniusFamily.localKernelOrder_eq_h`,
`FrobeniusFamily.localComplementIndex_eq_e`,
`FrobeniusFamily.localSmallIndex_of_family_cardinalities` を追加した。
`H78` の局所 `h/e/smallIndex` を family 側の `F.h i` / `F.e i` / `2e_i+1≤h_i`
から供給できる。

さらに
`FrobeniusFamily.characterEstimateData_of_source_decomposition_of_family_cardinalities`
を追加し、前回の source-data final assembly constructor が要求していた local `hindex` と
`H78.smallIndex` を、`L = F.L i`, `H = F.H i`, family-side small-index から内部生成する入口にした。


### 2026-06-04 pass: family-notated source-data final assembly

S09 に `FrobeniusFamily.characterEstimateData_of_family_source_decomposition` を追加した。
source norm / distinguished degree / degree-sum / `u,v,w` formula の RHS をすべて family 側の
`F.e i` と `F.h i` で受け取り、前回追加した cardinality bridge で local `H78` 表記へ変換する。
これで downstream の (7.8.b) 入力は family notation のまま `CharacterEstimateData` へ接続できる。


### 2026-06-04 pass: family-source displayed lower bound

S09 に `FrobeniusFamily.lowerBoundTerm_of_family_source_decomposition` を追加した。
`characterEstimateData_of_family_source_decomposition` と同じ family-notated source inputs から、
`CharacterEstimateData` を明示的に作らずに、選んだ minimal index `i` の Peterfalvi (7.10) 表示下界を直接返す。
これで downstream は (7.5)/(7.8.b)/(7.9) 由来の family notation 入力を、`card_G0_lower_bound` の sorry を経由せず
表示下界 consumer へ接続できる。


### 2026-06-04 pass: family-source terminal contradiction

S09 に `not_trivial_G0_of_family_source_decomposition` を追加した。
前回の `FrobeniusFamily.lowerBoundTerm_of_family_source_decomposition` を existential (7.10) bound に包み、
`not_trivial_G0_of_lowerBoundTerm` に渡す terminal consumer。
これで family-notated source data / real reduced family inequality / orthogonal integer decomposition が揃った時点で、
`card_G0_lower_bound` の sorry を経由せず `G₀ = {1}` の矛盾まで直接閉じられる。

### 2026-06-04 pass: S08 Ind-chain bridge from H78 coherence

S09 に `Hypothesis78.indChainDecomposition_of_isCoherent` を追加した。
具体的な S07 `IsCoherent τ H78.sourceSet A'` witness と `H78.nu = extension` を受け取り、
任意の source family `ζ_t ∈ H78.sourceSet` と supported scaled differences から、S08 の
`IndChainDecomposition τ ζ d` を `χ_t = H78.nu ζ_t` として構成する。

これで S08 側に積み上げた weighted Ind-chain Parseval / scalar coefficient API を、S09 の
`Hypothesis78` 表記から直接起動できる。

### 2026-06-05 pass: H78 Ind-chain weighted consumers

S09 に `Hypothesis78.indChain_weightedOutput_inner_self_re_eq_sum_sq_of_isCoherent`,
`Hypothesis78.indChain_inner_chi_zero_image_weightedDifferenceInput_re_eq_one_sub_sum_sq_of_isCoherent`,
`Hypothesis78.indChain_inner_chi_zero_image_weightedDifferenceInput_re_nonpos_of_isCoherent` を追加した。
前回の `Hypothesis78.indChainDecomposition_of_isCoherent` で作った S08 `IndChainDecomposition` を、
S09/H78 の引数列から直接 S08 weighted Parseval / scalar coefficient API に渡す consumer 形。

これで downstream の (7.8)/(7.10) 側は、H78 の `ν` と concrete `IsCoherent` witness だけを持っていれば、
`data := ...` を毎回組み立てずに weighted output norm と weighted source-difference の非正性を使える。

### 2026-06-05 pass: H78 Ind-chain exact weighted identities

S09 に `Hypothesis78.indChain_image_weightedDifferenceInput_eq_weightedOutput_sub_sum_sq_smul_chi_zero_of_isCoherent`,
`Hypothesis78.indChain_image_weightedDifferenceInput_eq_weightedOutput_sub_norm_smul_chi_zero_of_isCoherent`,
`Hypothesis78.indChain_inner_chi_zero_image_weightedDifferenceInput_eq_one_sub_norm_of_isCoherent` を追加した。
`Hypothesis78.indChainDecomposition_of_isCoherent` で作る S08 `IndChainDecomposition` から、
weighted source-difference の exact image equation と complex scalar coefficient identity を H78/S07 witness 入力列で直接返す consumer 形。

前回追加した real Parseval / nonpos consumer と合わせて、§9 側は `data := ...` を手で組み立てず、
exact identity と実数不等式の両方を H78 表記から呼べる。

### 2026-06-05 pass: H78 raw Ind-chain weighted identities

S09 に `Hypothesis78.indChain_image_weightedDifferenceInput_of_isCoherent`,
`Hypothesis78.indChain_inner_chi_zero_image_weightedDifferenceInput_of_isCoherent`,
`Hypothesis78.indChain_one_le_weightedOutput_inner_self_re_of_isCoherent` を追加した。
S08 の生の weighted source-difference 展開、reference coefficient の `1 - ∑ d_t²` 形、
および `d 0 = 1` からの weighted output norm 下界を H78/S07 witness 入力列から直接返す。

これで downstream は normal form へ集約する前の Ind 方程式も、S09 の `Hypothesis78`
インターフェイスだけで参照できる。

### 2026-06-05 pass: H78 weighted output coefficient recovery

S09 に `Hypothesis78.indChain_inner_chi_eq_ite_of_isCoherent`,
`Hypothesis78.indChain_inner_chi_weightedOutput_of_isCoherent`,
`Hypothesis78.indChain_weightedOutput_inner_self_eq_sum_sq_of_isCoherent` を追加した。
S08 の output family orthonormality、weighted output の係数回収、
complex Parseval form を H78/S07 witness 入力列から直接返す adapter 形。

前回までの raw/normalized weighted Ind 方程式と合わせて、§9 downstream は
weighted output の係数・norm・image equation をすべて H78 表記から呼べる。

### 2026-06-05 pass: H78 per-term Ind-chain image equations

S09 に `Hypothesis78.indChain_image_eq_of_isCoherent` と
`Hypothesis78.indChain_image_eq_zero_of_isCoherent` を追加した。
S08 `IndChainDecomposition` の per-term image equation と reference-index vanishing を、
H78/S07 witness 入力列から直接返す adapter 形。

これで weighted sum に集約する前の各 source difference 項も、§9 側から `data := ...`
を手で作らず参照できる。

### 2026-06-05 pass: reduced family inequality from (7.5)

S09 に `reduced_inequality_of_estimates` を追加した。
これは (7.5) `family_inequality` を、(7.10) の `CharacterEstimateData.base_estimate`
へ渡す real reduced inequality まで実際に畳む補題。
入力は `G₀` 上の identity contribution
`1 ≤ Σ_{g∈G₀}|χ(g)|²`、選択 index `i` の下界 `c ≤ ‖χ^{ρ_i}‖²`、
および `𝓑` の外側で `‖χ^{ρ_j}‖² ≥ |A_j|/|L_j|` となる非負寄与。

これにより、従来 `hred` として外部仮定にしていた (7.5) 由来の不等式は、
(7.8)/(7.9) 側の各 `ρ` 下界を揃えれば S09 内で生成できる形になった。

### 2026-06-05 pass: concrete (7.5) family package to base estimate

S09 に `FrobeniusFamily.base_estimate_of_family71_reduced_estimates` と
`FrobeniusFamily.characterEstimateData_of_family71_reduced_estimates` を追加した。

これは前回の `reduced_inequality_of_estimates` を `CharacterEstimateData` 側へ直接接続する入口。
入力は concrete な `FamilyHypothesis71`、`A_i = H_i^#`、`L_i` と `G₀` の識別、
`G₀` 上の identity contribution、選択 index の (7.8.b) 下界
`1 - e_i/h_i ≤ ‖χ^{ρ_i}‖²`、および `𝓑` 外の非負寄与。

従来外部仮定だった `hred` は、この入口では (7.5) family inequality から生成される。

### 2026-06-05 pass: `G₀` identity contribution from signed irreducibility

S09 に `FrobeniusFamily.one_le_G0_norm_sum_of_signed_irreducible` と、
それを使う `base_estimate_of_family71_reduced_estimates_of_signed_irreducible` /
`characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible` を追加した。

これは Peterfalvi (7.10) proof の表示
`(|G₀|-1)/|G| ≥ (|G₀|-χ₁(1)^2)/|G|`
に対応する Lean 実装。`1 ∈ G₀` と
`χ₁ = ± ξ` (`ξ ∈ Irr G`) から `1 ≤ |χ₁(1)|²` を証明し、
前回 constructor の外部入力 `hG0sum : 1 ≤ Σ_{g∈G₀}|χ(g)|²` を
signed irreducible witness から生成できるようにした。

### 2026-06-05 pass: family (7.5), coherent image, and `𝓑` decomposition assembly

S09 に `characterEstimateData_of_family71_signed_decomposition`
と `characterEstimateData_of_family71_coherent_zeta_decomposition`
を追加した。

これは (7.10) の `CharacterEstimateData` 構成で残っていた外部入力をさらに削る pass。
(7.5) の concrete `FamilyHypothesis71` と per-index lower bounds から base estimate を作り、
(7.9) の orthogonal integer decomposition から `𝓑`-sum bound を作る。さらに coherent
source form では、`ζ` の irreducibility と S07 coherence witness から `νζ = ±ξ` を内部生成し、
前回 pass の `G₀` identity contribution に接続する。`hred`、`hBsum`、明示的な
signed-irreducible witness を同時に外へ出さずに `CharacterEstimateData` まで進められる。

### 2026-06-05 pass: family (7.5) + source-data (7.8.b) coherent assembly

S09 に `characterEstimateData_of_family71_coherent_zeta_source_data` を追加した。

前回の coherent `ζ` constructor は `hΓ_bound : ⟨Γ,Γ⟩.re ≤ e_i - 1` を外部入力にしていた。
今回の入口では既存の
`FrobeniusFamily.gamma_inner_self_re_le_of_family_source_data` を内部で使い、family-notated な
(7.8.b) source data (`hind_norm`, `hzeta_ind`, source irreducibility/distinctness, degree sum,
`u,v,w` formula, small-index) から `Γ` bound を生成する。これで concrete (7.5)、coherence
image、(7.8.b)、(7.9) decomposition が `CharacterEstimateData` まで同時に接続される。

### 2026-06-05 pass: S08 Frobenius coherence to H78 Ind-chain socket

S09 に `Hypothesis78.indChainDecomposition_of_coherenceOn` と
`Hypothesis78.indChainDecomposition_of_sibley_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData`
を追加した。

S08 の Frobenius/base-anchor X-chain、Y coherence、generator-level mixed-inner glue から、
set rewrite 前の `Xset H' ∪ Yset` coherence を直接作り、extension を `H78.nu` と
definitional に固定したまま S08 `IndChainDecomposition` を返す。

これで (6.8.1) Frobenius branch の証明済み assembly を、S09/H78 の weighted-chain consumer に
`card_G0_lower_bound` の sorry を経由せず接続できる。`hyp.CoherenceTarget` への rewrite は
extension の definitional equality を隠すため、この socket は union-level 入力を要求する。

### 2026-06-05 pass: family71 source data to displayed bound and contradiction

S09 に `FrobeniusFamily.lowerBoundTerm_of_family71_coherent_zeta_source_data` と
`not_trivial_G0_of_family71_coherent_zeta_source_data` を追加した。

既存の `characterEstimateData_of_family71_coherent_zeta_source_data` が組み立てる
concrete (7.5)、coherent image、(7.8.b) source estimates、(7.9) decomposition を、
中間 package に戻さず Peterfalvi (7.10) の表示下界と (7.11) の `G₀ = {1}` 矛盾へ直接接続する。

これで `card_G0_lower_bound` の残り assembly 義務は、抽象的な `CharacterEstimateData` ではなく、
教科書の concrete source-data package を存在させる問題として使える形に近づいた。

### 2026-07-14 — (7.10)/(7.11) final assembly complete

`S09_FrobeniusCardG0LowerBound.lean` で minimal kernel member と canonical character を選び、
完成済みの (7.8.b)、(7.8.c)、(7.9) concrete bounds から
`FrobeniusFamily.CharacterEstimateData` を実構成した。これを displayed (7.10)
`card_G0_lower_bound` と (7.11) `not_trivial_G0` へ接続し、§9 の proof-term `sorry` を閉じた。

一般 Frobenius-kernel nilpotence そのものはここで再証明せず、両 endpoint は per-member
nilpotence を入力に取る。FT 上の実 consumer では各 kernel が
`maxNilpotentNormalHall` なので、BG §15 の構成済み nilpotence と subgroup equivalence から
この入力を供給する。したがって最終 FT 経路には未充足の nilpotence 仮定を残さない。

import DAG は `S09_Building78C` を lower `FrobeniusFamily` leaf に向け、S09 hub が final leaf を
re-export する形にした。AxiomsCheck tripwire は constructor、(7.10)、(7.11) の全てで green。
