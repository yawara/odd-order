# BG §4 設計書 — Prop 4.11 (Huppert) / Thm 4.12 (Huppert) / Thm 4.16 (Blackburn)

> **目的**: §4 最難の 3 結果を **将来の実装セッション**が cold start で着手できる
> Lean 実装設計書。**DESIGN / READING ONLY** — 本書は実装しない、設計と精読のみ。
> 上位の高レベル引き継ぎは [`s04_thm416_handoff.md`](s04_thm416_handoff.md)、§4 全体 DAG は
> [`s04_implementation_plan_2026_05_30.md`](s04_implementation_plan_2026_05_30.md)。
> **本書はその 3 結果に対する詳細設計（exact signature / proof skeleton / 依存表 /
> scaffold-trap 監査 / sub-issue 分割）**。
>
> 作成 2026-05-30。mmd 全文精読済 (Prop 4.11 = L1554-1586, Thm 4.12 = L1588-1622,
> Thm 4.16 = L1636-1704, 補題群 4.2/4.5/4.8/4.9/4.10/4.13/4.14/4.15 含む)。

---

## 0. 最重要 — SCAFFOLD-TRAP 総論 (memory `scaffold-sorry-free-not-done`)

この 3 結果は **conditional scaffold で "sorry-free" を偽装できる典型**。判定基準を
冒頭で固定する:

> **Doneness = hypothesis constructibility, NOT sorry-count / AxiomsCheck RC.**

具体的な罠の形 (この 3 結果で実際に起きうるもの):

1. **未充足仮説への hoist**: 「Prop 4.8 (`r≤2`+exp p ⇒ `|R|≤p³`)」「Lem 4.5 general
   (extraspecial 判定)」「Aut(Eₚⁿ)≅GL(n,p) 橋」を `theorem foo (hP48 : ...) (hbridge : ...) : ...`
   と仮説に積めば本体は sorry なしで通る。だが **その仮説を ⊤ で埋める手段が無ければ未完**。
2. **「operator A が R/S に作用する」の偽装**: Thm 4.12 / 4.16 は `A` が商 `R/S` の Fₚ-加群に
   作用し Maschke で complement を取る。repo には **商への `MulAut` 持ち上げが無い** (§後述)。
   `letI : MulAction A (R⧸S) := sorry_action` 的な未構成 instance は最悪の scaffold。
3. **central product の表現詐欺**: Thm 4.16(2) の `R=R₁∘R₂` を「`R₁⊔R₂=⊤` だけ」で表すと
   `⁅R₁,R₂⁆=⊥` (中心化) と `R₁⊓R₂≤Z` を落とし、命題が弱くなる。`IsCentralProduct` の
   3 条件を全部 field 化すること。
4. **agemo `℧¹(R')` の未定義回避**: Prop 4.11 は `𝒰¹(R')` (= `℧¹`, p 乗の生成群) の
   非自明性で場合分け。これを `Subgroup.closure {x^p}` で定義せず「`R'` cyclic だから…」と
   論点先取りすると Huppert の核 (cyclic 判定) を仮定してしまう。

各結果の §4 (SCAFFOLD-TRAP AUDIT) に **step ごとの genuine/fake 判定**を置く。

---

## 1. repo 既存資産 (sorry-free GIVENS, 精読で確認済)

### 1.1 operator-action infrastructure (`A` が `R` に `φ : A →* MulAut R` で作用)

> **重要**: repo は BG の "`A` = p′-group of operators on `R`" を
> **`φ : A →* MulAut R`** で表す。`[R,A]` / `C_R(A)` の repo 表現は以下。これが
> Thm 4.12 / 4.16 の **唯一の正しい土台**。BG の集合論的 `[R,A]` をそのまま subgroup と
> 思い込むと型が合わない。

| BG 記法 | repo decl (exact) | ファイル:行 |
|---|---|---|
| `A`-不変述語 | `OddOrder.Isaacs.Ch03.IsAInvariant φ H` (`def := ∀ a, (φ a)•H = H`) | `Ch03_SplitExtensions/Main.lean:2894` |
| `C_R(A)` | `Subgroup.fixedPointsOfMulAut φ` (mathlib) | — (repo 多用, `IsAInvariant.fixedPointsOfMulAut` @ Ch03:3129) |
| `[R,A]` | `OddOrder.Isaacs.Ch04.actionCommutator φ` (`def := closure {g·(φ a)g⁻¹}`) | `Ch04_Commutators/Main.lean:2006` |
| **Prop 1.6(a)** `R=C_R(A)·[R,A]` | `fixedPoints_sup_actionCommutator_eq_top` (coprime+solvable) | `Ch04:2741` |
| **Prop 1.6(b)** `[R,A,A]=[R,A]` | `iterCommutator_inl_inr_two_eq_one` (**Γ=R⋊A 形, NOT R-内部形**) | `Ch04:2785` |
| **Prop 1.6(d)** abelian 直積 | `fixedPoints_inf_actionCommutator_eq_bot_of_abelian` (`C_R(A)⊓[R,A]=⊥`) | `Ch04:3386` |
| `IsAInvariant` の `⊓`/`⊔`/`⊤`/`⊥` 閉包 | `IsAInvariant.inf`/`.sup`/`.top`/`.bot` | `Ch03:2930-2945` |

⚠ **Prop 1.6(b) の形に注意 (scaffold-trap 源)**: `iterCommutator_inl_inr_two_eq_one` は
**半直積 Γ=R⋊[φ]A の中の `⁅⁅XG,YA⁆,YA⁆ = ⁅XG,YA⁆`** を主張する (`XG=inl.range`,
`YA=inr.range`)。BG Thm 4.12 が使う「`[R,A]=[R,A,A]` だから `R=[R,A]` と仮定してよい」の
**R-内部 subgroup 版 (`actionCommutator (R↾[R,A] への制限作用) = [R,A]`)** とは直接同型でない。
変換には `actionCommutator φ = (inl⁻¹ image of ⁅XG,YA⁆)` 系の補題が要る — これは
**needs-impl**。下記 §3 で扱う。

### 1.2 §4 v1 で揃った GIVENS (`S04_PGroupsSmallRank.lean`, sorry-free)

| 内容 | decl (exact) |
|---|---|
| Lem 4.2(a) 左 | `commutatorElement_pow_left_of_central` |
| Lem 4.2(a) 右 | `commutatorElement_pow_right_of_central` |
| Lem 4.2(b) | `mul_pow_eq_mul_commutator_pow_of_central` |
| Lem 4.5(a) 存在 (非 normal) | `exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic` |
| Lem 4.5(a) normal (abelian-center case のみ) | `exists_normal_isElementaryAbelian_card_prime_sq_of_prime_sq_dvd_card_omega1Center` |
| Lem 4.7 ⇒ (易方向) | `scn3_empty_of_pRank_le_two`, `not_le_pRank_of_pRank_le_two` |
| **GL(2,p) エンジン** | `isPGroup_commutator_of_faithful_two_dim_charP` (Thm 2.6(b) 導来形) |
| 2 次元 faithful ⇒ Sylow abelian | `OddOrder.BG.Ch1.S02.odd_two_dim_sylow_abelian` (`hodd`,`hdim:finrank=2`,`ρ`,`hfaithful`,`hp_dvd`,`hchar:CharP`,`P:Sylow`) |

### 1.3 GroupTheory shared modules (sorry-free)

| 概念 | decl / 場所 |
|---|---|
| `pRank G p` / `rank G` | `PRank.lean`: `pRank_le_iff`, `le_pRank`, `pow_le_card_of_le_pRank`, `pRank_mono_of_le`, `IsElementaryAbelian.card_eq_pow_finrank`, `.log_card_eq_finrank` |
| SCN | `SCN.lean`: `IsSCN`, `IsSCN_n`, `IsSCN₃`, `isSCN_iff_isMaximalAbelianNormal` (Prop 4.4(a)), `IsSCN_n.le_pRank` |
| `Ω_n(G)` (closure 形) | `OmegaSubgroup.lean`: `Omega G p n`, `Omega.mem_of_pow_eq_one`, `Omega.mono`, `Omega.characteristic` (instance) |
| `Ω₁` of abelian | `OmegaSubgroup.lean`: `omega1OfAbelian G H p hH`, `mem_omega1OfAbelian`, `omega1OfAbelian_le` |
| metacyclic | `IsMetacyclic.lean`: `IsMetacyclic G` (`def := ∃ N, N.Normal ∧ IsCyclic N ∧ IsCyclic (G⧸N)`), `.of_isCyclic`, `.isSolvable` |
| extraspecial | `IsExtraspecial.lean`: `IsExtraspecial p G` (4 fields: `isPGroup`/`commutator_eq_center`/`frattini_eq_center`/`center_card=p`), `.commutator_card`, `.frattini_card` |
| Thompson critical (Thm 1.13) | `S01_Solvable.lean:845` `thompson_critical_omega` (`hp_odd`,`hG:IsPGroup` ⇒ ∃ `H` char, `[H,⊤]≤Z(H)`, cl≤2, `exp H = p`, `IsPGroup p (autCentralizer H)`) |
| Ω₁ exp p (cl≤2) | `CriticalSubgroup.lean:740` `Omega.pow_eq_one_of_class_le_two`, `:755` `Omega.exponent_eq_of_class_le_two` |
| `Omega.pow` (class≤2 power) | `CriticalSubgroup.lean` `mul_pow_eq_commutator_pow_mul_of_class_le_two` |

### 1.4 mathlib 確認済

* **`Matrix.card_GL_field`** あり (`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean:89`):
  `Nat.card (GL (Fin n) 𝔽) = ∏ i : Fin n, (q ^ n - q ^ (i:ℕ))` (`q = Fintype.card 𝔽`)。
  n=2,q=p ⇒ `(p²-1)(p²-p) = p(p²-1)(p-1)` (BG L1658 と一致)。
  **ただし `Aut(Eₚⁿ : F_p^n の群自己同型) ≅ GL(n,p)` の *群同型* は mathlib に無い** (needs-impl)。
* `Subgroup.fixedPointsOfMulAut` / `Subgroup.mem_fixedPointsOfMulAut` あり (mathlib)。
* Maschke (Thm 1.20): `Mathlib/RepresentationTheory/Maschke.lean` (repo S01 注記 `Ch04:1172`)。
  **ただし「`A`-invariant complement of a submodule」の subgroup-of-R 形は要 bridge** (§3/§4)。

---

## 2. 共通の needs-impl (3 結果が共有する前提補題)

実装順の前提。**これらが揃うまで Prop 4.11 / Thm 4.12 / Thm 4.16 本体は scaffold-trap に陥る**。

### N-1. agemo `℧ⁿ(R)` (= BG `𝒰ⁿ(R)`)  — **needs-impl** ⭐
```lean
-- OddOrder/GroupTheory/OmegaSubgroup.lean に追加 (Omega の双対)
def Agemo (G : Type*) [Group G] (p n : ℕ) : Subgroup G :=
  Subgroup.closure {g : G | ∃ x : G, g = x ^ (p ^ n)}
-- 必要補題:
--   Agemo.mono : m ≤ n → Agemo G p n ≤ Agemo G p m  (注: agemo は逆向き単調)
--   Agemo.characteristic : instance (Omega.characteristic と同型の証明)
--   (abelian H で) `℧¹(H) = ⟨h^p : h∈H⟩` の像同定
```
使用箇所: Prop 4.11 の `𝒰¹(R')≠1` 場合分け (mmd L1558, L1566-1570)、Thm 4.12 では暗黙。
**scaffold-trap**: これを定義せず Prop 4.11 を書くと `𝒰¹(R')` の議論が宙に浮く。genuine な
新規 def。

### N-2. `IsCentralProduct` — **needs-impl** ⭐ (Thm 4.16(2) 専用)
```lean
-- OddOrder/GroupTheory/CentralProduct.lean (新規)
structure IsCentralProduct {G : Type*} [Group G] (R₁ R₂ : Subgroup G) : Prop where
  sup_eq_top   : R₁ ⊔ R₂ = ⊤              -- G = R₁ R₂
  commute      : ⁅R₁, R₂⁆ = ⊥             -- R₁ centralizes R₂
  -- (normal は commute + sup から従うので field にしなくてよいが、
  --  BG def は R_i ⊴ G を要求。R₁⊔R₂=⊤ & ⁅R₁,R₂⁆=⊥ ⇒ R₁,R₂ ⊴ G を補題で出す)
```
mmd 定義 = L1377-1381 (`G=G₁∘⋯∘Gₙ`: `Gᵢ⊴G`, `Gᵢ` が `Gⱼ` を中心化 (i≠j), `G=G₁⋯Gₙ`)。
**注意**: `R₁⊓R₂ ≤ Z(G)` は `⁅R₁,R₂⁆=⊥` から導けるので別 field 不要だが、Thm 4.16(2) の
`Ω₁(R₂)=R₁'` まで含めると **full statement は `IsCentralProduct` + 追加等式**。
**scaffold-trap**: `commute` を落として `sup_eq_top` だけにしない。

### N-3. exp-p extraspecial — **needs-impl** (軽量)
```lean
-- IsExtraspecial.lean 拡張 or S04 局所
def IsExpPExtraspecial (p : ℕ) (G : Type*) [Group G] : Prop :=
  IsExtraspecial p G ∧ Monoid.exponent G = p
-- order p³ は (extraspecial + exp p + r≤2) から従う; Thm 4.16(2) では別途 |R₁|=p³ を持つ
```

### N-4. operator `A` の **商 `R/S` への作用** — **半分 DONE / Maschke のみ残** ⭐ (2026-05-30 更新)

> ⚠ **訂正 (2026-05-30)**: 本節は当初「商作用持ち上げ全体が needs-impl」と書いたが **誤り**。
> **φ̄ lift は既に Ch04 に存在**: `IsAInvariant.quotientMulAutHom` (`Ch04_Commutators/Main.lean:2248`,
> commit d53f690) + apply 補題 (`quotientMulAutHom_apply`) + descent `actionCommutator_quotient_eq_map`
> (`[R/S,A] = [R,A].map (mk' S)`) + `≤N ⇒ [R/S,A]=⊥`。**再実装してはならない** (重複。`bg-s04-n4-quotient-action`
> workflow が誤って再実装し破棄した経緯あり)。残るのは **Maschke complement bridge のみ** = 設計書
> [`s04_n4_maschke_bridge_design.md`](s04_n4_maschke_bridge_design.md) (難度 ⭐⭐ → ⭐ にダウングレード;
> Maschke 自体 mathlib 完成、type-plumbing ~5-8 補題)。⚠ **既存 `quotientMulAutHom` は `_root_` 欠落で
> 実名が `OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom` と二重 nest** —
> Ch04 外から呼ぶには名前解決に難あり (Ch04 修正 issue で対応予定)。
> なお **`[R,A]=⊤ ⇒ [R/S,A]=⊤`** は `actionCommutator_quotient_eq_map` + `map_top_of_surjective` の
> 2 行で出る (Maschke 段で inline 可、専用補題不要)。

Thm 4.12 / 4.16 の Maschke 段は **`A` が `R/S` (S は A-invariant normal) に作用する** ことを要する。
repo の `φ : A →* MulAut R` から `φ̄ : A →* MulAut (R⧸S)` を作る (= **既存 `quotientMulAutHom`**)。
```lean
-- needs-impl: A-invariant normal S に対する商作用の持ち上げ
--   φ̄ a := MulAut induced by (φ a) on R⧸S  (well-defined ∵ S が (φ a)-invariant)
-- さらに「A-invariant complement」を Maschke から取り出す subgroup 形:
--   Ω₁(R/S) を F_p-加群と見て A-submodule W の A-invariant complement X/S
```
Ch03 に `MulAut.conj` の商への intertwine (`Ch03:942-943` の `h_intertwine`) があるが、これは
**inner (conj) auto** 専用で `φ a` 一般の商持ち上げではない。**genuine な needs-impl**。
**これが §4 で最も scaffold-trap を生みやすい**: 「`A` が `R/S` に作用する」を未構成 instance
(`MulAction A (R⧸S) := sorry`) で誤魔化すと全体が崩れる。

### N-5. Prop 4.8 / Lem 4.5 general / Lem 4.9 / Lem 4.10 — **一部 DONE** (Wave 2、本書範囲外だが前提)

> **更新 (2026-05-30, commit 46e9e5c)**: ✅ **Lem 4.5(b) + Lem 4.10 完全達成**, ⚠ Prop 4.3(a) cl≤3 は precursor のみ (下記)。残 needs-impl = Prop 4.8(a)(b) / Lem 4.5(a)-general / Lem 4.5(c) (4.5(a)-general 待ち) / Lem 4.9 / Prop 4.3(a) cl≤3 の full collection+|R|帰納 / Prop 4.3(b)。
* **Prop 4.8(a)** (`r≤2` + exp p ⇒ `|R|≤p³`): SCN `A` を取り `|R/A|=|R/C_R(A)| ≤ |Aut A|_p ≤ |GL(2,p)|_p = p`
  (mmd L1516-1518)。`|Aut A|_p ≤ p` は **Aut(Eₚ²)≅GL(2,p)** 橋 + `|GL(2,p)|_p=p` 要 (N-6)。
* **Prop 4.8(b)** (`p>3` ⇒ `Ω₁(R)` exp 1 or p): minimal counterexample + cl≤3 (mmd L1520)。
* ~~**Lem 4.5(b)**~~ ✅ **DONE** (2026-05-30, commit 46e9e5c, `isElementaryAbelian_omega1_of_isCyclic_index_prime` @S04, sorry-free/axiom-clean)。crux `|Ω₁|≤p²` を hoist せず証明 — 核 `x^p∈Z(R)` は **Gorenstein 5.4.3/4.4 を引かず Isaacs Thm 6.12/Lem 6.16 共役エンジン再利用**で達成 (ZMod 自前計算回避)。Prop 4.11 step 8 / Thm 4.12 が直接呼べる。
* **Lem 4.5(c)** (`Ω₁(Z₂(R))` noncyclic exp p): 4.5(a)+Prop 4.3(a)。
* **Lem 4.9** (`p>3`, `|Ω₁(R)|≤p²` ⇒ `|Ω₁(R/T)|≤p²` ∀ `T⊴R`): mmd L1522-1544、Prop 4.11 の帰納で必須。
* ~~**Lem 4.10**~~ ✅ **DONE** (2026-05-30, commit 46e9e5c, `isElementaryAbelian_omega1_of_isMetacyclic` @S04, sorry-free/axiom-clean)。4.5(b) の系。Thm 4.12 が直接呼べる。
* ⚠ **Prop 4.3(a) cl≤3 は precursor のみ** (2026-05-30, commit 46e9e5c): linchpin `commutatorElement_pow_left_of_triple_central` (γ₃⊆Z ⇒ `⁅u^n,w⁆=⁅u,w⁆^n·⁅u,⁅u,w⁆⁆^C(n,2)`) + helper は green。**全 (u*v)^n collection + |R| 帰納は未完**。判明した注意: 全 collection は **γ₄=1** を要し, BG の f(n)=C(n,3)/g(n)=2C(n,3)+C(n,2) exponent は **mathlib commutator convention で誤り** (n=2 で `(uv)²=u·⁅v,u⁆·u·v²` の単一非中心項; 数値検証で BG-literal 形は 624/1200 失敗, mathlib-mirror 形は 0/1200)。再開時は mirror で f/g を再計算せよ。Prop 4.11 step (φ準同型) で要るのは Prop 4.3(**b**) で, これは未着手。

### N-6. Aut(Eₚⁿ) ≅ GL(n,p) 橋 — **needs-impl** ⭐ (Lem 4.13 / Prop 4.8 / Thm 4.16 文脈)
elementary abelian `E` (order pⁿ) に対し `MulAut E ≃* GL (Fin n) (ZMod p)`。
mathlib `Matrix.card_GL_field` で位数は出るが、**群同型は自前**。`E` を `(ZMod p)`-加群
(`PRank.lean` の `IsElementaryAbelian.zmodModule`) と見て `MulAut E ≃ (加群自己同型) ≃ GL`。
**scaffold-trap**: Lem 4.13 (q∣|Aut R| ⇒ q∣p²-1) と Prop 4.8 はこの橋に乗る。橋を仮説に
hoist すると見かけ上 sorry-free。

---

## 3. Prop 4.11 (Huppert): `p>3`, `|Ω₁(R)|≤p²` ⇒ `R` metacyclic

mmd: **L1554-1586** (PDF p.39, Huppert Satz III.11.6)。**§4 第2の山**。

### 3.1 提案 Lean signature

```lean
/-- **BG Proposition 4.11** (Huppert). `p` 素数, `p>3`, `R` 有限 `p`-群,
`|Ω₁(R)| ≤ p²` ⇒ `R` は metacyclic. -/
theorem isMetacyclic_of_omega1_card_le_prime_sq
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R) (hp3 : 3 < p)
    (hΩ : Nat.card (Omega R p 1) ≤ p ^ 2) :
    OddOrder.GroupTheory.IsMetacyclic R
```
**注**: `Omega R p 1` は closure 形 (非 abelian R で正しい `Ω₁`)。`hp3 : 3 < p` から
`Odd p` (奇) と `p > 3` を両方使う。

### 3.2 proof skeleton (mmd L1556-1586 keyed)

帰納 `|R|`。
1. **(L1558) abelian なら自明** (`IsCyclic`×`IsCyclic` or 直接 `IsMetacyclic.of_isCyclic`系)。
   `R` abelian ⇒ `Ω₁(R)` = abelian の `Ω₁`、`|Ω₁(R)|≤p²` ⇒ rank ≤2 ⇒ metacyclic。
   *(abelian 版 metacyclic は別途: 有限 abelian p-群で `Ω₁≤p²` ⇒ 高々 2 生成 ⇒ metacyclic)*。
2. **(L1558) `R` 非 abelian と仮定** ⇒ `1 ⊂ R' ⊴ R` ⇒ `R'∩Z(R)≠1`。
   `T := ⟨z⟩ ≤ R'∩Z(R)`, `|T|=p`, さらに `𝒰¹(R')≠1` なら `T ⊆ 𝒰¹(R')∩Z(R)` に取る。
   → **N-1 (agemo) 必須**。
3. **(L1560) Lem 4.9** で `|Ω₁(R/T)|≤p²` ⇒ 帰納で `R/T` metacyclic。
   → **N-5 (Lem 4.9) 必須**。商 `R⧸T` への帰納 (`T⊴R` ∵ `T≤Z(R)`)。
4. **(L1560-1562) (4.7)**: `R/T` metacyclic ⇒ ∃ `a,b∈R` で `⟨a,z⟩⊴R`, `R=⟨a,b,z⟩`。
   (持ち上げ: `R/T` の cyclic normal `⟨ā⟩` の preimage `⟨a,z⟩`。)
5. **(L1564)** `R'⊆⟨a,z⟩`。`R/T` cyclic なら `R/Z(R)` cyclic ⇒ Lem 4.1 で `R` abelian (矛盾)
   ⇒ `R/T` 非 cyclic ⇒ `⟨a,z⟩/⟨z⟩≠1`。`⟨a,z⟩/⟨aᵖ,z⟩` は `R/⟨aᵖ,z⟩` の位数 p の normal ⇒
   中心に含まれ `[a,b]=aⁱᵖzʲ`。
6. **(L1566-1570) 場合 `𝒰¹(R')≠1`**: `⟨z⟩=T⊆𝒰¹(R')⊆𝒰¹(⟨a,z⟩)=𝒰¹(⟨a⟩)⊆⟨a⟩` ⇒ `R` metacyclic by (4.7)
   (∵ `⟨a,z⟩=⟨a⟩` cyclic normal, `R/⟨a⟩` cyclic)。→ **N-1 (agemo) 必須**。
7. **(L1570-1582) 場合 `𝒰¹(R')=1`**: `R'` elementary abelian (∵ `|Ω₁(R)|≤p²` & `𝒰¹(R')=1`)。
   `aᵇ = a[a,b] = a^{1+ip}zʲ`、`[a,b]^b=[a,b]` (L1578 の計算) ⇒ `[a,b]∈Z(R)` ⇒ `R'=⟨[a,b]⟩` cyclic。
   → **Lem 4.2(a)(b)** (repo 既存 `commutatorElement_pow_*_of_central`) を直接使う計算。
8. **(L1584-1586) cyclic 判定で締め**: `S` = `R'⊆S` な maximal cyclic subgroup。`S⊴R`, `S≠R`。
   `S₁⊇S`, `|S₁/S|=p` ⇒ `S₁` 非 cyclic ⇒ Lem 4.5(b) で `|Ω₁(S₁)|=p²` ⇒ `Ω₁(S₁)=Ω₁(R)`,
   `S₁=Ω₁(R)S` 一意 ⇒ `R/S` が唯一の位数 p 部分群 ⇒ Lem 4.5 で `R/S` cyclic ⇒ `R` metacyclic。
   → **N-5 (Lem 4.5(b))** 必須。

### 3.3 依存表

| step | 依存 | 状態 |
|---|---|---|
| 1 | abelian metacyclic (有限 abelian p-群 `Ω₁≤p²` ⇒ ≤2生成) | **needs-impl** (軽。`FiniteAbelian` 分解 + `Ω₁` 次元) |
| 2 | `R'∩Z(R)≠1` (`R'⊴R`, p-群 ⇒ 非自明 normal は中心と交わる) | mathlib/repo: `IsPGroup` 中心交差 (`Subgroup.center` ∩ normal) ほぼ既存パターン |
| 2,6 | **agemo `𝒰¹`** | **needs-impl N-1** |
| 3 | **Lem 4.9** | **needs-impl N-5** |
| 3,4 | 商 metacyclic の preimage 持ち上げ | **needs-impl** (IsMetacyclic の商→preimage) |
| 5 | Lem 4.1 (`G/Z cyclic ⇒ abelian`) | mathlib: `Subgroup.center` quotient cyclic ⇒ comm。**要確認/軽 impl** |
| 7 | Lem 4.2(a)(b) | **exists** `commutatorElement_pow_left/right_of_central`, `mul_pow_eq_mul_commutator_pow_of_central` |
| 8 | **Lem 4.5(b)** (cyclic index p ⇒ Ω₁≅Eₚ²) | **needs-impl N-5** |
| 8 | maximal cyclic subgroup 存在 (有限性) | 軽 (有限 poset の極大元) |

### 3.4 SCAFFOLD-TRAP AUDIT (Prop 4.11)

| step | genuine か / 罠か | リスク度 |
|---|---|---|
| 1 abelian case | **genuine**。だが「abelian ⇒ metacyclic」を `hAb→metacyclic` で hoist して放置しがち。abelian p-群 `Ω₁≤p²` ⇒ 高々 2 生成 を **実証**せよ (`CommGroup.equiv_prod_multiplicative_zmod` 分解で因子数 ≤2)。 | **中** |
| 2 `R'∩Z≠1` | genuine, 標準。p-群の非自明 normal ∩ center。 | 低 |
| 3 Lem 4.9 適用 | **罠の温床**。Lem 4.9 自体が mmd L1522-1544 の独立帰納 (Prop 4.8 依存)。`(hLem49 : ∀ T⊴R, |Ω₁(R/T)|≤p²)` と hoist すると Prop 4.11 は通るが **Lem 4.9 が未実装なら未完**。Lem 4.9 を **先に sorry-free 実装**してから本体。 | **最高** |
| 6 `𝒰¹(R')≠1` branch | **罠**: agemo 未定義だと `𝒰¹(⟨a,z⟩)=𝒰¹(⟨a⟩)` の等式が宙に浮く。N-1 を genuine def で。 | 高 |
| 7 `R'=⟨[a,b]⟩` cyclic | **genuine**。Lem 4.2 計算 (repo 既存) で閉じる。ここは scaffold 不要、実証可能。**本結果で最も「実際に Lean が書ける」中核**。 | 低 |
| 8 cyclic 判定 | **罠**: Lem 4.5(b) (N-5) を hoist しがち。`(hL45b : ...) ` 形は未完。Lem 4.5(b) を先に。 | 高 |

**結論 (Prop 4.11)**: 本体の論理 (step 4,5,7) は repo 既存 Lem 4.2 で書ける genuine 部分。
だが **step 3 (Lem 4.9) と step 8 (Lem 4.5(b)) と step 2/6 (agemo) が hoist 罠の本体**。
**実装順は「N-1 agemo → Lem 4.9 → Lem 4.5(b) を各々 sorry-free → 然る後 Prop 4.11 本体」**。
これらを仮説に積んだ "sorry-free Prop 4.11" は **未完成**と判定する。

---

## 4. Thm 4.12 (Huppert): metacyclic + p′-operator `A`, `[R,A]=R` ⇒ `R` abelian (+ (b)(c))

mmd: **L1588-1622**。Prop 4.11 と Thm 4.16 を繋ぐ。

### 4.1 提案 Lean signature (operator は `φ : A →* MulAut R`)

```lean
/-- **BG Theorem 4.12(a)** (Huppert). `p` 奇素数, `R` metacyclic `p`-群,
`A` が `R` に作用 (`φ : A →* MulAut R`), `(|A|,|R|)` coprime かつ `[R,A]=R`
(`actionCommutator φ = ⊤`) ⇒ `R` abelian. -/
theorem isMulCommutative_of_metacyclic_actionCommutator_eq_top
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    (hR : IsPGroup p R) (hmeta : OddOrder.GroupTheory.IsMetacyclic R)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hRA : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤) :
    IsMulCommutative R
```
(b)(c) は別 theorem。**(b)** `T:=[R,A]` で `T∩C_R(A)=1`、**(c)** `T,C_R(A)` cyclic ∧ `R'⊆T`。

```lean
/-- **BG Theorem 4.12(c)**: `T=[R,A]`, `C=C_R(A)` ⇒ `T` cyclic, `C` cyclic, `R'⊆T`. -/
theorem thm412c_structure
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    (hR : IsPGroup p R) (hmeta : IsMetacyclic R)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R)) :
    IsCyclic (OddOrder.Isaacs.Ch04.actionCommutator φ)
      ∧ IsCyclic (Subgroup.fixedPointsOfMulAut φ)
      ∧ commutator R ≤ OddOrder.Isaacs.Ch04.actionCommutator φ
```

### 4.2 proof skeleton (mmd L1590-1622)

**(a)** 帰納 `|R|`:
1. **(L1590) Prop 1.6(b)** `[R,A]=[R,A,A]` ⇒ `R=[R,A]` と仮定してよい (`hRA`)。
   → repo `iterCommutator_inl_inr_two_eq_one` (**Γ形, §1.1 の変換 needs-impl 注意**)。
2. **(L1592-1600)** `R` metacyclic ⇒ `R'` cyclic。`S` = A-invariant cyclic, `R'⊆S` maximal。
   `S⊴R` & `S⊴RA`。`Aut S` abelian ⇒ `R=[R,A]⊆(RA)'⊆C_{RA}(S)` ⇒ `S⊆Z(R)` (4.9)。
   → **needs-impl**: 「metacyclic ⇒ R' cyclic」(IsMetacyclic の commutator)、A-invariant cyclic
     subgroup の極大選択、`Aut(cyclic)` abelian。
3. **(L1602-1608)** `R/S` abelian (∵ `R'⊆S`)。`Ω₁(R/S)` を Fₚ-加群かつ A-加群と見て、**Maschke**
   で `Ω₁(R)S/S` の A-invariant complement `X/S` を取る。Lem 4.10 で `Ω₁(R)` elem ab ⇒
   `X∩Ω₁(R)=Ω₁(S)` ⇒ `|Ω₁(X)|≤|Ω₁(S)|=p` ⇒ Lem 4.5 で `X` cyclic ⇒ maximal で `X=S` ⇒
   `Ω₁(R/S)=Ω₁(R)S/S`。
   → **N-4 (商作用) + Maschke subgroup 形 + Lem 4.10 (N-5) + Lem 4.5(b) (N-5)**。
4. **(L1610-1614)** `|Ω₁(R/S)|=|Ω₁(R)/Ω₁(R)∩S|≤|Ω₁(R)/Ω₁(S)|≤p` ⇒ Lem 4.5 で `R/S` cyclic ⇒
   `R/Z(R)` cyclic (∵ `S⊆Z(R)`) ⇒ Lem 4.1 で `R` abelian。

**(b)** `T=[R,A]`, Prop 1.6 で `[T,A]=T`, `R=T·C_R(A)`, `T=[T,A]×C_T(A)=T×(T∩C_R(A))`
⇒ `T∩C_R(A)=1`。→ Prop 1.6(d) = `fixedPoints_inf_actionCommutator_eq_bot_of_abelian` (但し
abelian 仮定; (a) で `R` abelian 確定後に適用) **exists**。

**(c)** (a) で `1⊂T⊂R` (proper) ⇒ `C_R(A)≠1`。(b) で `T∩C_R(A)=1` ⇒
`|Ω₁(R)|≥|Ω₁(T)||Ω₁(C_R(A))|≥p²`。Lem 4.10 で `|Ω₁(R)|≤p²` ⇒ `|Ω₁(T)|=|Ω₁(C_R(A))|=p` ⇒
Lem 4.5 で両者 cyclic。`T⊴R`,`R=T·C_R(A)` ⇒ `R'⊆T`。

### 4.3 依存表

| step | 依存 | 状態 |
|---|---|---|
| a-1 | Prop 1.6(b) `[R,A,A]=[R,A]` | **exists (Γ形)** `iterCommutator_inl_inr_two_eq_one` → **要変換 needs-impl** (R-内部 actionCommutator 形へ) |
| a-2 | metacyclic ⇒ `R'` cyclic | **needs-impl** |
| a-2 | A-invariant cyclic 極大 subgroup | **needs-impl** (A-invariant subgroup の poset 極大) |
| a-2 | `Aut(cyclic)` abelian | mathlib: `IsCyclic` ⇒ `Aut` comm (`CommGroup (ZMod n)ˣ` 系)。**要確認** |
| a-3 | **商 `R/S` への A 作用** | **needs-impl N-4** ⭐⭐ |
| a-3 | Maschke (A-invariant complement, subgroup-of-Ω₁ 形) | mathlib Maschke + **bridge needs-impl** |
| a-3,c | **Lem 4.10** (`Ω₁(R)` elem ab), **Lem 4.5(b)** | **needs-impl N-5** |
| a-4 | Lem 4.1 (`R/Z cyclic ⇒ abelian`) | 軽 needs-impl/mathlib |
| b | Prop 1.6(d) `C_R(A)⊓[R,A]=⊥` (abelian) | **exists** `fixedPoints_inf_actionCommutator_eq_bot_of_abelian` |
| b | `R=[R,A]·C_R(A)` | **exists** `fixedPoints_sup_actionCommutator_eq_top` (coprime+solvable; A solvable は odd order で可) |
| c | `|Ω₁(R)|≥|Ω₁(T)||Ω₁(C)|` (T∩C=1 ⇒ 積) | 軽 (disjoint normal の積位数) |

### 4.4 SCAFFOLD-TRAP AUDIT (Thm 4.12)

| step | genuine か / 罠か | リスク度 |
|---|---|---|
| a-1 Prop1.6(b) | **罠 (型不一致)**: repo の `iterCommutator_inl_inr_two_eq_one` は **Γ=R⋊A 形**。BG が使う「R-内部 `[[R,A],A]=[R,A]` ⇒ `R=[R,A]` reduction」へ持っていく **変換補題が needs-impl**。これを暗黙に同一視すると未充足。先に `actionCommutator_iterCommutator_two_eq` 的橋を sorry-free に。 | **高** |
| a-3 **商作用 + Maschke** | **最高リスク**。`A` が `R/S` に作用 (N-4) を未構成 instance で誤魔化すと全滅。Maschke の「complement」を `(hX : ∃ X, IsAInvariant ... ∧ X is complement)` で hoist しても、**N-4 が無ければ X を構成できない**。N-4 → Maschke bridge を **genuine に積み上げてから**。 | **最高** |
| a-2 metacyclic⇒R'cyclic | genuine だが needs-impl。IsMetacyclic def から `commutator R ≤ N` (cyclic normal) を出す。 | 中 |
| b | **genuine, 実証可能**。Prop 1.6(d)(a) は repo 既存。(a) で R abelian 後に直適用。**本結果で最も書ける部分**。 | 低 |
| c | genuine。Lem 4.10/4.5(b) (N-5) 依存だが論理は素直。 | 中 (N-5 待ち) |

**結論 (Thm 4.12)**: (b) は repo 既存 Prop 1.6(d) でほぼ即。(a) が **N-4 (商作用) の上に
Maschke を乗せる最深部**で、§4 全体で最も「instance を sorry で埋める」誘惑が強い。
**N-4 を最優先 genuine 実装**。(a)-1 の Γ↔R-内部 変換も忘れず橋を架ける。

---

## 5. Thm 4.16 (Blackburn) — §4 apex

mmd: **L1636-1704** (PDF p.40)。statement の (1)(2) は mmd 抽出で欠落 → **PDF 原文から復元**:

> `p` 奇素数, `R` 非自明 `p`-群, `A` を `R` の p′-自己同型群, `r(R)≤2`, `[R,A]=R`,
> `|A|` odd ⇒ **`p>3`** かつ `R` は次のいずれか:
> - **(1)** `R` is abelian, **or**
> - **(2)** `R = R₁∘R₂` (central product) — `R₁` は **order p³ の nonabelian exponent-p 群**,
>   `R₂` は **cyclic** で `Ω₁(R₂)=R₁'`。

### 5.1 提案 Lean signature

```lean
/-- **BG Theorem 4.16** (Blackburn). `p` 奇素数, `R` 非自明 `p`-群,
`A` 作用 (`φ : A →* MulAut R`), `r(R)≤2` (`pRank R p ≤ 2`), `[R,A]=R`
(`actionCommutator φ = ⊤`), `|A|` odd ⇒ `p>3` かつ (1) `R` abelian, または
(2) `R = R₁∘R₂` (central product, `R₁` order-p³ exp-p extraspecial, `R₂` cyclic, `Ω₁(R₂)=R₁'`). -/
theorem blackburn_rank_two_classification
    {R : Type*} [Group R] [Finite R] [Nontrivial R] {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    (hR : IsPGroup p R)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R)) (hAodd : Odd (Nat.card A))
    (hrank : OddOrder.GroupTheory.pRank R p ≤ 2)
    (hRA : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤) :
    3 < p ∧
      (IsMulCommutative R ∨
       ∃ (R₁ R₂ : Subgroup R),
         OddOrder.GroupTheory.IsCentralProduct R₁ R₂ ∧
         OddOrder.GroupTheory.IsExpPExtraspecial p R₁ ∧ Nat.card R₁ = p ^ 3 ∧
         IsCyclic R₂ ∧ Omega R p 1 ⊓ R₂ = ⁅R₁, R₁⁆)   -- Ω₁(R₂) = R₁'
```
**設計判断**: `Ω₁(R₂)=R₁'` の表現は `Omega (R₂ subtype) p 1 = (commutator R₁).comap ...` でも
よいが、ambient `R` 内の subgroup 等式で書くのが扱いやすい。最終形は実装時に詰める
(scaffold-trap: ここを `True` で誤魔化さない)。

### 5.2 proof skeleton (mmd L1638-1704)

帰納 `|R|`。
* **(L1638) 準備**: `r(R)≤2` ⇒ `SCN₃(R)=∅` (**exists** `scn3_empty_of_pRank_le_two`)。
  各 `|A|` 素因子 odd。Lem 4.13 で `p>3`。→ **Lem 4.13 (N-5/N-6)** 必須。
* **(L1638) Case A: `|Ω₁(R)|≤p²`**: Prop 4.11 で `R` metacyclic, Thm 4.12(a) + `[R,A]=R` で
  `R` abelian → **(1)**。→ **Prop 4.11 (§3) + Thm 4.12 (§4)** 必須。
* **(L1640-) Case B: `|Ω₁(R)|>p²`**: Prop 4.8 で `S:=Ω₁(R)` exp p, order p³。`r(R)=2` ⇒ `S`
  非 abelian ⇒ `S` extraspecial。`C:=C_R(S)`。(4.11) `S'⊆Ω₁(C)⊆S∩C=Z(S)=S'` ⇒ `|Ω₁(C)|=p`
  ⇒ Lem 4.5 で `C` cyclic。→ **Prop 4.8 (N-5) + Lem 4.5(b) + extraspecial 判定**。
  * **(L1648-1652) B-1: `R` が `S/S'` を中心化** ⇒ Lem 4.15 で `R=CS=SC`。`C` cyclic,
    `Ω₁(C)=S'` ⇒ **(2)** (`R₁=S`, `R₂=C`)。→ **Lem 4.15 (N-5) + N-2 (central product)**。
  * **(L1654-1704) B-2: `R` が `S/S'` を非中心化** ⇒ `T:=[R,S]`, `S'⊂T⊂S`, `|T|=p²`。
    `|R/C_R(T)|=p`, `R=S·C_R(T)` (4.12)。`C_R(T)/C` elem ab p-群 (4.13/4.14)。Maschke で
    `TC/C` の A-invariant complement `X/C` ⇒ `X=⟨x⟩` cyclic。`R=SX`, `[X,S]⊄S'` (4.15)。
    **GL(2,p) 合同で矛盾** (下記 §5.3) ⇒ **B-2 は起きない**。

### 5.3 ⭐ GL(2,p) 合同矛盾 (mmd L1684-1704) — 本書の SPECIAL ATTENTION 焦点

**結論を先に**: この矛盾は **純 `ZMod p` 算術**であり、
`isPGroup_commutator_of_faithful_two_dim_charP` を **経由しない**。
`|GL(2,p)|=p(p²-1)(p-1)` (L1658) は **`|R/C_R(T)|=p` の動機付けにのみ**使われ、矛盾本体は
整数 `i,j,k ∈ (ZMod p)ˣ`/`ZMod p` の合同式で閉じる。

**設計 (B-2 矛盾の Lean 化)**:
1. `S/T ≅ Fₚ` (位数 p), `T/S' ≅ Fₚ`, `S' ≅ Fₚ` (S extraspecial, exp p)。
   生成元 `y∈S∖T`, `z∈T∖S'`, `x` (X=⟨x⟩ の生成元)。
2. `[R,A]=R` & (4.12) ⇒ `[S,A]⊄T` ⇒ ∃ `α∈A` で `[S,α]⊄T`。整数 `i,j,k`:
   `x^α=xⁱ`, `y^α≡yʲ (mod T)`, `z^α≡zᵏ (mod S')` (mmd L1686)。
3. **`j²≢1 (mod p)`** (L1690-1692): `α` odd order ⇒ `α²` が `S/T≅Fₚ` に非自明作用
   ⇒ `j² ≢ 1`。
   → Lean: `α` の位数が奇 ⇒ `j` (∈ `(ZMod p)ˣ`) の位数が奇 & ≠1 の作用 ⇒ `j²≠1`。
   **`y^{α²}≡y^{j²} (mod T)`** (L1688) と `α²` 非自明から。
4. `i≢0` (L1694): `⟨xⁱ⟩=⟨x^α⟩=⟨x⟩` ⇒ `i∈(ZMod p)ˣ`。
5. **Lem 4.2 を 2 回適用** (L1696-1700):
   `[y,z]ⁱ=[y,z]^α=[y^α,z^α]=[yʲ,zᵏ]=[y,z]^{jk}` ⇒ **`jk≡i (mod p)`** (∵ `[y,z]∈S'≅Fₚ` 位数 p)。
   `[x,y]ᵏ≡[x,y]^α≡[x^α,y^α]≡[xⁱ,yʲ]≡[x,y]^{ij} (mod S')` ⇒ **`ij≡k (mod p)`**
   (∵ `[x,y]∈T∖S'`, `T/S'≅Fₚ`)。
   → Lean: **repo 既存 `commutatorElement_pow_left/right_of_central`** (S' 中心化 ∵ `[R,T]⊆S'`)。
6. **合同連鎖** (L1702): `jk≡i`, `ij≡k` ⇒ `ij²≡jk≡i` (j を ij≡k に掛ける) ⇒ `i(j²-1)≡0`。
   `i∈(ZMod p)ˣ` ⇒ **`j²≡1`**。step 3 の `j²≢1` と矛盾 ✗。
   → Lean: `ZMod p` で `i*(j^2-1)=0` & `IsUnit i` ⇒ `j^2-1=0` ⇒ `j^2=1`。`omega`/`field_simp`
     ではなく `ZMod p` (= 体, p 素数) の `mul_eq_zero` + `IsUnit.ne_zero` で。

**マッピングの設計判断 (SPECIAL ATTENTION への回答)**:
- ⭐ **j²≡1 vs j²≢1 は fresh ZMod p 算術**。`isPGroup_commutator_of_faithful_two_dim_charP` には
  **routing しない**。後者は (a)-Case や Lem 4.17 の「`A/C` が `V` に faithful ⇒ `(A/C)'` p-群」
  用エンジンで、Thm 4.16 published proof の B-2 矛盾とは別物。**両者を混同するのが scaffold-trap**
  (「エンジンで B-2 を閉じる」と書くと、実際には閉じない論理を仮定してしまう)。
- B-2 で実際に要るのは: (i) `S/T`, `T/S'`, `S'` を `ZMod p` と同定する **Fₚ-同定補題**
  (extraspecial exp-p の構造、N-3 周辺)、(ii) repo Lem 4.2 の commutator 計算、(iii) `α` の作用を
  `ZMod p` の単元 `i,j,k` に落とす **operator-on-Fₚ-section** (N-4 の特殊形)、(iv) `j²≠1` を
  `α²|_{S/T}` 非自明から出す **odd-order ⇒ no involution in (ZMod p)ˣ-action**。
- `|GL(2,p)|=p(p²-1)(p-1)`: **`Matrix.card_GL_field` で計算可能だが Thm 4.16 本体では数値は不要**
  (B-2 を消すのに `|GL(2,p)|` の素因数分解は使わない; 使うのは `j²≡1` 合同のみ)。`|R/C_R(T)|=p`
  (4.12) は `T⊴R`, `T⊄Z(S)`, `|Aut T|` の p-part が p であること経由だが、これは **Aut(Eₚ²)≅GL(2,p)
  橋 (N-6) + `|GL(2,p)|_p=p`** で出す。→ 4.12 (L1658-1660) には N-6 が要る、B-2 矛盾 (L1696-1702)
  には要らない、と **使用箇所を分離**せよ。

### 5.4 依存表 (Thm 4.16)

| step | 依存 | 状態 |
|---|---|---|
| 準備 | `SCN₃=∅` from `r≤2` | **exists** `scn3_empty_of_pRank_le_two` |
| 準備 | Lem 4.13 (`p>3`) | **needs-impl N-5 + N-6** |
| Case A | Prop 4.11 | **needs-impl §3** |
| Case A | Thm 4.12(a) | **needs-impl §4** |
| Case B 準備 | Prop 4.8 (exp p, order p³) | **needs-impl N-5** |
| Case B 準備 | `S` extraspecial 判定 (`r=2` ⇒ S 非 abelian, exp p order p³ ⇒ extraspecial) | **needs-impl** (`IsExtraspecial` 構成) |
| Case B 準備 | Lem 4.5(b) (`C` cyclic) | **needs-impl N-5** |
| B-1 | Lem 4.15 (`[S,R]⊆S' ⇒ R=S·C_R(S)`) | **needs-impl N-5** (Gorenstein 5.4.6) |
| B-1 | `IsCentralProduct` 構成 | **needs-impl N-2** |
| B-2 | `T=[R,S]`, `|T|=p²`, (4.12) | **needs-impl** (nilpotent commutator + N-6) |
| B-2 | `C_R(T)/C` elem ab (4.13/4.14, B の自己同型計算) | **needs-impl** (mmd L1662-1668 の β,γ 計算) |
| B-2 | 商 `C_R(T)/C` への A 作用 + Maschke complement | **needs-impl N-4** ⭐⭐ |
| B-2 | `Ω₁(C_R(T))=T` (`r≤2`) | **needs-impl** (rank 2 ⇒ Ω₁ 同定) |
| B-2 矛盾 | Lem 4.2 (repo), `ZMod p` 算術, Fₚ-section 同定 | **exists (Lem 4.2)** + **needs-impl** (Fₚ 同定, odd⇒j²≠1) |

### 5.5 SCAFFOLD-TRAP AUDIT (Thm 4.16)

| step | genuine か / 罠か | リスク度 |
|---|---|---|
| Case A 全体 | **罠 (上流依存)**: Prop 4.11 + Thm 4.12 を hoist すれば Case A は即。**両者が §3/§4 で未完なら Thm 4.16 も未完**。Case A は「Prop 4.11/Thm 4.12 が sorry-free」を **constructibility で要求**。 | **最高** |
| Case B extraspecial 判定 | genuine だが needs-impl。`IsExtraspecial` の 4 field を `S` で実証 (`Z(S)=S'=Φ(S)`, `|Z(S)|=p`)。罠: `(hSes : IsExtraspecial p S)` で hoist しない。 | 高 |
| (2) central product | **罠**: `IsCentralProduct` (N-2) を弱い `R₁⊔R₂=⊤` で誤魔化すと (2) が偽の弱命題に。`⁅R₁,R₂⁆=⊥` と `Ω₁(R₂)=R₁'` を必ず実証。 | 高 |
| B-2 商作用+Maschke | **最高リスク**。Thm 4.12 a-3 と同じ N-4 罠。`C_R(T)/C` への A 作用を未構成 instance で埋めない。 | **最高** |
| B-2 GL(2,p) 合同 | **genuine, 実証可能**。`ZMod p` 算術 + repo Lem 4.2。**ここは scaffold 不要、Lean で書ける**。ただし **`isPGroup_commutator_...` に誤 routing するな** (§5.3)。Fₚ-section 同定と `j²≠1` (odd) は別途 genuine impl。 | 中 (本体は書ける) |
| 帰納の閉じ方 | genuine。B-2 が矛盾なので Case B では常に B-1 ⇒ (2)。`|R|` 帰納は Case A の R/T や部分群に効く。罠: 帰納仮説の適用先が `r≤2` & `[·,A]=·` を保つか要確認。 | 中 |

**結論 (Thm 4.16)**: 最終 apex なので **上流 (Prop 4.11, Thm 4.12, Prop 4.8, Lem 4.5(b),
4.13, 4.15, N-1〜N-6) が全部 sorry-free でないと本体は scaffold-trap**。本体固有の genuine 中核は
**B-2 の ZMod p 合同矛盾** (repo Lem 4.2 で書ける) と extraspecial/central-product 構成。
**B-2 を `isPGroup_commutator_of_faithful_two_dim_charP` で閉じようとするのは誤設計** — published
proof は純算術で閉じる。

---

## 6. 推奨 sub-issue 分割 + 実装順 + gate

> 原則: **leaf を build-green で回せる単位に切り、hard content を上流 sorry-free 補題に押し下げてから
> apex を組む**。各 issue は 0016/§4 v1 と同型の「逐次 build-green + adversarial verify + 自律 fix」
> workflow。issue 採番は main range (base 0) か、並行なら base 割当 (CLAUDE.md / issue_management)。

### Wave 0 — 新規 API 束 (build-green 単発向き, 相互独立)
- **I-0a `Agemo` (N-1)** — `OmegaSubgroup.lean` に追加。gate: なし。
- **I-0b `IsCentralProduct` (N-2)** — `CentralProduct.lean` 新規。gate: なし。
- **I-0c exp-p extraspecial (N-3)** — `IsExtraspecial.lean` 拡張。gate: なし。
- **I-0d Aut(Eₚⁿ)≅GL(n,p) 橋 (N-6)** — `PRank.lean` の `zmodModule` 上に。gate: なし。
  `Matrix.card_GL_field` で `|GL(2,p)|` 数値も補題化。

### Wave 1 — operator 商作用 (最深ゲート, 設計先行)
- **I-1 商 `R/S` への A 作用 + A-invariant complement (N-4)** ⭐ — **持ち上げ `φ̄` は Ch04 既存**
  (`quotientMulAutHom`, §2 N-4 訂正参照、再実装不可)。残 = **Maschke complement の subgroup 形のみ**
  = [`s04_n4_maschke_bridge_design.md`](s04_n4_maschke_bridge_design.md) (`Ω₁(R/S)` Fₚ-加群化 + mathlib
  Maschke + module↔subgroup 還元, ~5-8 補題)。**Thm 4.12 / 4.16 B-2 の両方が依存** ⇒ 最優先。
- **I-1b Prop 1.6(b) の Γ↔R-内部 変換** ✅ **DONE** (2026-05-30, commit 3641c6a,
  `OperatorQuotientAction.lean` `actionCommutator_restrict_self_eq_top`, sorry-free/axiom-clean)。gate: なし。

### Wave 2 — §4 前提補題 (Prop 4.11/4.12/4.16 が共有)
- **I-2a Prop 4.3(a) cl≤3/p>3** — regular p-group collection (mmd L1410-1472, `(uv)ⁿ`)。
  gate: なし (cl≤2 は repo 既存)。
- **I-2b Lem 4.5(b)(c) + Lem 4.10** — cyclic index p ⇒ `Ω₁≅Eₚ²` (Gorenstein 5.4.3/4.4)。
  gate: I-0a。
- **I-2c Prop 4.8** (`r≤2`+exp p ⇒ `|R|≤p³`, `p>3`⇒Ω₁ exp p)。gate: I-2a, I-2b, I-0d。
- **I-2d Lem 4.9** (`|Ω₁(R/T)|≤p²`)。gate: I-2c。
- **I-2e Lem 4.13/4.14** (q∣|Aut R| ⇒ q∣p²-1, q<p)。gate: I-0d。

### Wave 3 — §3 山 (設計先行, multi-sub)
- **I-3 Prop 4.11 (Huppert)** ⭐ — §3 の skeleton。
  **gate**: I-0a (agemo), I-2b (Lem 4.5(b)), I-2d (Lem 4.9)。
  sub-stage: abelian case / step 7 核 (Lem 4.2 計算) / step 8 cyclic 判定。

### Wave 4 — Thm 4.12 (設計先行)
- **I-4 Thm 4.12(a)(b)(c)** ⭐ — §4 の skeleton。
  **gate**: I-1 (N-4 商作用), I-1b (Prop1.6b 変換), I-2b (Lem 4.10/4.5b), Prop 1.6(d) (既存)。
  sub-stage: (b)(c) (Prop1.6(d) で軽) を先に / (a) (Maschke 段) を後に。

### Wave 5 — Thm 4.16 apex (設計先行, multi-sub)
- **I-5 Thm 4.16 (Blackburn)** ⭐ — §5 の skeleton。
  **gate**: I-3 (Prop 4.11), I-4 (Thm 4.12), I-2c (Prop 4.8), I-2b (Lem 4.5b), I-2e (Lem 4.13),
  Lem 4.15 (Gorenstein 5.4.6, → I-5 内 or 別 issue), I-0b/0c (central product / exp-p), I-1 (N-4)。
  sub-stage: **Case A** / **Case B 準備 (extraspecial+C cyclic)** / **B-1 ⇒ (2)** /
  **B-2 矛盾 (ZMod p 合同, 最も書ける)** を別々に。

### 実装順 (依存最小化)
```
I-0a I-0b I-0c I-0d   (Wave0, 並行可)
   → I-1 I-1b          (Wave1, N-4 最優先)
   → I-2a→I-2b→I-2c→I-2d, I-2e  (Wave2)
   → I-3 (Prop4.11)    (Wave3, gate: I-0a,I-2b,I-2d)
   → I-4 (Thm4.12)     (Wave4, gate: I-1,I-1b,I-2b)
   → I-5 (Thm4.16)     (Wave5, gate: 上記全部 + Lem4.15)
```

---

## 7. 参照パス (絶対)

- **BG §4 原典**: `/home/ywr/odd-order/references/bg/local-analysis.mmd`
  - Prop 4.11 = L1554-1586, Thm 4.12 = L1588-1622, Thm 4.16 = L1636-1704
  - Lem 4.2 = L1389-1394, Prop 4.3 = L1474+(L1387-1472 proof), Lem 4.5 = L1481-1499,
    Prop 4.8 = L1511-1520, Lem 4.9 = L1522-1544, Lem 4.10 = L1546-1552,
    Lem 4.13 = L1624, Lem 4.14 = L1628, Lem 4.15 = L1632
  - central product def = L1377-1381
  - **Thm 4.16 (1)(2) は mmd 抽出欠落** → PDF text (`pdftotext`) L2602-2609 から復元 (本書 §5 冒頭)
- **Gorenstein 行間**: `/home/ywr/odd-order/references/gorenstein/finite-groups.mmd`
  (Lem 4.5 general = 5.4.10, Lem 4.5(b) = 5.4.3/5.4.4, Lem 4.13 = 5.4.15, Lem 4.15 = 5.4.6)
- **既存 S04**: `/home/ywr/odd-order/OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean`
- **operator infra**: `/home/ywr/odd-order/OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`
  (`IsAInvariant` L2894, `fixedPointsOfMulAut` 系), `.../Ch04_Commutators/Main.lean`
  (`actionCommutator` L2006, Prop1.6(a) L2741, Prop1.6(b) L2785, Prop1.6(d) L3386)
- **GroupTheory shared**: `PRank.lean`, `SCN.lean`, `OmegaSubgroup.lean`, `IsMetacyclic.lean`,
  `IsExtraspecial.lean`, `CriticalSubgroup.lean` (`thompson_critical_omega` は `S01_Solvable.lean:845`)
- **Thm 2.6 エンジン**: `/home/ywr/odd-order/OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`
  (`odd_two_dim_sylow_abelian` L4681)
- **mathlib GL card**: `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean:89`
  (`Matrix.card_GL_field`)
- **新規作成先**: `OddOrder/GroupTheory/CentralProduct.lean`, `OmegaSubgroup.lean` (Agemo 追記),
  `IsExtraspecial.lean` (exp-p 追記)
- **上位引き継ぎ**: `/home/ywr/odd-order/notes/bg/s04_thm416_handoff.md`,
  `/home/ywr/odd-order/notes/bg/s04_implementation_plan_2026_05_30.md`

---

## 8. 最重要メッセージ (実装セッションへ)

1. **judge by hypothesis constructibility, not sorry-count**。Prop 4.8 / Lem 4.5 general /
   N-4 (商作用) / N-6 (GL 橋) を仮説に積んだ "sorry-free" は **全部未完**。
2. **N-4 (operator 商作用 + Maschke) が §4 で最深の単一ゲート**。Thm 4.12(a) と Thm 4.16 B-2 が
   両方依存。未構成 `MulAction`/`MulAut` instance を sorry で埋める誘惑が最大。**最優先 genuine 実装**。
3. **Thm 4.16 B-2 の j²≡1 矛盾は純 ZMod p 算術** — `isPGroup_commutator_of_faithful_two_dim_charP`
   に routing しない。repo Lem 4.2 (`commutatorElement_pow_*_of_central`) で commutator を計算し、
   `ZMod p` の `mul_eq_zero` + `IsUnit i` で閉じる。これは **本体固有の genuine に書ける中核**。
4. **`|GL(2,p)|` 数値は Thm 4.16 本体の矛盾には不要**。Lem 4.13 / Prop 4.8 / (4.12) の
   `|Aut T|_p=p` 出力にのみ N-6 + `Matrix.card_GL_field` が要る。使用箇所を混同しない。
5. **central product (2) は 3 条件 + `Ω₁(R₂)=R₁'` を全部実証**。`R₁⊔R₂=⊤` だけの弱命題にしない。
