# BG §4 precursor(2): minimal ψ-invariant ⇒ special exp p (Gorenstein Thm 3.7/3.8/3.10)

> 2026-05-31 作成。precursor(1) `pRank_le_two_of_scn3_empty` (= G Thm 4.15(i)) 完成 (commit c1d23e8)
> 後の次ゲート。**BG Lem 4.13 (= G Thm 4.15(ii), q∣p²-1) の本体入力**。設計ノート、cold-start
> でここから着手可能。⚠ **これは 【大】 — 複数セッション規模** (coprime-action 構造論を §3.6-3.10 で要構築)。

## ゴール (precursor 2)

BG Lem 4.13 の証明 (G Thm 4.15(ii)) で使う:
> `D` = `A`-invariant subgroup of minimal order on which `ψ` (prime order `q≠p` の元) acts
> nontrivially ⇒ **`D` は special `p`-group of exponent `p`** (`p` odd)。

これは **Gorenstein Thm 3.8** (special 部分群の存在 = minimal ψ-inv に Thm 3.7 適用) +
**exponent p** 部分 (Thm 3.10 の Ω₁ 論法、`p` odd) の合わせ技。

目標署名 (案):
```lean
-- D = minimal A-invariant on which ψ acts nontrivially (ψ ∈ A*, A p'-group, p odd)
-- ⇒ IsSpecial p ↥D ∧ Monoid.exponent ↥D = p
theorem isSpecial_expP_of_minimal_pprime_action ... : IsSpecial p D ∧ ...
```
`IsSpecial` は `OddOrder/GroupTheory/IsExtraspecial.lean` に定義済 (commit, 2026-05-31)。

## 依存ツリー (Gorenstein 番号、mmd = `references/gorenstein/finite-groups.mmd`)

```
precursor(2): minimal ψ-inv ⇒ special exp p
 ├─ G Thm 3.8 (minimal A-inv on which ψ nontrivial ⇒ special, A irred on Q/Φ(Q))   ← G L3870
 │   └─ G Thm 3.7 (ψ trivial on every proper A-inv normal ⇒ P'⊆Z, P/P' elem ab irred, special)  ← G L3812 【核・大】
 │       ├─ (ii) P/P' elem ab + A irreducible + ψ nontrivial:
 │       │   ├─ A indecomposable on P̄=P/P' (easy: 分解 ⇒ ψ trivial on each ⇒ 矛盾)
 │       │   ├─ 🔴 **G Thm 2.2 (indecomposable A-action on abelian p ⇒ homocyclic)**  ← MISSING
 │       │   ├─ 🔴 **G Thm 2.4 (Ω₁(P̄)=P̄ 経由 elem ab、coprime Ω₁-extension)**       ← MISSING
 │       │   └─ Maschke (indecomposable ⇒ irreducible, elem ab) ✅ Thm 1.20
 │       ├─ (i) P'⊆Z(P): [P,B]=P (B=⟨ψ^A⟩ normal closure) + three-subgroups lemma ✅
 │       │   └─ [P,B]=P は (ii) の irreducibility に依存 (B centralizes P', H=[P,B]⊄P' via Thm 3.6)
 │       ├─ 🔴 **G Thm 3.6 ([P,A,A]=[P,A]; =1 ⇒ A=1)**  ← assemblable (下記), NOT present
 │       │   └─ P=C_P(A)·[P,A] ✅ `fixedPoints_sup_actionCommutator_eq_top`@Ch04:2741 (両 P, H=[P,A] に適用)
 │       └─ (iii) special structure: (i)(ii) + Lem 2.2.2 commutator-power + p odd
 └─ exponent p 部分:
     ├─ Ω₁(D)=D: Ω₁(D)⊊D なら ψ trivial on Ω₁(D) (proper A-inv) ⇒ Thm 3.10 で ψ trivial on D 矛盾
     ├─ G Thm 3.10 (p odd, p'-aut が Ω₁(P) 上自明 ⇒ aut=1)  ← G L3920 【大】
     │   ├─ Thm 3.7 (induction で proper subgroup 上 A trivial ⇒ P special)
     │   ├─ Lem 3.9 ((xy)^p=x^p y^p for cl≤2 ∧ P/Z elem ab, p odd; Ω₁ exp p)  ← 部分的に present
     │   │   (S04d `Omega.exponent_eq_of_class_le_two` 系 + `mul_pow_prime_eq_one_of_class_le_two`)
     │   └─ Thm 3.2 (coprime stabilizes normal series ⇒ trivial) ✅ `actionCommutator_eq_bot_iff_acts_trivially`@Ch04:2184
     └─ G Thm 3.6 (上)
```

## present vs MISSING (repo survey 2026-05-31)

**present ✅** (Isaacs Ch04 §4D coprime-action が厚い):
- `fixedPoints_sup_actionCommutator_eq_top`@Ch04:2741 — **P = C_P(A)·[P,A]** (Thm 2.2.1 系、Thm 3.6 の核)
- `actionCommutator_eq_bot_iff_acts_trivially`@Ch04:2184 — **stabilizes ⇒ trivial** (Thm 3.2)
- `fixedPoints_inf_actionCommutator_eq_bot_of_abelian`@Ch04:3396、`actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime`@Ch04:3932 ほか coprime 多数
- Maschke (Thm 1.20)、three-subgroups (`commutator_commutator_le_of_rotate`@Ch04:1535)
- Lem 3.9 系 (class≤2 odd ⇒ Ω₁ exp p): S04d `Omega.exponent_eq_of_class_le_two` / `mul_pow_prime_eq_one_of_class_le_two`
- `IsSpecial` def ✅ (IsExtraspecial.lean)

**着地済 ✅ (2026-05-31)**:
- **G Thm 2.4** (Ω₁-extension) = `actionCommutator_eq_bot_of_omega1_le_fixedPoints`@`GroupTheory/CoprimeAbelianPGroup.lean` (commit a2780ec, sorry-free)。**判明: Thm 2.2 に依存しない** — Thm 2.3 (`G=C×[G,A]`、既存 `fixedPoints_inf_actionCommutator_eq_bot_of_abelian`) + Cauchy のみで完結。`IsSpecial` def も着地 (IsExtraspecial.lean)。

**MISSING 🔴** (precursor(2) の残る壁):
- **G Thm 2.2** — A が abelian p-群に indecomposable に作用 ⇒ homocyclic。**最難**。要 Lemma 2.1 (非 homocyclic abelian の agemo `℧ⁿ⁻¹` / Ω₁ 構造、基底・type 論) + Thm 3.3.2 (elem ab の A-不変 direct factor に A-不変補空間 = coprime Maschke; repo の N-4 Maschke bridge `exists_aInvariant_complement_in_omega1_quotient` が近い)。`Agemo`@OmegaSubgroup あり。
- **G Thm 3.6** — `[P,A,A]=[P,A]`。present infra から assemblable だが未着地。
- **G Thm 3.7/3.8/3.10** 本体。

## 実装順 (推奨, 下層から; 各 leaf = 別 bg-prove ターゲット可)

1. **G Thm 3.6** `actionCommutator_actionCommutator_eq_actionCommutator` (`[P,A,A]=[P,A]`): present `fixedPoints_sup_actionCommutator_eq_top` を P と A-invariant `H=[P,A]` に適用 (H への作用制限が plumbing)。**最も tractable な leaf、独立着手推奨**。
2. ✅ **G Thm 2.4** (coprime Ω₁-extension) — 着地済 (`CoprimeAbelianPGroup.lean`, commit a2780ec)。
3. **G Thm 2.2** (indecomposable ⇒ homocyclic): 表現論寄り、**最難・次ターゲット**。要 Lemma 2.1 + Thm 3.3.2 (coprime Maschke on elem ab)。
4. **G Thm 3.7** (核): 1-3 + Maschke + three-subgroups で (i)(ii)(iii) を assemble。
5. **G Thm 3.8** (minimal ⇒ special): Thm 3.7 を minimal A-inv subgroup に適用。
6. **G Thm 3.10** (Ω₁ 上自明 ⇒ trivial, p odd): Thm 3.7 + Lem 3.9 + Thm 3.2 + 帰納。
7. **precursor(2)** `isSpecial_expP_of_minimal_pprime_action`: Thm 3.8 + exp-p 論法 (Ω₁(D)=D via 3.10)。

## anti-scaffold 注意

- ⚠ `thompson_critical_omega`@S01:845 は **別物** (G 5.3.9/5.3.10 = characteristic critical subgroup、NOT minimal-ψ-inv-special)。流用不可。
- Thm 3.6/3.7 の「A-invariant subgroup H への作用制限」を未構成 instance に hoist しない (Ch04 の制限作用 API を使う)。
- Thm 2.2 (homocyclic) を仮定フィールドに逃がさない (これが本当の payload の一つ)。
- exp-p の「Ω₁(D)=D」を仮定に積まない (minimality + Thm 3.10 から genuine に出す)。

## G Thm 2.2 (indecomposable ⇒ homocyclic) — proof architecture (2026-05-31 調査確定)

Gorenstein 原文 = `references/gorenstein/finite-groups.mmd` **L3696-3757** (Ch.3 §2)。完全な攻略図:

**必要な部品 (順に):**
1. **`IsHomocyclic p G` def** (新規, 未着地)。clean な特徴付け = exp `p^n` の abelian p-群で
   **`Agemo G p (n-1) = Omega G p 1`** (⟺ Gorenstein の `r=m`; ℧ⁿ⁻¹⊆Ω₁ は常に成立、等号⟺homocyclic)。
   `Agemo`@OmegaSubgroup あり。n-1 を避けるなら exp で parametrize。
2. **Thm 3.3.2 (coprime Maschke on elem ab)** = `OperatorMaschke.exists_aInvariant_complement_in_omega1_quotient`
   から **R/S quotient 層を外した一般形**: 「elem ab `G`, `φ:A→*MulAut G` coprime, `W≤G` A-不変
   ⇒ A-不変 complement `X` (`X⊓W=⊥`, `X⊔W=⊤`)」。証明構造は OperatorMaschke L172-254 と同型
   (zmodModule → ρ=`mulAutToEnd G p ∘ φ` → `pW` invtSubmodule → `ComplementedLattice.exists_isCompl`
   → `Φ=(toZModSubmodule).symm.trans toSubgroup'` で subgroup 復元)。**quotient lift (L255-277) は不要**で
   むしろ短い。⚠ **layering**: `mulAutToEnd` は BG (AppA/OperatorMaschke) にしかない。Thm 3.3.2 を
   GroupTheory に置くなら `mulAutToEnd` を GroupTheory へ移し OperatorMaschke を consumer 化するのが
   筋 (将来 refactor)。当面は **BG 配下** (OperatorMaschke downstream) に置けば再利用可。Lemma 2.1 が 2 回使う。
3. **Lemma 2.1** (L3706): 非 homocyclic abelian `P` (exp `p^n`, `X=℧ⁿ⁻¹(P)`) に対し
   (i) A-不変 `T≠1` で `T∩X=1` (Ω₁(P)=X×T を Thm 3.3.2 で分解); (ii) `T∩X=1` ⇒ `P/T` exp `p^n`
   かつ `℧ⁿ⁻¹(P/T)=X̄`。**要: 有限 abelian p-群の基底・type 論** (mathlib の有限 abelian 分類
   `Mathlib.Algebra.Group.FiniteAbelian` 系 — 基底 `{xᵢ}` orders `pⁿⁱ`, `yᵢ=xᵢ^(pⁿⁱ⁻¹)`, `r=#{nᵢ=n}`)。
   repo に基底抽出の bridge 無し = **重い新規インフラ**。
4. **Thm 2.2** (L3715): `T`=maximal A-不変 disjoint from `X` (`Finite.exists_maximal`) → `P/T` homocyclic
   (Lemma 2.1 反復) → `Q=⟨xᵢ:i≤r⟩` で `P=T×Q` → Thm 3.3.2 で `P=T×R` (`R≠1`) ⇒ indecomposable 矛盾。

**規模**: Thm 3.3.2 ~80行 (OperatorMaschke 流用), Lemma 2.1 ~重 (基底論), Thm 2.2 ~中。
**= dedicated session 推奨** (precursor(1) と違い repo に無い有限 abelian 構造論を建てる)。
着手は Thm 3.3.2 (再利用効くし最も決定的) または `IsHomocyclic` def から。

## 参照パス

- BG: `references/bg/local-analysis.mmd` L1624-1628 (Lem 4.13/4.14)
- Gorenstein: `references/gorenstein/finite-groups.mmd` — Thm 3.6 L3826, Thm 3.7 L3812, Thm 3.8 L3870, Lem 3.9 L3898, Thm 3.10 L3920, Thm 2.2/2.4 (§2、要 locate)
- precursor(1) (完成、隣接技法): commit c1d23e8 `S04d_GorThm415.lean`
- present coprime infra: `OddOrder/Isaacs/Ch04_Commutators/Main.lean` §4D
- tracker: issue 0051 / `notes/bg/autonomous_prove_queue.md` (#9 系)
