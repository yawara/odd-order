---
id: 181
slug: skew-calculus-lean-formalization
title: "skew calculus と endgame の Lean 形式化 (Problem 1 解決の機械検証)"
created: 2026-08-13
---

# skew calculus と endgame の Lean 形式化 (Problem 1 解決の機械検証)

## 背景

BG App.C Problem 1 (Péterfalvi 1993) は 2026-08-13 に**紙上で否定的に全面解決**した
(敵対的検証 6 本全 CONFIRMED・fatal 0)。正本 =
[`notes/bg/appC_problem1_skew_calculus.md`](../notes/bg/appC_problem1_skew_calculus.md) §6.2 +
[`notes/bg/appC_problem1_pair_composition.md`](../notes/bg/appC_problem1_pair_composition.md) §9、
統合証明文書 = `notes/bg/appC_problem1_resolution.md`。
Part I ((B2)-elim = 衝突 1 個で witness 排除) は **Lean 化済・axiom-clean**。
Part II (skew calculus)・Part III (endgame) は紙上のみ。本 issue はその機械検証。

**merge 済の入口** (すべて axiom-clean・AxiomsCheck 登録済):
`false_of_collisionPair` / `false_of_conjPair_frobenius_family` /
`conjPair_aeval_of_frobenius_family` / `ConjPair.chain` /
`OddOrder/Algebra/FrobeniusCyclicModule.lean` 一式 /
`exists_paley_collision_pow_mul_down` / `false_of_conjPair_self`。

## やること (上流から)

- [ ] **SkewPair 定義と点関係式 (P)**: `SkewPair data e A B X Y : Prop :=
      ∀z ∈ U 版の b(Az^e)d(Xz^{e²})b(−Bz^e) = d(Yz^{e²})`。(P) = `a(z) = b(−p^ez^e)
      d(K(p)z^{e²}) b((p−1)^ez^e)` を `layered_relation_field` から (新 leaf
      `AppC_Problem1SkewCalculus.lean`; 既存 ConjPair 系のイディオム流用)。
- [ ] **skew 辺 (E(p,r))**: (P) 2 本の等置。`p, r ∈ T` の encode は
      `paleySet`/`normOneUnits` の既存 glue に合わせる。
- [ ] **反転・swap・再スケール・合成**: rev = 群逆元 / swap = (r,p)-辺 /
      `z ↦ tz` (t ∈ U) / 内側 b 相殺の合成補題。
- [ ] **閉条件**: t-逐次決定と `∏B = ∏A` ⟺ 閉じ (符号条件込み)。有限列上の帰納。
- [ ] **loop ⟹ kill**: 片側零 ⟹ 層単射で矛盾 / 両側非零 ⟹ χ(A) 分岐 +
      g-共役の層シフト (`g·layer_{i+1}(x)·g⁻¹ = layer_i(x)`、`conjGen_pow_three`) ⟹
      `ConjPair` ⟹ cube-loop で Frobenius 族 ⟹ `false_of_conjPair_frobenius_family`。
- [ ] **同 slot 2-loop ⟹ κ-定数** と **可換子 loop ⟹ (EX)** (全 4 符号セクター;
      per-leg slot 表は resolution.md の表を写す)。
- [ ] **(EX) ⟹ master formula** (anchor 論法; 退化人口: singleton {−1} は
      fwd-fwd 2-loop `e∘swap(e)` の別補題、singleton {ρ≠±1} は master 全射性)。
- [ ] **枝撃破**: Δ=0 (3 点矛盾) / Σ̄=0 (K 定数 ⟹ e²-衝突 glue、下記) /
      Frobenius 量子化 λ∈𝔽₃ (μ-解析 + gcd(3e,Q−1)=1 の単射性) /
      𝔽₃ 残 4 候補 (候補依存の致死パターン + e-冪単射性の out-degree 論法)。
- [ ] **Σ̄=0 glue の 1 補題化** (assembly 監査の nit): K 定数 on T ⟹
      `powDiff (e*e)` が `p−1` 点で衝突 ⟹ `exists_paley_collision_pow_mul_down` ⟹
      `exists_collisionPair_of_sub_ne_zero` (δ≠0 は `pow_injective_of_cube`) ⟹
      `false_of_collisionPair`。
- [ ] **capstone**: `Problem1.false_of_exotic` (仮説 = data + hp + q 素数奇 ≠3 +
      e 奇・cube・hexp のみ、衝突仮定なし) — ケース木全体の組み立て。
      既存 `false_of_centralizing` (定理 1) と合わせ Problem 1 の完全形式化
      `Problem1.hypothesisB_false` を最終形に。
- [ ] AxiomsCheck 登録・`OddOrder.lean` 配線・--strict lint clean を各段で維持。

## 完了条件

`Problem1.false_of_exotic` (無衝突仮定の capstone) が axiom-clean で `lake build` を
通り、AxiomsCheck 登録済であること。歴史的な per-q 証明書群 (trace/N1-N3/剛性) は
supersede されるが削除しない (定理として保持)。

## 参照

- 統合証明文書: `notes/bg/appC_problem1_resolution.md` (本 issue の数学的正本)
- 検証スクリプト: `notes/meta/c/{skew_cycles,endgame_check,lensA_commutator_verify,lensB_verify}.py`
- 関連 commit: bd1873b18 ((B2)-elim) / 9bb4a0b35 (family capstone) /
  793e5800f (e²→e ブリッジ) / 7bde7e759 (endgame closure) / eb2f382ae (assembly 監査)
- [issue 0180](0180-bg-appc-problem1-p-eq-three.md) (親 issue、経緯の全記録)
