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

- [x] **SkewPair 定義と点関係式 (P)** (2026-08-13, commit 5ae0afa81)。**設計変更**:
      layer (1,2) でなく **(0,1) で構築** — `SkewPair data e A B X Y` =
      `a(Aw)·b(Xw^e)·a(Bw)⁻¹ = b(Yw^e)` (∀w 非零平方)。点関係式は既存
      `layerFieldHom_two_factor` (relation (2)) をそのまま使い、閉 loop が置換
      `v := Aw` だけで標準 `ConjPair` になる (g-共役の層シフト不要)。
- [x] **skew 辺 (E(p,r))**: `skewPair_edge` (two_factor 2 本の第 3 層消去) +
      非退化 `skewPair_edge_left_ne_zero` / `skewPair_edge_weight_ne_zero`。
- [x] **反転・再スケール・合成**: `SkewPair.rev`/`rescale`/`comp` +
      `self_symm`/graph property (`self_left_eq_zero`/`self_right_eq_zero`)。
      swap 辺は独立補題不要 (= `skewPair_edge` を (r,p) 順で適用するだけ)。
- [x] **閉条件 (設計変更: 一般 k-連鎖理論は作らない)**: endgame が使う loop は
      同 slot 2-loop・fwd-fwd 2-loop・可換子 4-loop のみなので、各 loop を
      rescale+comp の直接合成で組む。一般の「t-逐次決定・∏B = ∏A 帰納」は不要
      (共謀仮定は具体 loop ごとに contrapositive で使われる)。
- [x] **loop ⟹ kill**: `false_of_skewPair_self_frobenius_family` — 閉 loop の
      Frobenius 族 (重み非零) → χ(A) 分岐 (向きは cube 不変で族一様) →
      `conjPair_of_self`/`conjPair_of_self_neg` → `false_of_conjPair_frobenius_family`。
- [x] **同 slot 2-loop ⟹ κ-定数** (commit 204fd6c5c): `false_of_proportional_edges` +
      `weights_proportional_of_proportional_edges` (K(p) = K(p')s^e ∧ K(r) = K(r')s^e、
      除算なし multiplied-out 形; loop 族は `paley_frobenius_iterate` で供給)。
- [x] **FrobFam 層 + 4-loop raw 形 + leg supply** (2026-08-13, commits 79281f7db/fbbcd575a):
      `FrobFam` (Frobenius 閉族) の edge/rev/comp/rescale/false_of_self で per-j
      boilerplate を集約 (既存 2 lemma を書き換え、statement 不変)。
      `false_of_four_loop`/`weights_eq_zero_of_four_loop` (endpoint 共有形の 4 脚 loop =
      (EX) の raw 形)。`FrobFam.leg_fwd`/`leg_swap` (任意高さ h からの class leg、
      per-leg slot 表の E/Ē 選択を符号仮定で解決)。
- [x] **step 4 (singleton {−1})** (commit 7a72905eb, 新 leaf
      `AppC_Problem1SkewEndgame.lean`): `false_of_three_antipodal` — 3 点の全対 ρ = −1
      ⟹ K ≡ 0 ⟹ 矛盾。
- [x] **可換子 loop ⟹ (EX)** (2026-08-13, commit 9227ed108): `legWeight` +
      `FrobFam.leg_resolved` (E/Ē 分岐を 1 補題に封じた Bool セクター統一 leg) +
      `exchange_relation` — v = δ₀ 正規化の可換子 loop で共謀 ⟹ 重み両成分消滅。
      8 セクターを 1 statement (Bool b₂b₃b₄ + cond 平方類仮定)。証明は分岐なし
      (leg_resolved ×3 + 高さ整合 field_simp ×2 + 4-loop lemma)。逆成分 c₁ = −χ(δ₀)
      の (EX) は swap 対 (r,p) への適用で得る設計。
- [ ] **(EX) ⟹ master formula (anchor 論法)**: resolution.md §4.3 の人口場合分け
      (χ=+1 anchor / 全 −1 で 2 クラス以上 / 単集合 {ρ₀≠±1} は全射性、{−1} は
      step 4 済)。λ± を anchor 対の K から定義し、各対の master 等式を
      exchange_relation + κ-constancy (weights_proportional) で pin する。
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
