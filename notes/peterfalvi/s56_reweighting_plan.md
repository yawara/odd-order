# (5.6) norm-weighted reweighting — multi-session plan (endpoint A 完遂)

**着手**: 2026-06-16 (lane-b session 43 cont.²⁹) / ユーザー裁可「(5.6) reweighting 着手」(cont.²⁸ fork)
**目的**: case-B (6.8.3) を closえる。ChatGPT (Pro 拡張) 検証で確定: case-B は reducible column を含む S₁ に
(5.6) を適用、‖χ‖²-weighted 和が必須、sidestep 無し ([[s08_6_8_3_reducibleS_chatgpt_answer]])。
**正本の数学**: notes/peterfalvi/s08_6_8_3_reducibleS_chatgpt_answer.md (Q1-Q4、(5.6) 正確な形 + 証明構造)。

## 🎯 decisive scoping 発見 (cont.²⁹、計画の根拠)

**S07 の (5.6) core 機構は既に general / norm-agnostic** — 恐れた「S07 書き直し」は不要の見込み:
- `CharacterPsiDecomposition τ χ ψ` (S07:1110) = 抽象 decomposition (一般 χ, ψ, X, Y)。inner-product lemma 群
  (inner_X_eq_coeff/inner_self_X/inner_self_chi_add_psi_eq 等) は norm-1 非依存。
- (5.6.2) opening bound `inner_self_Y_re_le_inner_self_psi` (S07:1444) = 一般 ψ、`‖χ‖²+‖ψ‖²=‖X‖²+‖Y‖²` +
  (5.4.a) `‖χ‖²≤‖X‖²` のみ使用、**norm-1 仮定なし**。docstring「Stated for the general ψ」「‖Y‖²≤a²‖χ₁‖²」(‖χ₁‖² 明示)。
- (5.6.2) integer-forcing core `int_eq_zero_of_sq_mul_le_of_two_mul_lt` (S07:1780) = `D a z : ℚ` を**抽象に取る**
  (`2a<D ⟹ λ=0`)。D = ∑ aᵢ²/‖χᵢ‖² でも ∑ aᵢ² でも通る。**norm-weighting 非依存**。

⟹ **norm-1/irreducible/Frobenius 仮定の所在 (要 trace・generalize)**:
- **(a) S08 contrapositive `sMember_degreeSumBound_of_not_coherent` (S08_CoherenceCorePart2:2650)**:
  `hF : IsFrobeniusGroup` を取り、結論で S₁ を `χmem : Fin k → IrreducibleCharacter ↥L` 列挙 (‖χ‖²=1 implicit、
  bound = ∑ χmem(1)²、denominator 無し)。**最大の generalize 対象**。`sMember_degreeSqReBound_of_not_coherent`
  (`.re^2` 版) も同様。
- **(b) forward (5.6) union 定理の bound interface** (要精査・次タスク): degree-ratio bound が ∑ aᵢ² (norm-1) か
  ∑ aᵢ²/‖χᵢ‖² (general) か。core が抽象 D ゆえ general 化は容易のはず。(6.6) application (case-A) は ∑ χⱼ(1)²
  (norm-1) を渡す (S07:1818 note) が、これは application 選択であって定理の制約とは限らない。
- **(c) Hyp (5.2) / R(χ) data の case-B 確立 = (5.3.b)**: certain-type で R(μ_j)=ω_ij^σ。**構築済 σ-isometry に接続**
  ((3.x) sessions 13-19、`dadeOrthonormalCharacterImageFamily` / signed family)。これが概念的に最も新規だが
  σ-data は既存。

## ▶ 次タスク (build order、未確定部は ⚠)

1. ⚠ **scoping 完了**: forward (5.6) union 定理 (S07、`coherentUnion`/`coherentPairChain`/retarget 系) の bound
   hypothesis 形を確認。一般 D を取るなら (b) は無改修。S08 (a) だけが本体。**次セッション第一手**。
2. **(a) S08 contrapositive の norm-weighted 版を追加実装**: `sMember_degreeSqNormBound_of_not_coherent` (新名)、
   `hF` 落とし、結論を一般 character family + bound = ∑ χ(1)²/‖χ‖² に。既約版は特殊化として保持 (case-A 無傷)。
   ⟹ これが `2ψ(1)η₁(1) ≥ ∑_{S₁} χ(1)²/‖χ‖²` を case-B に与える。
3. **(c) case-B の Hyp (5.2) 確立 ((5.3.b))**: S = induced char 集合に対し R(μ_j)=ω_ij^σ で coherence axiom。
   構築済 σ-isometry / signed family から。⚠ 最も精査要 (§5 Hyp 5.2 の Lean encoding ↔ σ-data の対応)。
4. **case-B (6.8.3) L4 assembly**: 上記 + FPF tower (cont.²⁶、`false_of_w2_break_arith` 系) + (5.6) X-sum identity
   (mixed X、`∑_X χ(1)²/‖χ‖²=|W₁||H:Z|(|Z|-1)`) → `false_of_coherentXunionYset_caseB_of_not_coherentS` →
   capstone `sibleySetup_is_coherent` の case-B branch。

## 設計原則
- **additive**: 既約版 (`sMember_degreeSumBound_of_not_coherent` 等) は case-A が使う → 削除せず保持。
  norm-weighted 版を**追加**し、既約版をその特殊化に (可能なら) するか並置。
- **build-green + axiom-clean / commit per piece**。core (S07/S08 CorePart) 触る commit は full build。
- **(5.6) 正確な数学は chatgpt_answer.md Q1-Q4 が正本** (射影係数 1/‖χᵢ‖²、quadratic `λ²∑(aᵢ²/‖χᵢ‖²)−2aλ+‖Z‖²≤0`、
  `b=2a/∑(aᵢ²/‖χᵢ‖²)`、(5.4)(5.5) で τ₂ 等長)。

**正本=本ファイル + chatgpt_answer.md。S07 core は norm-agnostic 判明、reweighting は S08 application 層 (a)+(c) が本体。
次=forward (5.6) bound 形の scoping → S08 norm-weighted 版追加。**
