# Pf (6.8.3) gap RESOLVED — 正本 (2026-06-17, hub 13-agent workflow + 厳密検証)

> **この note が (6.8.3) / norm-weighted (5.6) / case-B capstone の現時点 source-of-truth。**
> 先行の `s56_reweighting_plan.md`(churn 多・retraction 多)・`s08_6_8_3_reducibleS_chatgpt_answer.md`
> ・`s08_6_8_assembly_plan.md` のうち本 note と矛盾する記述は本 note を優先。
> 検証 = workflow `wf_4810e1ac-022` (Recon 6 + Derive 2 + Verify 5、1.35M tokens) + hub 直接 grep 裏取り。

## 🎯 結論 (一言)

**(6.8.3) の "gap" は数学的に存在しない。** Peterfalvi の Theorem (5.6) は**出版時点で既に norm-weighted**
(仮説 (c) と証明が ‖χᵢ‖² 分母を持つ) で、reducible member は**出版 (5.6) の射程内**。しかも
**その norm-weighted エンジンも、counting 恒等式も、FPF 算術破綻も、repo に既に sorry-free で実装済**。
残るのは **case-B の formalization GLUE のみ** (新数学なし)。両 derivation とも confidence=high・math gap=0、
5 verdict すべて holds=True/high。

⟹ B の session 49 RECON「5 genuine §6 gap、generalized (5.6) は大物」と ChatGPT「(5.6) 一般化は
large undertaking」は **repo 現実に対して過大評価**。真の残務は wiring。

## 1. なぜ「gap でない」か — repo 在庫 (すべて sorry-free, 裏取り済)

| 部品 | repo の場所 | 状態 |
|---|---|---|
| **norm-weighted (5.6) エンジン** | `S08_CoherenceWeighted.lean`: `XAdjoinStepInputW`:56 / `xAdjoinStepW`:286 / **`coherentDegreeSqNormBound_of_not_coherentW`**:475 / `xChainCoherentW`:556 | ✅ 0 sorry |
| (5.6.2) collapse (1/‖χᵢ‖² 分母つき) | `S07_Coherence.lean`: `CharacterPsiDecomposition.Y_collapse_of_family`:5059 / `int_eq_zero_of_sq_mul_le_of_two_mul_lt`:1789 | ✅ |
| (5.4.a) ‖X‖²≥‖χ‖² / (5.4.b) / (5.5) | `S07_Coherence.lean` ~:1351–:1515 | ✅ |
| (5.6.3) τ₂ 拡張 retarget | `S07_Coherence.lean`: `retarget`/`retarget_isCoherent_of_*`:2680/:3262/:3737 | ✅ |
| counting 恒等式 Σ_X χ(1)²/‖χ‖² = \|L:H\|(\|H\|−\|H:Z\|) | `S08_CoherenceCorePart2.lean`: `sum_re_sq_Xset_eq`:2837 / `:2894`; `index_mul_card_sub_factor` | ✅ |
| ‖Ind_H^L θ‖²=[I_G(θ):H] / Σχ(1)²/‖χ‖² | `InducedIrreducible.lean`: `card_mul_inner_self_induce_eq_card_inertia`:172 / `sum_div_normSq_induce_image_eq`:274 | ✅ |
| Cor (2.30) d²≤\|H:Z\| | `θ.isIrreducible.exists_degree_sq_le_index` (S08CP2:3486 で case-A 既使用) | ✅ |
| **case-B FPF 算術破綻** | `S08_CaseBEndgame.lean`: `false_of_w2_break_arith`:49 / `caseB_fpf_bound`:338 / **`false_of_caseB_break_of_bounds`**:384 | ✅ 0 sorry |
| (5.2) carrier / R(χ) / coherence 構造 | `S07_Coherence.lean`: `IsCoherent`:1557 / `S07.Hypothesis`:1665 / `OrthonormalCharacterImageFamily`:766 | ✅ |
| σ-isometry (R(μ_j)=ω_ij^σ) | `S05_SigmaIsometry` ((3.x) sessions 13-19 で構築済) | ✅ |

**⚠ 重要**: 重み付きエンジン (`coherentDegreeSqNormBound_of_not_coherentW`/`xChainCoherentW`) は
**消費者ゼロ** (grep 確認: S08_CaseBEnumeration の docstring 以外に caller なし) =「作られたが capstone に未配線」。

## 2. 数学 — Theorem (5.6) (norm-weighted, 出版形) と (6.8.3) bootstrap

### (5.6) [04.7, 出版形・既に重み付き]
Hyp (5.2) 下、𝒮₁={χ₁..χₙ}⊂𝒮 共役閉、𝒮₂={χ,χ̄}⊂𝒮, 𝒮₁∩𝒮₂=∅。(a) 𝒮₁ coherent、(b) χ₁(1)∣χ(1)、
**(c) `2χ(1)χ₁(1) < Σᵢ χᵢ(1)²/‖χᵢ‖²`** ⟹ 𝒮₁∪𝒮₂ coherent。
**証明の核** (5.6.1)→(5.6.2): `(χ−aχ₁)^τ = X−Y`、Y を 𝒮₁^{τ₁} 基底へ射影し
**`Y = a·χ₁^{τ₁} − λ·Σᵢ (aᵢ/‖χᵢ‖²)·χᵢ^{τ₁} + Z`** (係数は **λ·aᵢ/‖χᵢ‖²**、λ load-bearing)。
(5.4.a) ‖X‖²≥‖χ‖² + 等長で `λ²·Σᵢ(aᵢ²/‖χᵢ‖²) − 2λa + ‖Z‖² ≤ 0`。`b=2a/Σᵢ(aᵢ²/‖χᵢ‖²)`、
仮説 (c) が `0<b<1` ⟹ λ∈ℤ で λ=0 ⟹ Z=0 ⟹ Y=a·χ₁^{τ₁} ((5.6.2))。τ₂ 拡張で coherence。
**reducible でも成立**: ‖χᵢ‖² 分母は orthogonal だが非 orthonormal な χᵢ^{τ₁} への射影係数で、reducibility に
依存しない。**reducibility を縛るのは結論でなく仮説 (5.2)** (各 reducible μ_j に R(μ_j) と pairwise 直交が要る)。

### (5.2) が case B で成立 [(5.3.b)]
(5.3.b): 𝒮 ⊂ {Ind_K^L θ | H⊄Ker θ} で Hyp (5.2) 成立。reducible χ=μ_j には **R(μ_j)={±δ ω_ij^σ, ∓δ ω_ik^σ}**
(μ̄_j=μ_k)。**= 構築済 σ-isometry の像**。⚠ 符号 convention: (5.3.b) は δ_j、(4.9.b) は δ_k → (4.9.a) で整合、
formalize 時は一方に固定。**(5.6) 自体は Frobenius-free** (Frobenius/certain-type は (5.2) 確立にのみ使う)。

### (6.8.3) bootstrap [case B]
S not coherent と仮定 → 有限性で X∪Y⊂S₁⊂S (共役閉, S₁ coherent), S₂={ψ,ψ̄}⊂S, S₁∪S₂ not coherent を取る。
(5.6) 対偶: `2ψ(1)η₁(1) ≥ Σ_{S₁} χ(1)²/‖χ‖² > Σ_X χ(1)²/‖χ‖²`。
**counting**: `Σ_X χ(1)²/‖χ‖² = Σ_{θ∈Irr H: Z⊄ker θ} |L:H|θ(1)² = |L:H|(|H|−|H:Z|) = |W₁||H:Z|(|Z|−1)`。
ψ=Ind_H^L θ, θ(1)=d ⟹ `2d|W₁|² > |W₁||H:Z|(|Z|−1)`、Cor (2.30) `d²≤|H:Z|` ⟹ `4|W₁|² > |H:Z|(|Z|−1)²`。
**case B 矛盾**: W₁ が H/H' と H'/Z=H'/W₂ に FPF (奇数位数) ⟹ 各因子 ≥2|W₁|+1 ⟹ `|H:Z|=|H/H'||H'/Z|≥(2|W₁|+1)²`、
|Z|−1≥2 ⟹ `|H:Z|(|Z|−1)² ≥ (2|W₁|+1)²·4 > 4|W₁|²`。矛盾。⟹ S coherent。

### 🔑 検証で出た formalize 上の精密化 (verdict より)
1. **counting は SUM レベルでのみ正しい**: per-single-θ の `χ(1)²/‖χ‖² = |L:H|θ(1)²` は reducible χ では**偽**
   (正: `|L:H|²θ(1)²/r`, r=|I_L(θ):H|)。和として θ∈Irr H 全体を走り L-orbit 重複が per-χ 値を再構成。
   repo の `sum_re_sq_Xset_eq` は θ 上の和で正しく処理済 (linear |L:H| collapse 込)。
2. **|L:H| は linear** (squared でない): |W₁|-元 W₁-orbit の各 θ が **1 つの** χ (χ(1)=|L:H|θ(1)) に誘導されるため。
3. **reducible 回避不可** (verdict 4, holds): case (c2) でのみ非自明。X=S−S(Z) が reducible column μ_j を含み、
   column→constituent 置換は coherence を保たない (Dade 拡張は Z[S₁] の column 基底上で定義)。c1 Frobenius は全既約で問題なし。
4. strict vs non-strict: (5.6.c) は strict、対偶は ≥、bootstrap は FPF slack (2|W₁|+1)²>4|W₁|² から矛盾 (repo は non-strict で処理)。

## 3. 残務 = formalization GLUE (新数学なし) — frontier

唯一の実 sorry = **`S08_CoherenceTheorems.lean:59`** (`sibleySetup_is_coherent` の X-nonempty 枝)。閉じるのに必要:

1. **(6.8.3) bootstrap 配線** (NEW WORK, assembly): 既存重み付きエンジンを消費する case-B capstone
   - `caseB_xSum_le_two_psi`: case-A `xSum_le_two_psi`(S08CP2:3229) の mirror、`coherentDegreeSqNormBound_of_not_coherentW` + `caseB_member_family_weighted` を使う。
   - `false_of_coherentXunionYset_of_not_coherentS_caseB`: case-A capstone (S08CP2:3439) の mirror、(a) reducible-S 用 break-pair extractor + (b) `caseB_xSum_le_two_psi` + (c) `false_of_caseB_break_of_bounds`(既存)。
2. **`caseB_member_family_weighted`** (NEW WORK): mixed break set S₁ (既約 + reducible column μ_j) の per-step
   `XAdjoinStepInputW` を組む。`mc i = ‖μ_j‖²` を供給。部品は既存 (`caseB_constituentDecomposition`/`caseB_phi_family`/`certainTypeR`/σ-images)。
3. **per-step `XAdjoinStepInputW` 構成子** (NEW WORK): `xChainCoherentW` が hstep として要求。certain-type column data から各ステップ入力を構築 (xChainCoherentW の docstring に明示)。
4. **reducible 用 break-pair extractor**: `exists_coherentBreakPair`(S08CP1:965) は `hSbirr`=全既約を仮定。
   involution ベースの列挙ゆえ irreducibility 非依存の可能性が高いが、**1 箇所も ‖χ‖²=1 を消費しないか要確認** (移植 or 1 点 weight-aware 化)。
5. **math-(A)/(B) dispatch** (NEW WORK, final wiring): S08:59 で `hyp.cases` (Frobenius/CertainType) 分岐 +
   case (c2) 内で `Z(H)∩W₂` を `eq_bot_or_eq_of_le_of_card_prime` で case-A(=⊥)/case-B(=W₂) に分け、A→centralCommutator/Zc 経路、B→anchored-image+算術破綻 経路へ。

### (6.8.2) X∪Y coherence の前提 `hXanchored` (別系統・要解決)
case-B capstone は X∪Y coherent を前提とする (`coherentCertainTypeSet_union_Yset_via_anchoredImages`、
hXanchored 入力)。session 49 が詰まったのはここ。**解決法 = per-φ-polymorphic 化** (別 ChatGPT 相談で確定、
正本 `s08_6_8_chatgpt_answer.md`): 固定 φ でなく **column ごと `φ_c := centralChar Z (θ_c)`** を取れば
positivity `⟨φ_c, Res_Z θ_c⟩ = θ_c(1) > 0` が Isaacs 2.27 から即時。
- ⚠ **架構上の問い** (B が精査すべき): `exists_decomposition_caseB`(S08CB2:126) は `IsPGroup ↥H` を要求するが、
  上記 bootstrap 経路 (重み付き (5.6) + counting + FPF) は **H が p-群である必要はない**。
  per-φ aggregate 経路 (IsPGroup 要) と bootstrap 経路 (不要) のどちらで capstone を閉じるか要判断。
  IsPGroup が真に要るなら、p-group reduction は **Frobenius 専用 `isPGroup_of_not_coherent` でなく Hyp (6.4)/(6.5) 一般形**
  から (c2 ⟹ L/H' Frobenius via FPF on H/H'、+ nilpotent-with-pgroup-abelianization)。詳細 `s08_6_8_chatgpt_answer.md` Q4。

## 4. B レーン稼働の推奨手順

0. (前提) 上記架構上の問い (bootstrap 経路 vs per-φ aggregate 経路、IsPGroup 要否) を最初に判断。
   **bootstrap 経路が IsPGroup を回避できるなら最短** (既存エンジン消費のみ)。
1. (6.8.3) capstone 配線: `caseB_member_family_weighted` → `caseB_xSum_le_two_psi` → `false_of_coherentXunionYset_of_not_coherentS_caseB`。
   ほぼ case-A mirror。reducible break-pair extractor の irreducibility 非依存を確認。
2. (6.8.2) X∪Y coherence: per-φ producer を φ-polymorphic 化 (centralChar/Isaacs 2.27) → hXanchored 充足。
3. math-(A)/(B) dispatch を S08:59 に配線 → 完全 close。
4. 低リスク確認: coprime quotient-centralizer 式 (FPF 整除に要、mathlib/CoprimeAction にあるか grep; なければ標準新補題)。

**規模感**: 「Section 5 大改造」ではなく **case-A の構造化 port + per-φ refactor + dispatch**。multi-session だが tractable。
```
