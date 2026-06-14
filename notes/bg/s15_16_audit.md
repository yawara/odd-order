# BG §15 / §16 — faithfulness + dependency + gate audit (Lane G, 2026-06-14, post-13.6)

Lane G を §13 → BG §15+§16 に再配置した直後の着工前監査。目的は LAUNCH の
「scaffold の faithful 化 + §14 非依存補題」を実行可能な形に落とすこと。
正本 mmd = `references/bg/local-analysis.mmd`、§15 = L4086–4255、§16 = L4256–4562。
対象ファイル = `OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean`（9 sorry）/
`S16_MainResults.lean`（9 sorry）。

## 0. ゲート現実（重要）

**§15/§16 の 18 endpoint はすべて §14（Lane H）/ §13（Lane F）に gate されている。**
各 docstring が proof gate を列挙しており（下表）、mmd の "schematic proof" 依存表
（L4424–4449）とも一致する。⟹ **現時点で §14 非依存に証明できる §15/§16 の主結果は無い。**
唯一の ungated Lean ターゲットは `M_F` の基本 API（§3）。本格証明は F が §13、H が §14 を
landing させてから。

## 1. FT-critical spine（私の担当の中で最短経路に乗る部分）

```
Prop 16.1 (型辞書 S14↔shared)  ──┐
BG Theorem I  (8.8 へ)          ──┼─→ Peterfalvi S10_BGInterface (既に私の scaffold を cite)
BG Theorem II (8.12/8.13 へ)    ──┘        ↓
                                    Pf §10–16 character theory
                                            ↓
                          FeitThompson.sectionSixteenHypothesis_of_isMinimalSimpleOdd
                                  (= FeitThompson 層 唯一の実 sorry)
```

- `sectionSixteenHypothesis_of_isMinimalSimpleOdd`（[FeitThompson.lean:67]）は **Peterfalvi**
  の `S16.Hypothesis` を生成する。BG §16 の Theorem I/II はそこへ供給される指標論側の入力。
- `OddOrder/Peterfalvi/S10_BGInterface.lean` は既に私の §16 scaffold を cite している
  （`proposition_type_classification` / `theoremI_…` / `theoremII_…`）。⟹ **私が §16 scaffold を
  証明すると Peterfalvi interface の conditional 補題が自動 unconditional 化する。**
- よって優先順位 = **Prop 16.1 → Theorem I → Theorem II**（A–E はそれらの支持）。

## 2. 忠実性 verdict（endpoint 別）

### §16（mmd L4256–4562 を直接照合済）

| endpoint | mmd | verdict | 備考 |
|---|---|---|---|
| `proposition_type_classification` (Prop 16.1) | L4478 | ✅ **faithful** | 6 句 = mmd (a)–(f) 完全一致 |
| `theoremB_U_and_A_tame` (Thm B) | L4368 | ✅ **faithful** | 5 句 = B(1)–(5)。⚠ 句2 は `centralizerGeneratedBySigma M U = ⟨U∩M̂_σ⟩` の def 等式に依存（成立するが証明要） |
| `theoremA_maximal_structure` (Thm A) | L4274 | ⬜ 未照合 | gate: 10.2(b)/15.1(a)/14.2(abc)/15.2(a)/15.5/15.7 |
| `theoremC_paired_structure` (Thm C) | L4303 | ⚠ **lossy** | `∃! Mstar` 句が C(4)(6)(7)(8) を緩く束ね、**落ちている**: C(4)「K=C_{M*}(K*) かつ K* は κ(M*)-Hall」/ C(6)「M∩M*=K×K*」(scaffold は IsCyclic(K⊔K*) のみ) / C(7)「全 H∈M_P は M か M* に共役」/ C(8)「N_G(Ẑ)=Z」/ C(9)「C_M(Ẑ)=A_0−A」。また C(2)「M_F 非巡回」が Thm C に無い（Cor 15.6 にはある） |
| `theoremD_msigma_conjugacy_and_centralizers` (Thm D) | L4317 | ⬜ 未照合 | D(4) tail は復元済。gate: 15.3(b)/12.17/14.4(b)/A(8)/15.9 |
| `theoremE_sigma_partition_and_counting` (Thm E) | L4370 | ⬜ 未照合 | gate: 14.5(c)/13.9/14.9 |
| `aSets_support_slice` | L4368/4404 | ⬜ 未照合 | A/A_0 の TI + Supports スライス |
| `theoremI_…dichotomy` (Thm I) | **L4526** | ⚠ **両部あるが圧縮** | 句1 共役 = mmd Thm I 句1 ✓ / 句2 dichotomy は mmd の (1)–(5) を圧縮し **落ちている**: W の normalizer-V 性質、S=W₁S′/T=W₂T′/S∩T=W 構造、条件(5)「S,T とも II–V 型」。**docstring の mmd 行参照 L4402 は誤り → L4526 に修正要** |
| `theoremII_tame_embedding` (Thm II) | **L4548** | ⚠ **lossy** | (Ti)+D⊆A+一意性+型I/II は捕捉、**落ちている**: (Tii)(a)–(e) supporting-subgroup system、(Tiii)。Pf (8.12)/(8.13) が (Tii)/(Tiii) のどこまで要るか要確認。docstring 行参照 L4416 も要確認 |

### §15（docstring の gate 表のみ。mmd L4086–4255 の本文照合は次セッション）

| endpoint | gate（docstring 記載、mmd と要照合） |
|---|---|
| `typeP_auxiliary_structure` (Lemma 15.1) | 14.7(d)(h)/12.10(b)/10.2(c)/14.3/12.5(d)/12.12 |
| `mf_ne_msigma_typeP1_structure` (Thm 15.2) | 14.1/14.7(f)/14.2(a)/6.3(a)/3.8/1.5(a)(d)/3.7/3.10/5.5(a) |
| `mf_hall_centralizer_control` (Cor 15.3) | — |
| `nilpotent_hall_embeds_in_mf` (Cor 15.4) | — |
| `fitting_decomposition` (Cor 15.5) | — |
| `typeP_kstar_in_mf` (Cor 15.6) | — |
| `fitting_not_ti_cases` (Thm 15.7) | E_i/exponent/Ω₁(Z(P)) 句は §12/§10.13 encoding 完成まで deferred と docstring 明記 |
| `tau2_transfer_constraint` (Thm 15.8) | 14.12/15.2/12.6/Uniqueness/12.17/14.4 |
| `centralizer_escape_final_local` (Cor 15.9) | 同上 |

## 3. §14 非依存の provable core（現時点で唯一の Lean ターゲット）

`maxNilpotentNormalHall M = sSup {N | N≤M ∧ (N.subgroupOf M).Normal ∧ Nilpotent ∧ Hall}`。
def docstring は「この sSup が再び maximal nilpotent-normal-Hall 性を持つ（特に Hall）」を §15 へ
deferred としている。そのうち **containment と M-正規性は §14 非依存に証明可能**（Hall 性が本丸で残る）。

- ✅ **`maxNilpotentNormalHall_le` (`M_F ≤ M`)** — 本セッション landing（`sSup_le fun _ hN => hN.1`、S15_MF.lean）。
- ⬜ **`M ≤ normalizer (M_F)` / `(M_F.subgroupOf M).Normal`** — 次ターゲット。証明スケッチ:
  m∈M に対し各候補 N は (N.subgroupOf M).Normal ⟹ M≤N_G(N) ⟹ `conj m • N = N`
  (`conj_smul_eq_self_of_mem_normalizer` + `le_normalizer_of_normal_subgroupOf`)。よって
  conj m は候補集合 S を各点固定 ⟹ `conj m • sSup S = sSup S` ⟹ m∈normalizer。
  要 pin: 本 repo の set-引数 `Subgroup.normalizer (· : Set G)` の所在 + pointwise `smul_sSup`。
- Hall/nilpotent の well-definedness = 真の §15 内容（nilpotent は Fitting で join 可、**Hall が hard core**）。

## 4. 次セッション推奨

1. `M ≤ normalizer (M_F)`（§3 スケッチ）を landing — MF 基本 API を完成。
2. faithfulness 監査続行: Thm A/D/E + Lemma 15.1 を mmd 本文照合（§15 本文 L4086–4255 未読）。
3. lossy statement の修正（Thm C → Thm II → Thm I dichotomy の順）。**ただし**:
   - scaffold sorry の statement 強化は Peterfalvi citation を壊さない（結論が強くなるだけ）が、
     1 定理ずつ build 検証して進める。
   - 落ちた句のうち **downstream（Pf 8.x / final contradiction）が実際に要する分**を優先復元。
     不要に重い句を足して sorry を膨らませない。
4. 本格証明は §14（H）/§13（F）landing 後。それまでは 1–3 を回す。

## 5. §15-body 忠実性監査 (mmd L4166–4262, 2026-06-14 追加)

§15 endpoint 全 9 件は **external citation 0**（freely fixable）。⚠ **monitor の sorry-不増 gate**
ゆえ修正は「既存 sorry の強化/差替え」のみ可、**新 sorry'd theorem の追加は不可**（合流 abort）。

| endpoint | mmd | verdict |
|---|---|---|
| `mf_hall_centralizer_control` (Cor 15.3) | L4204 | **✅ FIXED 2026-06-14** — 旧 scaffold は無関係な centralizer-escape 主張 (`C_G(X)≤M ∨ …`) で docstring (「centralizer and conjugacy control」) と不一致だった。mmd 15.3(a) `C_M(H)=C_{M_σ}(H)·X` (X cyclic τ₂) + (b) `N_M(H)`-fusion に restated (uncited, sorry-neutral) |
| `typeP_kstar_in_mf` (Cor 15.6) | L4228 | ✅ **faithful**（K*≠1 cyclic ⊆ M_F∩M''、M_F 非巡回 — 5 句一致） |
| `typeP_auxiliary_structure` (Lemma 15.1) | L4166 | ⚠ **narrowed + lossy**: scaffold は `IsTypeP M` 仮説を追加（mmd は **全 M ∈ ℳ**）→ type-F 失う。また 15.1(c) の「X は cyclic τ₂(M)-subgroup」が脱落（M(C_G(X))={M} のみ保持） |
| `mf_ne_msigma_typeP1_structure` (Thm 15.2) | L4180 | ⚠ **organizational**: mmd 冒頭の一般鎖「1⊂M_F⊆M_σ⊆M'⊂M」が statement に無いが、その事実は **Theorem A に存在**（`MF≤Msigma`, `Msigma≤M'`）。M_F≠M_σ 分岐の 7 bullet は概ね faithful |
| `fitting_decomposition` (Cor 15.5) | L4219 | ⚠ **lossy + 要検証**: mmd F(M)=F(M_σ)×Y を scaffold は `MF(Msigma M)⊔Y` で表現（**MF(M_σ) vs F(M_σ)** の等式は非自明・要確認）。(a)τ₂/(c)「H⊆M', M'/H nilpotent」/(d)「K≠1→F(M)⊆M'」脱落 |
| `fitting_not_ti_cases` (Thm 15.7) | L4234 | ⚠ **known-deferred**（docstring 明記）: (d) E₃=1/E₂⊴E/E≅E₁、(e) 詳細 trichotomy（O_p/O_{p'}/exponent/Ω₁(Z(P))）が deferred。mmd の (a)(b)(c) + (e) 概形は捕捉 |
| `tau2_transfer_constraint` (Thm 15.8) | L4264 | ⚠ 要精査: mmd「q=|K|, q は τ₂(H) 唯一の素数, τ₂(M)=∅」を scaffold は `tau2 M=∅ ∧ ∃q, tau2 N={q}`（**N vs H**、「q=|K|」脱落） |
| `centralizer_escape_final_local` (Cor 15.9) | L4298 | ⬜ 未精査 |
| `nilpotent_hall_embeds_in_mf` (Cor 15.4) | L4215 | ⬜ 未精査（mmd: nilpotent Hall H → M を H⊆M_σ に取れる） |

**次の安全な fix（sorry-neutral 強化、優先順）**: Lemma 15.1(c) に「X cyclic ∧ τ₂」追加 / Cor 15.5 に
(c)(d) 追加 + MF(M_σ)=F(M_σ) を別途確認 / Lemma 15.1 の `IsTypeP` 仮説除去（要 type-F 整合確認）。
**Thm 15.2 一般鎖は新 theorem 不可（monitor gate）ゆえ Theorem A 経由で足りると判断、修正不要**。

## 参照

- mmd §16 schematic proof 依存表 = L4424–4449（Thm A–E の gate を 1 行で）。
- Prop 16.1 本文 + 証明 = L4478–4520（Thm A(8)/B(1-3)/C(2)(8)/15.7(c) 使用 → gated 確認）。
- Thm I = L4526、Thm II = L4548、tamely imbedded の定義 remark = L4560。
- Peterfalvi 消費側 = `OddOrder/Peterfalvi/S10_BGInterface.lean`（私の scaffold を既に cite）。
