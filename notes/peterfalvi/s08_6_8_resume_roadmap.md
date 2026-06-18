# Pf (6.8) case-B resume roadmap — 正本 (2026-06-17, 2 workflow + Plan agent + 直接 grep で code-verified)

> この note が **S08:59 `sibleySetup_is_coherent` を閉じるための現行 source-of-truth**。churn した
> `s08_6_8_assembly_plan.md`(458KB)/`s08_6_8_3_gap_resolution.md` のうち本 note と矛盾する記述は本 note を優先。
> 上位方針・FT 接続の文脈 = 記憶 [[ft-path-policy]] の 2026-06-17 検証訂正ブロック。

## ✅✅✅✅ 2026-06-18 cont.¹³ — case-B 核心数学 COMPLETE: seed + anchor + bootstrap (P4+P5+P6a+P6b)

**cont.¹² の残務 (P4 glue + P5 wire + P6 discharge) のうち、case-B 固有の数学を全て完成。**
新 leaf [`S08_CaseBSeedGlue.lean`](../../OddOrder/Peterfalvi/S08_CaseBSeedGlue.lean) (4 producer、
全 sorry-free + axiom-clean = propext/Classical.choice/Quot.sound のみ、full build 3859 jobs green):

- **(P4) `coherentXunionYset_caseB`** — seed `IsCoherent hyp.tau (X(W₂) ∪ Y)`。cX=`caseBXset_isCoherent`、
  ν=`exists_glue_nu_Xset_Yset_via_map`(grid ∪ irreducible-X source、全員 irreducible ゆえ orthonormality
  自動)、hmixed=`caseB_member_seam_all_Yset`(column 専用 seam を一般メンバ化)、cross-diagonal χ₁−a₁·η₁ で
  hDτ(anchored image 恒等式)+hgen(`hgen_withDiagonal_Xset`、次数比整数性は hdvd の p-power 可除性から)。
  commit `e2ac14a4`。
- **(P5) `nonempty_coherent_S_caseB_of_anchor`** — seed→S coherence(`nonempty_coherent_S_caseB` bootstrap)。
- **(P6a) `exists_caseB_Xset_anchor`** — 最小次数 p-power anchor。`exists_charValue_one_eq_mul_xBaseBlock_anchor`
  (Frobenius 版)を case-B へ: `Set.exists_min_image` で最小次数 χ₁ 直接選択、p-power ゆえ最小が全てを割る。
- **(P6b) `nonempty_coherent_S_caseB_of_structure`** — **case-B 枝を「(6.4)/(6.5) 構造データ + hXne + hYcard」へ
  完全還元**。anchor=(P6a)、hnonzero=共役差 χ̄−χ(`caseB_irr_conj_diff_support`、no-real ゆえ≠0)、Y-anchor=
  `Yset_nonempty`。commit `e17be957`。

**⟹ case-B の数学的内容(seed glue + anchor 構成 + p-power 可除性 + 6.8.3 bootstrap)は完全に閉じた。**
**「hXanchored gap」は cont.¹² の anchored-image route で完全消滅 = ユーザー直接管理は不要に。**

### ▶ 残務 = S08:59 dispatch (case-B 固有でない overarching phase、(6.5) p-群還元にゲート)

`nonempty_coherent_S_caseB_of_structure` を S08:59 に配線するには:
1. **(6.5) p-群還元** = X-nonempty(H 非可換)から H が p-群(p≥3 odd)を導く。**= dispatch 全体の真のゲート。
   単一定理として未形式化**(case-A producer `Xset_centralCommutator_isCoherent_of_c2_caseA` も hp/hp3/hHp/hHnonab を
   仮説で取る ⟹ 還元は dispatch level でまだ無い)。Sibley minimal-counterexample 論法、大型・別 phase。
2. **構造データ discharge `_of_c2_caseB`** (case-A producer のミラー、未実装) = math-case-B 条件(W₂⊆Z(H)) + p-群 +
   非可換から hcen/hderiv/hc2/hcZ/hfpf/hFPF/hYcard/hXne を導く。素材は在庫: hfpf=`caseB_fpf_bound`
   (`S08_CaseBEndgame:338`、hMgt=非可換 + hWMgt 入力)、hFPF=hfpf + index 算術(case-B で W₂⊆H ゆえ
   W₂.index=|W₁|·(W₂.subgroupOf H).index、∴ |W₁|<index)、hderiv=`commutator_subgroupOf_self`、
   hcen=case 条件、hcZ=W₂ 素数。**achievable だが多ピース + 下流で (6.5) にゲート**。
3. **math case A/B split** = Z(H)⊓W₂ が ⊥(case A)か W₂(case B)か(`eq_bot_or_eq_of_le_of_card_prime`、素数位数)。
4. **Frobenius (c1) 枝** = `nonempty_coherent_S_caseA_of_frobenius`(unconditional、hp/hp3/hHp/hHnonab 要)。
5. **case-A (c2) 枝** = `Xset_centralCommutator_isCoherent_of_c2_caseA` + S への bootstrap。

**⟹ S08:59 を閉じる残務は case-B seed work でなく overarching dispatch + 未形式化の (6.5) 還元。**
**FT 文脈不変**: (6.8) は [[ft-path-policy]] で orphaned (deferred-payoff) — 閉じても feitThompson sorry は今は減らない。

## 🔨 2026-06-18 cont.¹⁴ — (6.5) p-群還元に着手 (ユーザー裁可): (6.5)(b) 適用 DONE、残ゲート = (6.3)+(6.4.c)

**(6.5) Theorem 精読** (`04.8:50-74`): (6.4) Hypothesis + ¬coherent(S(M)) ⟹ (a) K/H₁ chief factor +
`|K:H₁| ≤ 4|L:K|²+1` / (b) K/M 非可換 p-群 / (c) |L:K| ∤ p−1。**(6.8) は M=1,K=H で適用**し by_contra で
¬coherent を供給 (`04.8:150`「By (6.5), we may assume H is a non-abelian p-group」)。

**🎉 (6.5)(b) の group-theory core は repo に既存・形式化済み** (`S08_CoherenceCorePart1`):
- `isPGroup_of_isFrobeniusGroup_of_card_le` (`:3120`) = (6.8)(c1) Frobenius 版。
- `isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator` (`:3159`) = (6.8)(c2) certain-type 版。
- 両方 **`hbound : |Abelianization H| ≤ 4|W₁|²+1` を唯一の非自明入力**に取る (内部で chief-factor + nilpotent
  ⟹ p-群 を処理 = `isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization` `:3097`)。

**✅ cont.¹⁴ 成果 (R1, `057fab18`、新 leaf `S08_PGroupReduction.lean`、sorry-free+axiom-clean)**:
- odd 側条件 `card_W1_odd`/`card_H_odd`/`card_abelianization_H_odd` (|L| 奇から)。
- **`exists_isPGroup_H_of_frobenius_of_card_le`** = (c1) 適用 (hyp.cases.inl + odd + hbound → H p-群)。
- **`exists_isPGroup_H_of_c2_of_card_le`** = (c2) 適用 (W₁-共役 action 構築 + explicit-conj hfix を smul 形へ
  bridge + hcop + hbound → H p-群)。
- ⟹ **(6.5)(b) 適用は両ケース完了**。残ゲート 2 本を named 仮説として isolate。

**▶ 残ゲート (cont.¹⁴ で確定、(6.5) 還元の本体)**:
1. **hbound = Theorem (6.3) の対偶** = 真の bottleneck。(6.3) (`04.8:24`): [H/M nilpotent ∧ S(H₁) coherent ∧
   |H:H₁|>4|L:K|²+1] ⟹ S(M) coherent。**未 assembled**: arithmetic core (`degreeBound_le_of_sqrt_bound`
   `:2798`) + nilpotency central step (`isNilpotent_normal_inf_center_ne_bot` `:1100` /
   `exists_maximal_normal_between` `:1149` / `normal_central_of_maximal_normal_below` `:1175`) は在庫だが、
   **minimal-A induction の assembly + (6.2) degree bound (`2|L:C|√|C:D| ≥ |K:A|−1`、(5.6) coherence-break
   sum) が未**。(6.2) 部品 = `theta_degree_le_index_mul_sqrt_index` (`:557`) + break sum (case-B の
   `sum_re_div_normSq_Xset_eq` を一般 S(A) へ)。**= 大型 (~2-3 session)**。
   (6.8) M=1 適用: ¬coherent(S) + H nilpotent + S(⁅H,H⁆)=Y coherent (hyp.coherentYset) ⟹ |H:⁅H,H⁆|≤4|W₁|²+1。
2. **hfix (c2 のみ) = (6.4.c)** = W₁-共役固定点 ⊆ ⁅H,H⁆ (= L/⁅H,H⁆ が kernel H/⁅H,H⁆ の Frobenius)。
   h46 の (4.2)/(4.6) 構造から導出要。c1 は Frobenius 構造から自動。

**▶ dispatch 全体構造** (S08:59、`(nonempty…).some` で Type 化):
```
by_contra hncoh  -- ¬Nonempty(IsCoherent S)
rcases hyp.cases with hF | ⟨h46,…⟩
· -- c1: hbound(6.3) → exists_isPGroup_H_of_frobenius → p≥3(odd)+nonabelian(hXe)
  --     → nonempty_coherent_S_caseA_of_frobenius (既存 unconditional) → contra
· -- c2: hbound(6.3)+hfix(6.4.c) → exists_isPGroup_H_of_c2 → p-群
  --     → math A/B split (eq_bot_or_eq_of_le_of_card_prime) →
  --       A: case-A producer / B: nonempty_coherent_S_caseB_of_structure (cont.¹³) → contra
```
非可換 = hXe (Xset ⁅H,H⁆ nonempty ⟹ ⁅H,H⁆≠⊥ via `SsubFiltration_bot` ⟹ commutator ↥H≠⊥)。
p≥3 = p∣|H|∣|L| 奇 ⟹ p 奇。**⟹ 次の本丸 = Theorem (6.3) assembly ((6.2) break bound + minimal-A induction)**。

### 🔨 cont.¹⁴ 進捗² — (6.3) 着手: (6.2) foundational 2 ピース landed、残 = (6.2) break bound (case-intertwined)

新 leaf `S08_Theorem63.lean` (sorry-free):
- **`sum_re_div_normSq_SsubFiltration_eq`** (`068ab98c`) = (6.2) の S(A) 次数二乗和
  `∑_{χ∈S(A)} χ(1)²/‖χ‖² = |L:K|(|K:A|−1)` (case-B `sum_re_div_normSq_Xset_eq` を単一フィルタ簡約)。
- **`exists_SsubFiltration_member_degree_index`** (`b0df4345`) = (6.2) の degree-|L:K| anchor
  (A⊊K ⟹ degree-1 char inflate+Ind、divisibility |L:K|∣ψ(1) の源)。

**▶ 残 = (6.2) break bound `|K:A|−1 ≤ 2|L:C|√|C:D|`** = 大型・**case-intertwined**:
- 部品: break pair `exists_coherentBreakPair_general` (`:1035`) + (5.6) family bound + 上記 sum + theta bound
  `theta_degree_le_index_mul_sqrt_index` (`:557`)。
- **🚨 重要発見 (再調査不要)**: (5.6) family bound `sMember_degreeSqNormReBound_of_not_coherent`
  (`S08_CaseBEnumeration:741`) は **h46 依存** (no-real / 列 Gram は case-B 固有)。break pair も
  `HasNoRealCharacters Sb` を要求するが **S(A)/S(B) の no-real は c1/c2 で別証明** (c2=列/既約 dichotomy h46
  依存、c1=Frobenius、既約は odd order)。⟹ **「general (6.2)」は naive に作れない** — (6.2)/(6.3) は (6.8) の
  c1/c2 case 構造と絡む。raw engine `coherentDegreeSumBound_of_not_coherent` (`:2451`, h46 非依存) から
  case 別に組むか、(6.8) M=1 適用を c1/c2 で分けて (6.2) を各々具体化する設計判断要。
- minimal-A induction の部品は在庫 (`exists_maximal_normal_between`/`isNilpotent_normal_inf_center_ne_bot`/
  `normal_central_of_maximal_normal_below`/`degreeBound_le_of_sqrt_bound`)。
- **見積 ~1-2 session**。次着手 = (6.2) break bound を c1/c2 case 別 or raw-engine 一般で組む設計を確定 → 実装。

### 🎉🎉 cont.¹⁴ 進捗³ — 特大発見: (6.2)/(6.3)/(6.5) は c1 用に repo 既存・完成 → Frobenius 枝を完全 close

**`S08_CoherenceCorePart2:3538-3837` に (6.2)/(6.3)/(6.5) が Frobenius 用に全実装済みと判明**(精読見落とし):
- `psi_degree_le_of_source`/`_central` (theta bound)、`six_two`/`six_two_central` (= (6.2))、
  `six_three_index_bound`/`six_three` (= (6.3) minimal-A induction full)、
  **`isPGroup_of_not_coherent` (`:3803`) = (6.5) 還元 `¬coherent(S) ⟹ H が p-群`**(全 c1=hF 依存)。

**✅ R2 (`3b8b367a`、`S08_PGroupReduction.lean`、sorry-free+axiom-clean): (6.8) の Frobenius (c1) 枝を完全 close**:
- `nonempty_coherent_S_of_frobenius` (hF + hXe ⟹ Nonempty(IsCoherent S)): by_contra →
  `isPGroup_of_not_coherent` → p≥3 (`three_le_of_isPGroup_H`) + 非可換 (`commutator_ne_bot_of_Xset_commutator_nonempty`)
  → `nonempty_coherent_S_caseA_of_frobenius` → 矛盾。**= S08:59 の c1 分岐そのもの**。

**▶ 残 = c2 (Hyp46) 分岐の (6.5) 還元**。2 ゲート:
1. **c2 (6.3) = reducible-break subtlety**。c1 の six_two は break ψ を irreducible 要求
   (`isIrreducibleCharacter_of_mem_S_of_frobenius hF` + (5.6) engine `coherentDegreeSumBound_of_not_coherent`
   は `χ : IrreducibleCharacter` 必須)。**c2 は S に reducible column を含む** ⟹ break が column なら (5.6) engine
   不適用。**⚠ T63-1/T63-2 (sSubFiltration sum + bound) は ψ irreducible 前提ゆえ c2-(6.3) が reducible break を
   生むなら off-path** = 要検証 ([[pf-s08-caseb-seed-route-uncertain]] 型の不確実性)。c2-(6.3) の break が
   構造的に irreducible と示せるか(列が S(A) に常に入り break から除外されるか)を次に精査。
2. **hfix = (6.4.c)**(W₁-共役固定点⊆⁅H,H⁆、h46 から導出、`exists_isPGroup_H_of_c2_of_card_le` 入力)。

**dispatch 配線は保留**: `nonempty_coherent_S_of_frobenius` は S08_PGroupReduction 在(S08_CoherenceTheorems の
下流)ゆえ直接 import 不可。c1 piece は S08_CoherenceCore 上流の素材のみ使う ⟹ 将来 upstream 移設 or hub に inline。
**c2 が揃ってから一括配線**(中間 sorry を hub に残さない)。⟹ **次 = c2-(6.3) reducible-break 精査 → 可なら c2 還元実装**。

## 🚨🚨 2026-06-18 cont.¹² — 重大訂正: 「真の gate = hDeg = (6.6)」は **誤り**。(6.8.2) は anchored-image で chain/hDeg 不要

**教科書 04.8 の (6.8) proof を直接精読(L140-235)して判明。cont.⁸/⁹/¹⁰ の「case-B X-coherence の真の gate =
hDeg `2a < ∑ deg²/mc` = (6.6) degree theory」は誤診断。** 根拠:

1. **(6.6) は `X ⊂ Irr L`(全 irreducible)前提**(04.8:74)。これは **case (A)**(`Z=Z(H)∩H'`)の枝で、(6.8.1) が
   「S と S(Z) が各 w₂−1 個の reducible char を持つ ⟹ X=S−S(Z) ⊂ Irr L」を示し (6.6) を適用。**case (B) ではない**。
2. **case (B)(Z=W₂)は (6.8.2) が X∪Y coherence を anchored-image で直接構成**(chain も (6.6) も使わない):
   - (6.8.2.1) η^{τ₁} は Z^# 上定数、(6.8.2.2) aggregate `(Ind^L_Z φ − |H:Z|η₁)^τ = X − |H:Z|Y`、
     (6.8.2.3) **∀χ∈X**: `(χ − aη₁)^τ = X₁(χ) − aY`(a=χ(1)/|W₁|、X₁⊥Y^{τ₁})。
   - **proof of (6.8.2)**: τ₂ を「Z[X∪Y,L^#] 上 = τ、η₁ ↦ Y」と定義 ⟹ (6.8.2.3) で τ₂ は生成系
     **Z[X∪Y, L^#] ∪ {η₁}**(= Z[X∪Y] を張る)上 inner product 保存 ⟹ isometry = coherence。**degree 不等式ゼロ。**
3. **hDeg/(6.6)/Cor 2.30(d²≤|H:Z|)は (6.8.3) にある**(04.8:230-235)= S coherent の bootstrap。これは
   **`nonempty_coherent_S_caseB`(`S08_CaseBWeightedEndgame:372`)で既に DONE**(X∪Y coherent seed → S coherent)。

**⟹ cont.⁸-¹⁰ の chain(`xChainCoherentW`)+ hDeg + norm-1 anchor 問題は全て不要な detour。** chain は (6.6)/case-A の
道具で、case-B は anchored-image τ₂ が正道。私の `coherentCertainTypeSet_union_Yset_caseB`(cont.¹¹)は
**まさに (6.8.2) を certainTypeSet(等次数)に制限したもの**。

**▶ 正しい残務 = (6.8.2) を全 X に一般化**(= seed `IsCoherent (Xset W2 ∪ Y)`、hDeg 不要):
- **per-χ anchored image は全 X で在庫済**: `caseB_member_anchored_image`(任意 θ∈Irr H, W₂⊄Ker θ ⟹ Ind^L_H θ∈X、
  sorry-free)が (6.8.2.3) を全 χ∈X に供給(reducible column / irreducible 不問)。θ-extraction = `hyp.S_eq`
  ({Ind θ:θ≠1})+ Xset membership。
- **varying a**: certainTypeSet は等次数で uniform a₀ だったが、全 X は a=χ(1)/|W₁| が χ ごとに変わる。
  hXinner(等長)は varying a でも成立(`⟨X(χᵢ),X(χⱼ)⟩ = ⟨χᵢ,χⱼ⟩`、私が手計算で確認: aᵢaⱼ 項相殺)。
  xchi_inner_eq_of_anchored を varying-a に一般化要。
- **generation**: 等次数 column diff(`mem_span_columnDiff_of_mem_zSupportedSpan`)→ **scaled diff χᵢ−dᵢχ₁**
  (dᵢ=χᵢ(1)/χ₁(1)∈ℕ ∵ H が p-群)、`span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs`(S07:172、既存)。
- **assembly**: `certainTypeSet_isCoherent_via_anchoredImages` を全 X に一般化(extension を χ-indexed Ximg に)
  → Y と glue(`coherentUnion_of_glued_…`)→ seed → `nonempty_coherent_S_caseB` → S08:59。**= (6.8) case-B を閉じる。**

**⟹ (6.8) case-B は hDeg(大型 §6 degree theory)無しで closeable。** orphaned 文脈は不変だが、closeability の評価が
「multi-session hard §6 math」から「anchored-image 一般化 assembly(新数学ゼロ、在庫部品の varying-a 再配線)」に格上げ。

### 🔨 cont.¹² 進捗 (本セッション) — all-X building block 3 個 landed、残 = extension map + assembly

**✅ 着地 (sorry-free・axiom-clean、leaf 3632 green)** — (P3) の coherence-field content は全て在庫化:
- **`caseB_Xset_member_anchored`**(`b7329b61`)— (6.8.2.3) anchored image を **全 χ∈Xset W₂** に供給
  (θ-extraction: χ=Ind θ ∧ W₂⊄Ker θ via S_eq + mem_SsubFiltration → caseB_member_anchored_image)。
  返り = (X, a=χ(1)/|W₁|, deg, anchored, seam ⟨X,ν₁⟩=0, X∈ZIrr, support)。= **hXanchored + hXzirr + hXmixed source**。
- **`inner_eq_of_anchored_varying`**(`f3cb2e58`)— **varying-a** cross-member isometry
  `⟨Xᵢ,Xⱼ⟩=⟨χᵢ,χⱼ⟩`(xchi_inner_eq_of_anchored の uniform-a₀ を per-χ aᵢ/aⱼ に一般化、aᵢaⱼ 相殺)。
  = 全 X coherence の **hXinner** content。⚠ caseB_member_anchored_image は ℂ-smul `(a:ℂ)•ν` ゆえ
  scalar 補題は robust な simp-only パターン(rw は star 不在で fail)。
- **`anchoredImage_scaledDiff_eq`**(`12764e7c`)— scaled-diff homogeneity `Xᵢ − dᵢ•X₁ = τ(χᵢ − dᵢ•χ₁)`
  (aᵢ=dᵢ·a₁ で ν₁ 相殺 + τ 線形)。= **extends_on_supported** content(varying degree)。

**▶✅ (P3) extension map = 構築完了**(本セッション、`34c707b9`):
- **`grid_mu_notMem_Xset`**(`95f74522`)— 列 constituent μ_{iχ₂} ∉ Xset W₂(度数 mod |W₁| 論法、
  X-member ≡0 / grid ≡±1、`certainType_degree_modEq` + |W₁|≠1)。
- **`caseBXsetExtension`**(`34c707b9`)— dichotomy 拡張 `ν` (basis Irr(L) 上
  `if ω∈Xset W₂ then Ximg(ω) else xChiExtensionFun`)、`caseBXsetExtension_eq : ν(χ)=Ximg(χ) ∀χ∈Xset W₂`
  (`caseB_S_member_column_or_irreducible` dichotomy: column=`columnSum`(grid sum, μ∉Xset で交わらず)、
  irreducible=basis if_pos)。**= cont.¹² で isolate した hard blocker を解消**。

**▶✅ (P3') cX coherence = 構築完了**(本セッション):
- **`mem_span_scaledDiff_of_mem_zSupportedSpan`**(`d645520b`)— supported degree-0 φ → span{f−d•χ₁}
  (varying-degree generation、`mem_span_columnDiff` の一般化)。
- **`caseBXimg` + `caseBXimg_spec`** + **`caseBXset_isCoherent`**(`fc7f8daf`)— `IsCoherent (Xset W₂)`
  via anchored images、4 field 全て building block で discharge(inner=`inner_eq_of_anchored_varying`、
  extends=`anchoredImage_scaledDiff_eq`+generation、ZIrr=bundle)。anchor χ₁ + divisibility(p-群 integral
  ratio)+ nonzero を仮説化(全 satisfiable)。

**▶ 残 = (P4) glue + (P5) wire + (P6) discharge**(cX 完成、最終 assembly mile):
- **(P4) glue-ν + union**: cX(`caseBXset_isCoherent`)と cY を `coherentUnion_of_glued` で union →
  `IsCoherent (Xset W₂ ∪ Y)` seed。要 combined ν(= caseBXsetExtension on X / cY.ext on Y)=
  `exists_integralCharacterMap_glue_of_orthonormal`(**orthonormal source 要**: grid {μ_{ij}} ∪ irreducible
  X-members、全 distinct irreducible で orthonormal、⊥ Y)。column 版 `exists_glue_nu_columnSum_Yset_via_map`
  を grid+irreducible source に拡張(~60行)。glue 条件: hagreeX/Y、hsrc_ortho=`caseB_Xset_orthogonal_Yset`、
  himg_ortho=`caseB_anchoredImage_seam_all_Yset`(seam 全 Y)、hgen。
- **(P5)** seed → `nonempty_coherent_S_caseB`(`S08_CaseBWeightedEndgame:372`)→ S08:59 case-B 枝。
- **(P6) discharge** {anchor χ₁=min-degree X-member, divisibility(θ(1) p-power ⟹ min∣all), nonzero,
  hη₁1/hχ₁1(irreducible degree>0)}+ case-B 構造仮説(hyp.cases.inr)。⚠ **p-power divisibility が唯一の新 math**
  (IsPGroup ⟹ char degree p-power、min selection)。
- **見積**: glue-ν(orthonormal source)+ union + wire + discharge(p-power)≈ 1 fresh session。hDeg 不要。
- **(参考・旧見積)**: extension map = fresh session 1 本(dichotomy basis 構成 + μ∉Xset 構造補題 + 4 coherence field
  配線、building block は ↑で完備ゆえ純 assembly)。hDeg 不要(cont.¹²)。

## ✅✅✅ 2026-06-18 cont.¹¹ — BASE COHERENCE 完成: `IsCoherent (certainTypeSet ∪ Y)` を unconditional 化 + trap 除去

cont.¹⁰ viable route の **(B1) base = `certainTypeSet ∪ Y` coherence** を **UNCONDITIONAL** で landing
(case-B 構造仮説 hW2H/hcen/hderiv/hcop/hp/hHp/hprime/hW2comm/hW2cenL/hc2/hFPF を取るが、これらは
case-B の**実事実**で satisfiable — norm-1 anchor のような構造的不能ではない)。長年の **「hXanchored gap」は
完全に解消** = 全 obligation が dischargeable と実証。3 commit:

1. **`caseB_anchoredImage_seam_all_Yset`**(`44eb562a`, sorry-free・axiom-clean): per-column anchored
   `X` ⊥ **全** `cY.ext y`(anchor η₁ だけでない)。導出 = `⟨X,ν_y⟩ = ⟨X,cY(y−η₁)⟩ + ⟨X,ν₁⟩`、
   後者 = hmix=0、前者 = τ Dade 等長 + cY 等長で `a₀(1−c)+a₀(c−1)=0`(c=⟨η₁,y⟩ 相殺、convention-robust)。
   = 旧 cont.⁷「irreducible seam」を **全 Y・raw-image レベル**に一般化した uniform hXmixed。
2. **`coherentCertainTypeSet_union_Yset_caseB`**(`e6c367ce`, **unconditional**, sorry-free・axiom-clean):
   `coherentCertainTypeSet_union_Yset_via_anchoredImages` の全 obligation を discharge:
   - **Ximg χ₂ := τ(columnSum χ₂ − a₀•η₁) + a₀•ν₁**(certainTypeSet columns 上、他は 0)⟹ hXanchored は
     gated で **trivial 整理**。
   - **hXinner** = `xchi_inner_eq_of_anchored`(per-member、support は bundle 由来)。
   - **hXzirr** = bundle(non-column は 0∈ZIrr)。
   - **hXmixed** = `caseB_anchoredImage_seam_all_Yset`(全 Y)。
   - **uniform a₀** = 参照列 k の weight、certainTypeSet membership の等次数(`columnSum_apply_one`)が全列を a₀ に強制。
   - 補助 `caseB_column_anchored_full`(per-column 完全 bundle: X,a,deg,anchored,seam,ZIrr,support)、
     `caseB_member_anchored_image` に `X∈ZIrr` 追加。
   - **a₀ は `Exists.choose` で取り出す**(goal `IsCoherent` が Type ゆえ `obtain` で ∃ から data 取得不可)。
3. **GATING FIX(trap 除去)**: `hXinner` は両 anchoredImages lemma で **ungated(∀ χ₂ χ₂')** だったが、
   実際は span_induction₂ generator(= certainTypeSet member)でしか使われず、**non-member 列には
   discharge 不能**(support 無 ⟹ τ-等長不成立)= [[scaffold-sorry-free-not-done]] の潜在 trap。member に gate して除去。

**✅ full build 3858 jobs / 26.9s、AxiomsCheck OK。** ⟹ base coherence(B1)完了。

**▶ 残り = (B2) chain + (B3) seed 配線**(cont.¹⁰ の通り、ただし **真の gate = hDeg = (6.6) hard §6 degree theory**):
- **(B2) chain** = `xChainCoherentW`(`S08_CoherenceWeighted:556`)を base=`coherentCertainTypeSet_union_Yset_caseB`、
  X-target=`Xset W2 ∪ Y`、cover=irreducible X-pair に fold → `IsCoherent (Xset W2 ∪ Y)` = seed。
  - **⚠ cover gap 確認済(2026-06-18)**: `caseB_Xset_conjugatePairCover` の仮説 `hnonS₀_irr`(非-certainType 列は
    全 irreducible)は **一般には成立しない**。`S08_CaseBEnumeration:36-42` docstring の通り、**degree class k 以外の
    reducible 列**は `certainTypeSet h46 k` に入らず irreducible でもない ⟹ `Xset W2` を base=`certainTypeSet h46 k`
    (単一 class)+ irreducible chain で **cover しきれない**(norm-1 anchor とは別の構造 gap)。成立は
    「`certainTypeSet h46 k` が全 reducible X-member を捕捉する regime(= 単一 degree class)」のみ。
    ⟹ full seed には **(i) case-B で reducible 列が単一 class と示す**(6.8.2 構造)か **(ii) base を全 class の
    reducible 列(`certainTypeSet` の class 横断和)に拡張**が要。**= (6.8.2) degree-class 構造理論**(hDeg と別の gate)。
    私の `coherentCertainTypeSet_union_Yset_caseB`(単一 class k)は正しい building block だが full seed には不足。
  - **per-step `XAdjoinStepInputW`**: anchor=η∈Y(`‖η‖²=1`、hanchorNorm 満足 ✅)、core field
    (Dmem/hortho/htau1)=brick 2 `caseB_member_orthoDatum`、bound assembly=brick 3 `sMember_degreeSqNormBound`
    (Y-anchor で再利用可)。**真の gate = `hDeg : 2a < ∑ deg²/mc`**(=(6.6) degree inequality、FPF bound から、
    大型 §6 degree theory、multi-session、user-managed)。
- **(B3)** = seed(B2)+ hW2cen/hcZ/hfpf を `nonempty_coherent_S_caseB`(`S08_CaseBWeightedEndgame:372`, DONE skeleton)に
  → `IsCoherent S` → S08:59 case-B 枝。

**FT 文脈(不変)**: (6.8) は [[ft-path-policy]] で FT carrier から **orphaned (deferred-payoff)** — base coherence を
landing しても feitThompson の sorry は今は減らない。(B2) chain の hDeg gate に着手するかは「(6.8) 完全 close」価値 vs
on-path piece(§14 counting=lane-H 等)の優先度判断を要する。本セッション成果 = **base coherence の unconditional 化
+ trap 除去**(seam という長年の難所を含む)。

## ✅✅ 2026-06-18 cont.⁵ — ROUTE RESOLVED: anchoredImages は (6.8.2.3) の正準ツール (cont.⁴ の疑問を解消)

> ⚠ **cont.⁶ で精緻化**: 下記「canonical cX 説は誤り / cX は xChiExtension 必須」は **OVERSTATED**。
> canonical column image も実は ⊥ Y(`inner_coherent_extension_certainTypeOmegaSigma_eq_zero`)ゆえ
> **cX 本命は canonical `xChainCoherentW`**(anchoredImages-cX は不要)。`caseB_member_anchored_image` は
> (6.8.2.3) 部品として保持だが seed には canonical 路線。詳細 = cont.⁶ 末尾。以下 cont.⁵ 本文は (6.8.2.3) の
> 数学的理解として正しい(anchoredImages = (6.8.2.3) の正準ツールは真)が、cX 実装路線だけ cont.⁶ が上書き。

**cont.⁴ の疑問「anchoredImages は critical path 上か?」を、教科書 (6.8.2.3) 原文 + Lean 署名の直接精査で
解決。結論 = anchoredImages 機構 (`caseB_per_phi_anchored_fromYset` 中心) は (6.8.2.3) の唯一の正準ツールで、
ON-PATH かつ CORE。off-path ではない。** 検証根拠 (本セッション、code+textbook-verified):

1. **教科書 (6.8.2.3) は全 χ∈X で成立** (`04.8_*.mmd:208`「Let χ∈X」): `(χ − a·η₁)^τ = X₁ − a·Y`,
   `X₁ ⊥ Y^{τ₁}`, `a = χ(1)/|W₁|`。(6.8.2) proof (`:224`) は τ₂ を `η₁^{τ₂}=Y` でこの恒等式から組む
   ⟹ **hmixed (= seam X-image⊥Y-image) は (6.8.2.3) そのもの**。reducible column と irreducible の両方を要する。
2. **`caseB_per_phi_anchored_fromYset`(`S08_CaseBAssembly:1647`) が (6.8.2.3) を全 X で出す**: 中心線形指標 φ
   の **全正重み constituent** `θ:{0<constituentWeight hφ' θ}` を走り、各 θ に
   `τ(Ind^L_H θ − a•η₁) = (caseB_phi_family…).X − a•cY.ext η₁`(a=θ(1))を出力。**`hirrAnc` field が
   「Ind H θ が column でない」枝 (= irreducible X-member) を明示処理**(column≠Ind H θ ⟹ η₁⊥Ind H θ)。
   W₂≤Z(H) ゆえ全 irreducible θ は `Res^H_{W₂}θ = θ(1)·φ_θ`(`exists_central_phi_data`)で φ_θ の constituent
   ⟹ **全 χ=Ind^L_H θ∈X が per-φ family で尽くされる**(reducible column も irreducible も)。
3. **⟹ cX は xChiExtension を使う** (canonical Dade chain ではない): hmixed は `cX.ext(χ) = X(θ)`(anchored
   image の X-part, ⊥ Y = hXaggorth)を要求。canonical Dade chain image は anchor 項だけずれ得て hmixed を壊す。
   **∴ cont.⁴ point 3「real cX = xChainCoherentW canonical」は誤り**。正しい cX = `xChiExtension`-base
   (`certainTypeSet_isCoherent_via_anchoredImages` `S08_CaseBXChiCoherence:246` の Ximg=X(θ) 拡張) を
   **certainTypeSet → 全 Xset W2 に一般化**したもの。

**∴ route 確定 = anchoredImages 一般化路線** (canonical 路線は破棄):

- **(S1) `Xset_W2_isCoherent_via_anchoredImages`** = `certainTypeSet_isCoherent_via_anchoredImages` を
  index `χ₂:W₂-dual` → `χ∈Xset W2`(または constituent θ)に一般化。extension = Ximg(χ)=X(θ_χ) を per-φ
  producer で全 χ に供給(中心 φ_θ で被覆)。出力 = `IsCoherent hyp.tau (Xset W2)` で `cX.ext(χ)=X(θ)`。
- **(S2) hmixed** = `⟨X(θ), cY.ext η⟩ = 0`(= per-φ producer の `hXaggorth`)で **済**(reducible+irreducible 一様)。
- **(S3) glue** = `coherentXunionYset_caseB_of_glued`(`S08_CaseBCoherence2:1616`)に (S1)cX + (S2)hmixed +
  diagonal D を渡し `IsCoherent hyp.tau (Xset W2 ∪ Y)` = seed → `nonempty_coherent_S_caseB` → S08:59。

**残務 = 純 assembly(新数学ゼロ。(6.8.2.3) hard math は per-φ producer に sorry-free 実在)**:
per-φ aggregation を全 X に展開(中心 φ_θ 被覆 + Classical.choose で Ximg) + cX 一般化 + glue 配線 + diagonal D。
⚠ **「user-managed ChatGPT gap」では無くなった**(hard math 済) — Lean assembly のみ。ただし大型 multi-step。
**↓ 以下 cont.⁴ は履歴 (point 3 canonical 説は上記で訂正済)。**

## 🔨 2026-06-18 cont.⁶ — (S1) 着手: 一般 per-member anchored image 着地 + cX 構成の分解

**✅ landed `caseB_member_anchored_image`** (`S08_CaseBAnchoredSeed.lean`, commit `dc94d1aa`,
sorry-free・axiom-clean): `caseB_column_anchored_image` を**任意 irreducible θ** (W₂ 上非定数 `hθne`
= `Ind^L_H θ∈X`) に一般化し、**seam 直交 `⟨X, η₁^{τ₁}⟩=0`** も同時出力
(`caseB_constituentDecomposition_X_orthogonal`)。出力 =
`∃ X a, (Ind θ)(1)=a·η₁(1) ∧ τ(Ind θ−a•η₁)=X−a•cY.ext η₁ ∧ ⟨X,cY.ext η₁⟩=0`。
**⟹ (6.8.2.3) hXanchored + hXmixed を全 χ∈X 一様に供給する基盤** (reducible column / irreducible 不問)。

**cX = `IsCoherent hyp.tau (Xset W2)` (extension=X(θ)) の構成 = 残 (S1) 本体。分解**:
- **(P1) scaled-diff 純代数** (trivial): 2 member の anchored image から `τ(χᵢ−d•χ₁)=Xᵢ−d•X₁`
  (η₁ 項相殺 ∵ `aᵢ=d·a₁`, d=χᵢ(1)/χ₁(1)∈ℕ ← H が p-group)。`caseB_member_anchored_image` ×2 + map_sub/nsmul。
- **(P2) scaled-diff span 特徴付け** (本命の work): `zSupportedSpan(Xset W2)` が `{χᵢ−dᵢ•χ₁}` で張られる。
  column 版 `mem_span_columnDiff_of_mem_zSupportedSpan`(`S06_CertainTypeCoherence:377`)は**等次数**ゆえ
  unscaled `μⱼ−μₖ`。Xset W2 は次数バラバラ ⟹ scaled 版要。S07 に汎用エンジン候補:
  `span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs`(`S07_Coherence:172`)・
  `coherentOfPairChainCover`(`:4841`、xChainCoherentW が使用)。

**✅ sub-question 精査済 (cont.⁶ 末尾、code-verified) — cont.⁵「canonical cX 説は誤り」は OVERSTATED と訂正**:

- **canonical column image は実は ⊥ Y**: `certainTypeExtension h (columnSum χ₂) = sign·Σᵢ certainTypeOmegaSigma`
  (`certainTypeExtension_columnSum` `S06_CertainTypeCoherence:113`)。そして **`inner_coherent_extension_
  certainTypeOmegaSigma_eq_zero`(`S08_CaseBCoherence2:1246`)が `⟨cY.ext η, certainTypeOmegaSigma⟩=0`
  を既に証明**(η∈coherent S₁, irreducible, η−η' supported)⟹ canonical column extension ⊥ Y は FREE。
  ∴ cont.⁵ の「canonical は hmixed を壊す」は誤り、**column については canonical も anchoredImages も両方 OK**。
- **⟹ cX 経路は CANONICAL xChainCoherentW が本命** (anchoredImages-cX + P2 自作 span は不要):
  cX = `xChainCoherentW`(certainTypeSet canonical base + irreducible pair chain)、varying-degree は
  chain が処理。per-step hstep = `XAdjoinStepInputW` は `caseB_member_orthoDatum`(`S08_CaseBEnumeration:336`、
  coupled D+hortho+htau1 既存)から組む(brick 2/3 の成果)。**cX は既存部品でほぼ組める**。
- **hmixed (seam) = case-split で証明** (coherentXunionYset_caseB_of_glued の hmixed):
  - **column χ∈certainTypeSet**: `inner_coherent_extension_certainTypeOmegaSigma_eq_zero` を Σ 展開で ⊥ Y。✅ 既存
  - **irreducible χ∈Xset W2**: Frobenius (6.8.1) `himg_ortho via (4.1)`(`S08_CoherenceCore:1424`,
    `inner_span_Xset_Yset_eq_zero_of_irreducible_X` `CorePart2:1573`)の **mixed-X 版インスタンス化**が要
    (all-irreducible 版は直接使えない)。← **唯一の非自明残**。
- **`caseB_member_anchored_image`(cont.⁶ 着地)の位置づけ**: anchoredImages-cX 路線の部品だが、canonical 路線が
  本命なら seed には不要。ただし (6.8.2.3) 自体の独立価値 + irreducible-seam を anchored image 経由で出す
  代替路にも使える(X(θ)⊥Y を直接持つ)。**廃棄せず保持**。

**▶ 次セッションの一手 = (1) hmixed の irreducible-χ 枝**(mixed-X 用 himg_ortho、(4.1)+supported-diff)
**→ (2) cX = xChainCoherentW の hstep assembly**(caseB_member_orthoDatum を XAdjoinStepInputW に昇格)
**→ (3) coherentXunionYset_caseB_of_glued 配線 + diagonal D**。canonical 路線で確定。P2 span 自作は不要。

## ✅✅✅ 2026-06-18 cont.⁷ — hmixed COMPLETE (両 seam + case-split assemble)、残 = cX + ν/D glue

cont.⁶ の (1) hmixed を**完全 assemble**。3 lemma 着地(全 `S08_CaseBAnchoredSeed.lean`、sorry-free・axiom-clean、
full build 3858 jobs green):
1. **`caseB_member_anchored_image`**(`dc94d1aa`)— (6.8.2.3) per-member anchored image + X(θ)⊥Y、任意 θ。
2. **`inner_extension_caseB_Xset_Yset_eq_zero_of_irreducible`**(`23272240`)— **irreducible-χ seam**
   `⟨cX.ext χ, cY.ext η⟩=0`。Frobenius `inner_extension_Xset_centralCommutator_Yset_eq_zero_general` の
   mixed-X 版だが all-X-irreducible 不要: 参照 χ'=χ̄(conj-closed + no-real)、source は hpair から
   `inner_eq_zero_of_mem_span_of_pairwise_orthogonal`、(4.1) signed-difference。**= 旧「唯一の非自明残」を解決**。
3. **`caseB_hmixed`**(`e3afb9de`)— glue `hmixed` を **cX + hcolAgree のみに gate**:
   X⊥Y(`caseB_Xset_orthogonal_Yset`)で両辺 0 → case-split(`caseB_S_member_column_or_irreducible`):
   column = `hcolAgree`(cX.ext μ_j=certainTypeExtension μ_j)+ 既存 column-Y seam
   `inner_certainTypeExtension_columnSum_coherentYset_extension_eq_zero`(`S08_CaseBCoherence2:1449`)、
   irreducible = #2。

**∴ hmixed 完成。残 2 ピース**:
- **(A) cX = `IsCoherent hyp.tau (Xset h46.W2)`** = `xChainCoherentW`(base=certainTypeSet canonical、
  cover=`caseB_Xset_conjugatePairCover` 既存)+ **per-step `hstep : XAdjoinStepInputW`**
  (`caseB_member_orthoDatum` `S08_CaseBEnumeration:341` が D+hortho+htau1 core 供給、残=全 field assemble =
  **大型 fresh effort**)。**未 instantiate**。**+ hcolAgree**(cX.ext(col)=certainTypeExtension(col)、chain が
  base 拡張保存 + congrMap extension 不変 ⟹ 成立のはず、要証明)。
- **(B) ν/D/hgen/hDτ glue 配線** = `coherentXunionYset_caseB_of_glued`(`S08_CaseBCoherence2:1616`)の
  combined map ν(cX|X + cY|Y glue)+ diagonal D。template=`coherentCertainTypeSet_union_Yset_via_anchoredImages`
  だが mixed-X 用に要調整(orthonormal glue は column 不可、線形独立 glue 要)。

**▶ 次の一手 = (A) cX 構成** → (B) glue → seed `IsCoherent (Xset W2∪Y)` → `nonempty_coherent_S_caseB`(既存)
→ S08:59。hmixed は `caseB_hmixed` で完成済。

## ⚠ 2026-06-18 cont.⁸ — cX 構成の真の scope 判明: (6.6) 重み付き X-coherence (大型 §6 math)

cX 構成を徹底精査(xChainCoherentW / XAdjoinStepInputW / Frobenius template / 既存 consumer 全調査)した
結論。**cont.⁷ の「残りは機械的 assembly」は楽観で訂正** — cX = (6.6) **重み付き X-coherence** で実質的な §6
degree theory を要する:

1. **重み付き chain consumer が未存在**: irreducible-X 版 `Xset_isCoherent_from_adjoinSteps_of_irreducible_X`
   (`S08_CoherenceCorePart2:4232`, hyp.tau bridge 内包) は **all-X-irreducible 前提**(`hX:∀φ∈Xset, irreducible`)
   ゆえ case-B(reducible column 含む)に直接不可。weighted `xChainCoherentW`(`S08_CoherenceWeighted:556`)は
   **dadeIntegralCharacterMap レベル**で、hyp.tau bridge を持たない。⟹ **新規 `Xset_isCoherent_from_adjoinStepsW`
   (weighted chain + certainTypeSet base + Dade→hyp.tau congr)を構築要**(irreducible 版を mirror、laborious)。
2. **per-step `hDeg : 2a < ∑ deg²/mc` = 真の gate = (6.6) degree-divisibility math**: Frobenius は
   `PairUnionCommonIndexPrimePowerStepData`(prime-power / common-index / [Is] Cor 2.30 central bound)で
   hDeg を構築。case-B はこの **weighted 版 producer (= notes/s08_6_8_blocker_central_Z.md の "producer monolith")**
   を要する。**これが (6.6) の数学的核**。brick 3 (`sMember_degreeSqNormBound`) は field assembly を済ませたが
   **Y-anchor 前提**(η∈S₁)で、X-chain は **column-anchor**(certainTypeSet 基準)ゆえ deg/a 定義が異なり直接再利用不可。
3. **hcolAgree**(cX.ext(col)=certainTypeExtension(col)): chain base 保存 + congrMap で成立のはず、要証明。

**∴ cX = 大型 multi-session §6 work**(weighted chain consumer + degree producer monolith + map congr)。
**機械的でない**。**(B) glue も mixed-X ν 構築要**。

> ### ✅ cont.⁹ 更新 (2026-06-18) — weighted chain consumer DONE、map congr は不要だった
> **`caseB_Xset_isCoherent_of_hstepW`**(`S08_CaseBAnchoredSeed.lean`, commit `804fbfe1`, sorry-free・
> axiom-clean): cX を **per-step `hstep` (XAdjoinStepInputW) のみに gate** する chain consumer。
> 🔑 **cont.⁸ の「map congr monolith 要」は誤り**: `hyp.tau = dadeIntegralCharacterMap hyp.dade
> (hyp.dade.fullDadeIsometryData hyp.hconj)` が **defeq** ゆえ `xChainCoherentW hyp.dade hyp.hconj` が
> hyp.tau に直接 land(retarget 不要)、base `certainTypeSet_isCoherent_tau_canonical` も defeq 一致。
> 上記 #1「新規 chain consumer 構築」= **完了**(thin wrapper だった)。
> **∴ cX 残務 = per-step `hstep` (= XAdjoinStepInputW producer) のみ** = (6.6) degree producer monolith。
> core field (Dmem/hortho/htau1) = `caseB_member_orthoDatum` 既存。真の gate = **hDeg `2a < ∑ deg²/mc`**
> (=(6.6) degree-divisibility、Frobenius `commonIndexPrimePowerSums` の weighted 版)+ field assembly
> (brick 3 `sMember_degreeSqNormBound` を **column-anchor** 用に翻案、brick 3 は Y-anchor 前提ゆえ要 adapt)。

## 🔄 2026-06-18 cont.¹⁰ — ARCHITECTURE 訂正: separate-cX 路線は非可能、seed は chain-onto-(certainTypeSet∪Y)

**重大訂正**: cont.⁹ の「cX(=X-coherence 単独)を weighted chain で構築」は **非可能**と判明。
`XAdjoinStepInputW` は accumulator に **norm-1 anchor**(`hanchorNorm : mc i₁=1`)を要求するが、
`certainTypeSet` は全 column が `‖μ_k‖²=|W₁|>1`(`S06_CertainTypeConjugation:270`)で **norm-1 member 皆無**
⟹ base=certainTypeSet の chain は **step 0 で hstep unsatisfiable**。`caseB_Xset_isCoherent_of_hstepW`
(commit `804fbfe1`)は sorry-free だが hstep discharge 不能(= [[scaffold-sorry-free-not-done]] の罠、
docstring に⚠明記済 `7f...`)。

**∴ separate-cX + glue 路線(`coherentXunionYset_caseB_of_glued`)は非可能** — cX(Xset W2 単独)が
weighted chain で組めない(norm-1 anchor 無し)。⟹ **`caseB_hmixed`(case-split glue hmixed)+ irreducible
seam + base-certainTypeSet consumer は非可能路線の産物**(ただし下記参照で一部再利用可)。

**✅ VIABLE 路線 = seed を chain-onto-(certainTypeSet∪Y) で直接構築**:
- base = **`certainTypeSet ∪ Y` coherence**(Y-anchor `η`, `‖η‖²=1`)= anchoredImages
  (`coherentCertainTypeSet_union_Yset_via_anchoredImages`、∀-column hXanchored を `caseB_member_anchored_image`
  から供給)。
- weighted chain `xChainCoherentW` を base=certainTypeSet∪Y / X-target=`Xset W2 ∪ Y` / cover=irreducible
  X-pair に fold → **`IsCoherent (Xset W2∪Y)` = seed を直接構築**(separate cX + glue 不要)。
- anchor=η(Y, norm 1)ゆえ **brick 3 `sMember_degreeSqNormBound` の field assembly が直接再利用可**
  (Y-anchor 前提が合致)。X⊥Y seam は **in-chain `hortho_mem`** で処理。
- 真の gate = **hDeg `2a < ∑ deg²/mc`**(=(6.6) degree inequality、不変)。

**再利用可否**: `caseB_member_anchored_image` = 再利用(base 供給)。`caseB_hmixed`/irreducible seam/
base-certainTypeSet consumer = 非可能路線、ただし map-convention fact + wrapper 構造 + seam の数学は
corrected base で部分再利用可。**▶ 次 = seed-chain-onto-(certainTypeSet∪Y) を組む**(base anchoredImages
+ chain hstep brick-3 再利用 + hDeg)。

**FT 文脈**: (6.8) は [[ft-path-policy]] で **FT carrier から orphaned (deferred-payoff)** — cX を完成しても
feitThompson の sorry は今は減らない。⟹ cX 着手は「(6.8) を完全に閉じる」価値 vs 「§14 counting (lane-H) 等
on-path piece」の優先度判断を要する。**本セッションの確実な成果 = hmixed 完成**(seam という長年の難所)。
cX(=degree theory)は別 effort として scope。

## 🗂 (履歴・訂正済) 2026-06-18 cont.⁴ — anchoredImages route の必要性に疑問

> ⚠ 本 block の疑問は cont.⁵ で解決済 (anchoredImages = ON-PATH/CORE)。point 3「canonical cX」は誤りと判明。

**cont.³ で組んだ anchoredImages route (hXanchored, `S08_CaseBAnchoredSeed.lean` 8 commit) が seed の
critical path 上か不確実と判明**。記憶 [[pf-s08-caseb-seed-route-uncertain]] が正本。要点:

1. **certainTypeSet coherence は既に FREE**: `certainTypeSet_isCoherent_tau_canonical`(`S08_CaseBAssembly:170`)
   UNCONDITIONAL・sorry-free。anchoredImages はこの同じ集合を Ximg 拡張で別構成しているだけ。
2. **endgame seed = 全 X-set** `IsCoherent (Xset h46.W2 ∪ Yset)`。anchoredImages の
   `coherentCertainTypeSet_union_Yset_via_anchoredImages` は `certainTypeSet ∪ Y`(1 次数列 ⊊ Xset W2、
   `certainTypeSet_subset_Xset` `S08_CaseBCoherence2:2069`)⟹ **seed に不足**。
3. **実 cX = `xChainCoherentW`**(`S08_CaseBEnumeration:120`: base S₀=certainTypeSet, X=Xset W2、base は
   canonical 使用 `S08_CoherenceWeighted:545`)= certainTypeSet (canonical free) + irreducible 対 chain。

**未解決の核心**: `coherentXunionYset_caseB_of_glued`(`S08_CaseBCoherence2:1616`)の **hmixed
(X-image ⊥ Y-image = seam 直交)** を canonical certainTypeSet 拡張が満たすか? **満たせば anchoredImages 不要**
(残務 = canonical certainTypeSet + irreducible xChain → cX → Y-glue)。満たさねば私の Ximg 直交拡張が seam に必要
(ただし全 Xset W2 を Ximg 化要)。⚠ roadmap 旧記述「hXanchored = 唯一の gate」は session-48 anchoredImages 由来で
現 codebase (canonical+xChain) と乖離の疑い。**次の一手 = anchoredImages を盲目継続せず、まず hmixed が
canonical 拡張で成立するか精査 → route 確定**。cont.³ の 8 commit は全 sorry-free・健全(中心指標等は汎用 §6 事実)
だが seed 未 close。

## 🔨🔨🔨 2026-06-18 cont.³ — hXanchored: ALL hard math done (core+cY-unif+R1+R2) (自走)

`S08_CaseBAnchoredSeed.lean` に着地した順に(全 build-green 3629 jobs・axiom-clean):
1. **`exists_central_phi_data`** — per-θ 中心線形指標 φ_θ([Is] 2.27)を **両形式**(compHom e φ on
   W₂.subgroupOf H = producer 用 / φ on W₂ = aggregate 用)+ linearity + positivity + **master
   restriction eq** `Res θ = θ(1)·(compHom e φ)` で出力。
2. **`compHom_phi_ne_trivial_of_restrict`** — restriction eq + (∃w, θ(w)≠θ(1)) ⟹ φ_θ ≠ 1。
3. **`caseB_column_anchored_image`**(★ core integration)— certain-type column χ₂(θ=Res_H μ_{0,χ₂}
   が W₂ 上非自明 hWne + |𝒴|≠2 hYcard)について `τ(columnSum χ₂ − a•η₁) = X − a•hyp.coherentYset.ext η₁`
   (a=θ(1))。全 block を wiring: exists_central_phi_data → exists_decomposition_caseB_coherentYset →
   caseB_hnonlin/hcol/hirr/hirrAnc → caseB_per_phi_anchored_fromYset → columnSum_eq_induce_H。
4. **`exists_decomposition_caseB_coherentYset`**(cY-uniformity)— (6.8.2.2) aggregate を **canonical
   `hyp.coherentYset`** に対して出力(opaque existential cY でない)。good case の `coeff_eq_neg_or_edge_caseB`
   witness が hyp.coherentYset そのもの、edge は |𝒴|=2 ゆえ hYcard で排除。**⟹ ∀-column が単一 anchor 共有**。

**🎯🎯 全ハード math 解決**: central gap(#1)・core integration(#3)・cY-uniformity(#4)・**(R1) §6
中心指標非自明性**・**(R2) degree 関係**。commits: `b4820084`/`d2f2ddb6`(#1)/`a5736e47`(#2,#3)/
`d9e2c246`(#4)/`cdb98ca7`(R1)/`0b0e25ee`(R2)。

**✅ (R1) 解決(rabbit-hole でなかった)**: `caseB_column_W2_nonconstant`(χ₂≠1 ⟹ ∃w∈W₂.subgroupOf H,
θ(w)≠θ(1))= Pf (4.7) `Hypothesis.not_subset_characterKernel_chiRestrict_of_ne_one`(W₂⊄ker chiRestrict)
を K=H で existential 形に repack(値は L-レベル μ_{0,χ₂} に落として K↔H dependent-transport 回避)。
**⟹ `caseB_column_anchored_image` は今 `hχ₂ : χ₂ ≠ 1` を直接取る**(hWne を内部導出)。
**✅ (R2) 解決**: per-column lemma が degree 関係 `columnSum χ₂(1) = (a:ℂ)·η₁(1)`(a=θ(1))も出力
(induce_apply_one + index_H_eq_card_W1 + constituentWeight_eq_apply_one)。

**現 per-column lemma `caseB_column_anchored_image`**(完成形): χ₂≠1 + |𝒴|≠2 ⟹
`∃ X a, (columnSum χ₂(1) = a·η₁(1)) ∧ τ(columnSum χ₂ − a•η₁) = X − a•hyp.coherentYset.ext η₁`。

**▶ 残 = (6.8.2.3) seed 組立(機械的・math gate なし)**:
- **(R3) certainTypeSet coherence** = `certainTypeSet_isCoherent_via_anchoredImages`(`S08_CaseBXChiCoherence:246`)
  に 3 obligation 供給:
  - **hXanchored**(∀-column): membership `columnSum χ₂∈certainTypeSet h46 k`(= ∃χ₂'≠1 degree-match ∧
    columnSum χ₂=columnSum χ₂')展開 → per-column lemma を χ₂' に適用 → degree-match で a=a₀(均一)を導出。
    **Ximg χ₂ := Classical.choose**(membership witness χ₂' → per-column X)。a₀=参照列 k の θ(1)。
  - **hXinner**(★ 新認識の obligation): `∀χ₂χ₂', inner(Ximg χ₂)(Ximg χ₂') = inner(columnSum χ₂)(columnSum χ₂')`
    = **Ximg の等長性(cross-column 内積保存)**。`ind_cross_inner_eq_zero`(`S06_CertainTypeCharacters:448`、
    χ₂≠χ₂' で直交)+ within-column(Dade 等長)で。中規模。
  - **hXzirr**: `Ximg χ₂ ∈ ZIrr`(= `(caseB_phi_family …).X` は Dade image、容易)。
- **(R4) seed 配線**: certainTypeSet coherence →(irreducible-X chain `xChainCoherent` と glue)→ cX
  (`IsCoherent (Xset W₂)`)→ `coherentXunionYset_caseB_of_glued` → hXYcoh → `nonempty_coherent_S_caseB`
  (brick 4.4)→ S08:59。**この cX glue(certainTypeSet ⊔ irreducible-X = Xset W₂)も中規模 assembly**。
**正本 leaf = `S08_CaseBAnchoredSeed.lean`。次の一手 = (R3) ∀-column hXanchored + hXinner(Ximg 等長)。**
**⚠ math gate は全消滅**(R1-R2 で);残は choice-Ximg + 等長 + seed glue の機械的 wiring。

## 🔨 2026-06-18 cont.² — hXanchored 着手: central-char bridge 完成 + integration マップ確定

**新 leaf `S08_CaseBAnchoredSeed.lean`**(commits `cf736ef5`→`b4820084`、build-green 3629 jobs・axiom-clean):
- **`exists_central_phi_data`**(= Q1「中心 gap」解決): 任意 irreducible θ of H (W₂≤Z(H)) について、θ の
  中心線形指標 φ_θ([Is] 2.27 `exists_central_linear_restriction`、`Res^H_{W₂} θ = θ(1)·φ_θ`)を
  `subgroupOfEquivOfLe` で L-部分群 W₂ に transport し、**両形式 + linearity + positivity** を出す:
  (i) `hφ' : IsIrreducibleCharacter (compHom e φ)`(W₂.subgroupOf H 上 = producer 用)、
  (ii) `IsIrreducibleCharacter φ`(W₂ 上 = aggregate 用、`compHom_of_surjective`)、(iii) `φ 1 = 1`、
  (iv) `0 < constituentWeight hφ' θ`(= θ(1))。**fixed-φ 誤読を解消**: 各 column の θ は**自分の** φ_θ に乗る。

**🔑 integration の全 building block が実在・sorry-free と確認**(再調査不要):
- aggregate (6.8.2.2): `SibleyDadeHypothesis.exists_decomposition_caseB`(`S08_CaseBCoherence2:126`)。
  入力 = hcop/hp/**hHp(IsPGroup p ↥H = (6.5)還元)**/hprime/hW2comm/hW2cen/hη₁/**φ:IrreducibleCharacter ↥W₂**/
  hφ1/hφ(≠1)/hc2/hFPF。出力 = `∃ cY X, X⊥Y ∧ X∈ZIrr ∧ τ(Ind φ − |H:W₂|•η₁) = X − |H:W₂|•cY.ext η₁`。
- bundles: `caseB_hcol`(`S08CBA:986`)・`caseB_hirr`(`:1010`、要 `caseB_hnonlin` `:719`)・
  `caseB_hirrAnc`(`:757`)。per-φ anchored producer: `caseB_per_phi_anchored_fromYset`(`S08CBA:1647`、sorry-free)。
- column→θ: `columnSum_eq_induce_H`(θ=Res_H μ_{0,χ₂})・`certainTypeRestrict_isIrreducible`。
  column degree: `columnSum_apply_one`(`S06_CertainTypeCoherence:278`)。

**🛑 残 integration の核心 subtlety = cY-anchor consistency**(数学 gap でなく Lean 設計判断):
- `certainTypeSet_isCoherent_via_anchoredImages`(`S08_CaseBXChiCoherence:246`)の hXanchored は anchor を
  **`hyp.coherentYset.extension η₁` に hardcode**。一方 producer `caseB_per_phi_anchored_fromYset` は
  parametric cY を取り `… − a•cY.ext η₁` を出す。
- `exists_decomposition_caseB` は cY を **existential** で返す ⟹ producer に渡す cY が `hyp.coherentYset` と
  一致する保証が項レベルで取れない。**ただし** `exists_Ycoherence_hgood_caseB`(`S08_CaseBCoherence:1309`)の
  **good case は cY = `hyp.coherentYset`**(`:1341`)、m=2 edge case のみ別 cY(η₂ relabel, `:1342+`)。
- ⟹ 選択肢: (A) seed lemma `certainTypeSet_isCoherent_via_anchoredImages` の anchor を**parametric cY 化**
  (hyp.coherentYset hardcode を外す) → producer の cY をそのまま使える / (B) good-case cY=hyp.coherentYset を
  existential から露出する variant を作る + m=2 edge を別処理。**(A) が clean**(seed lemma の小改修)。
- 他の残: per-column で Ximg χ₂ := `(caseB_phi_family … φ_{χ₂} …).X` を定義、a₀ uniform = θ(1)(certainTypeSet
  equal-degree)、∀-column 組立、φ≠1 nontriviality(column の W₂⊄ker θ から)、m=2 edge。

**▶ 次の一手**: (1) cY-anchor を (A) で解決(seed lemma parametric 化)→ (2) per-column anchored image
`caseB_column_anchored_image`(exists_central_phi_data + exists_decomposition_caseB + caseB_hcol/hirr/hirrAnc
+ caseB_per_phi_anchored_fromYset)→ (3) ∀-column hXanchored + Ximg 定義 → (4) seed cX→hXYcoh→endgame。
**ChatGPT 不要**(全 block 実在、Q1-Q3 = `s08_6_8_chatgpt_answer.md` で math 健全確認済、残は wiring + (A) 設計)。

## ✅ 2026-06-18 cont. — brick 4.4 consumer producer skeleton landed → loop STOP @ hXanchored

**`nonempty_coherent_S_caseB` 完成**(`S08_CaseBWeightedEndgame`、commit `089b4033`、build-green
3631 jobs・axiom-clean `[propext, Classical.choice, Quot.sound]`)= case-(B) (6.8.3) 矛盾の
**producer (正) 形**。`by_contra` + `false_of_coherentXunionYset_caseB_of_not_coherentS` で
「seed `hXYcoh` + 構造データ (hW2cen/hcZ/hfpf) ⟹ `Nonempty (IsCoherent hyp.tau hyp.S …)`」。
case-(A) producer `nonempty_coherent_S_caseA_of_frobenius` の正確な mirror(ただし case-A は seed を
inline 構成、case-B は seed を hypothesis 化 = §6 `hXanchored` gate ゆえ)。

**⟹ brick 4.4 の loop で閉じられる側(consumer skeleton)は landed。** S08:59 の case-(B) 枝は
`nonempty_coherent_S_caseB hyp h46 hHK hW1 hW2cen hcZ hfpf (seed)` 一発に reduce 済(seed 構成だけが残)。

**🛑 LOOP STOP に到達**(LAUNCH stop-when 通り): 残る唯一の gate = `hXYcoh` seed 構成
(`coherentXunionYset_caseB_of_glued` の `hXanchored`、§6 certain-type structure theory)=
**ユーザー直接管理ゆえ loop では閉じない**。⚠ [[scaffold-sorry-free-not-done]]: producer は sorry-free
でも (6.8) は **done でない**(seed = hXanchored が未構成のまま)。S08:59 は依然 bare sorry。
- **残務(loop 外、要ユーザー判断 or 司令塔指示)**: (1) hXanchored 構成(§6、ユーザー管理) →
  (2) hfpf を `caseB_fpf_bound`(`CaseBEndgame:338`、`cert` 取る)から導出 = h46↔cert reconcile +
  `.index = Nat.card (↥H ⧸ …)` 同定 → (3) S08:59 で `hyp.cases.inr` から h46/cert 抽出 +
  `eq_bot_or_eq_of_le_of_card_prime`(`CorePart1:3354`) math-A/B 分岐 + case-B 枝 producer 呼出。
- **代替(LAUNCH 許容)**: endpoint A が STOP ⟹ endpoint B/C/D/E signature pin へ並列切替も可
  (ただし [[ft-path-policy]]: S15/S16 の ω/μ/ν/τ₃ は free field で現状 orphaned consumer 0)。

## ✅✅✅✅ 2026-06-18 セッション更新 — brick 4 endgame COMPLETE (case-B (6.8.3) 矛盾)

**`false_of_coherentXunionYset_caseB_of_not_coherentS` 完成**(`S08_CaseBWeightedEndgame`、commit
`277f3013`、build-green・axiom-clean・sorry-free、full build 3851 jobs/3.66s)= **case-B (6.8.3) の
矛盾** 「X(W₂)∪Y coherent ∧ S not coherent ⟹ False」。これで brick 4 chain (4.1→4.2→4.3) 完結。

**着地した brick 4 結果**(`S08_CaseBWeightedEndgame`、すべて axiom-clean):
1. **`sum_re_div_normSq_Xset_eq`**(4.1)= weighted Xset 恒等式 `∑_{X(Z)} (χ1).re²/‖χ‖² = |L:H|·(|H|-|H:Z|)`。
2. **`xSum_le_two_psi_caseB`**(4.2)= bridge(任意 S₁ ⊇ Xset W2、`Xdiff⊆Xset W2⊆S₁`)。
3. **`S_hasNoRealCharacters_caseB`** = `Xset_hasNoRealCharacters_caseB` の S-level 版(break extractor 用)。
4. **`false_of_coherentXunionYset_caseB_of_not_coherentS`**(4.3 endgame)= 上記 + `exists_coherentBreakPair_general`
   + ψ-irreducibility 導出 + Cor 2.30 (`degree_sq_le_index_of_central_quotient`) + `false_of_w2_break_arith`。

**🔑 (a)(b) 両 gate を解除した知見**(2026-06-17 の「gate 近傍」懸念は杞憂と確定):
- **(a) general S₁**: chain 全体(`caseB_S_pairwise_orthogonal`/enumerator/breakChar/brick3/bridge)を
  **任意 conj-closed coherent S₁ ⊆ S** に in-place 一般化(commit `de9f2054`、net −52行=general 版は簡潔)。
  per-member dispatch は S-level ゆえ機械的だった。
- **(b) break char irreducible**: `columnSum_mem_S` + `columnSum_notMem_SsubFiltration`(両形式化済)で
  **column ∈ X(W₂) ⊆ S₁** ⟹ break char ψ∈S\S₁ は column 不可 ⟹ irreducible。endgame 内の小補題で導出。

**▶ 残 = brick 4.4 = `S08_CoherenceTheorems:59` c2-math-B dispatch**(endgame を消費):
endgame は hypothesis で取る `hXYcoh`(X∪Y seed coherence)・`hfpf`((2|W₁|+1)²≤|H:W₂|)・`hW2cen`(W₂ 中心)・
`hcZ`(2≤|W₂|)を S08:59 で供給:
- **hXYcoh の構成** = `coherentXunionYset_caseB_of_glued`(`CaseBCoherence2:1616`)で X(h46.W2)∪Y coherence
  を組む。ここで **`hXanchored`(§6 certain-type structure theory gap)= ユーザー直接管理 gate**。
- **hfpf** = `caseB_fpf_bound`(`CaseBEndgame:338`)。⚠ これは `cert : CertainTypeHypothesis`(h46 でない)
  を取る → h46 ↔ cert の reconcile 要(または cert を `hyp.cases.inr` から直接取得)。hW2cen/hcZ も同源。
- dispatch = `eq_bot_or_eq_of_le_of_card_prime`(`CorePart1:3354`)で math-A/math-B 分岐、math-B 枝で endgame。
endgame 自体は閉じた(seed を hypothesis 化)ので、残務は **seed 構成(gate)+ FPF data 配線**のみ。

## ✅✅✅ 2026-06-17 セッション更新 — brick 3 COMPLETE (norm-weighted member-family bound)

**3 結果着地** (`S08_CaseBEnumeration.lean`、全 build-green、axiom-clean
`[propext, Classical.choice, Quot.sound]`、full build 3850 jobs/78s):

1. **`caseB_breakChar_fields`** — break-character ψ の 8 fact(`sBreakPair_fields` の case-B 類似)。
   非実性(`caseB_irr_nonreal`)・self/cross Kronecker(`irreducibleCharacter_inner_eq_ite` +
   `caseB_irr_conj_inner`)・conj-diff 支持(`caseB_irr_conj_diff_support`)・**ψ⊥S₁/ψ̄⊥S₁**。
   case-B 固有点 = S₁ が reducible column を含むので column への直交は degree-mod|W₁|
   (`caseB_inner_irr_columnSum_eq_zero`)、irreducible への直交は Kronecker で dispatch。
2. **`sMember_degreeSqNormBound_of_not_coherent`**(brick 3 core)= weighted degree-ratio bound
   `∑ⱼ (degⱼ)²/mcⱼ ≤ 2a`。enumerator(brick 2 `exists_sMemberOrthogonalFamilyW`)+ per-member
   coupled datum(`caseB_member_orthoDatum`)+ degree data(`sMember_charValue_one_eq_mul_anchor`)+
   break fields + 生成 bridge(`…_scaledDiffs`/`…_anchorGeneration`)を組んで engine
   `coherentDegreeSqNormBound_of_not_coherentW` に投入。**anchor `i₁` = Yset member**(`Yset_apply_one`
   で degree |W₁|、irreducible ゆえ `mc i₁=1`)。
3. **`sMember_degreeSqNormReBound_of_not_coherent`**(real-part scaling)= `∑ⱼ (χⱼ(1).re)²/mcⱼ ≤
   2ψ(1).re·η(1).re`(`sMember_degreeSqReBound_of_not_coherent` mirror、anchor degree |W₁| で rescale)。

**実装で確定した知見(再調査不要)**:
- `hψeq : ψ = induce H θ`(S_eq の等式は χ=induce、左辺 χ)→ 内在 fact は `rw [hψeq]`、`hψirr' := hψeq ▸ hψirr`。
- anchor の ZIrr(`htau1ψ`)は `scaledDiff_dadeImage_mem_ZIrr (χ₁ := ⟨χmem i₁, hanchorIrr⟩)` で
  **anchor を直接 IrreducibleCharacter 化**(η 経由の `rw [hi₁eq]` は motive-not-type-correct で失敗)。
- brick 2 enumerator の Gram は `instDecidableEqFin`、engine は `Classical.propDecidable` → engine の
  `hmemortho` 引数は `by rw [hmemortho i j]; rcases eq_or_ne i j with h | h <;> simp [h]` で正規化(template 流)。
- `exists_sMemberOrthogonalFamilyW`/`caseB_breakChar_fields` は plain `S08` namespace ゆえ **dot 記法不可**
  (`exists_sMemberOrthogonalFamilyW hyp …`)。`hyp.sMember_*`/`hyp.Yset_*` 等は SibleyDadeHypothesis method で dot 可。
- `hνZ`(member の coherent extension ∈ ZIrr)= `hS₁coh.extension_mem_ZIrr (χmem i) (Submodule.subset_span …)`
  (`IsCoherent` 構造体フィールド)。

### ▶▶ 次 = brick 4 = c2 endgame（**新 leaf 必須**、scope 確定 2026-06-17）

**⚠ leaf 配置**: `S08_CaseBEndgame.lean` は `S08_CaseBCoherence2` のみ import し **brick 3
(`S08_CaseBEnumeration`)を見ない**。brick 4 は `S08_CaseBEnumeration` + `S08_CaseBEndgame` 両方を
import する**新 leaf `S08_CaseBWeightedEndgame.lean`** に置く（FPF spine + brick 3 + X∪Y seed が揃う）。

unweighted endgame `false_of_coherentXunionYset_of_not_coherentS`(`CorePart2:3439`)+ `xSum_le_two_psi`
(`:3229`)を mirror。4 sub-piece:

1. ✅ **`sum_re_div_normSq_Xset_eq`**(commit `eae34b5c`、build-green・axiom-clean、`S08_CaseBWeightedEndgame`)=
   weighted Xset 恒等式 `∑_{X(Z)} (χ1).re²/(⟨χ,χ⟩).re = |L:H|·(|H|-|H:Z|)`、**case-B 仮説不要**。
   `sum_div_normSq_induce_kernelFilter_eq`(複素 `χ1²/⟨χ,χ⟩`)の A=⊥/A=Z 差 + 各 summand real 変換
   (`induce_apply_one` で degree、`inner_self_eq_realCast` で norm)。**実装罠**: `sum_div_normSq_…` 呼出は
   named-arg `(H:=H)` が instance 解決前に H を pin せず stuck → **`@` positional 形**(`@sum_div… ↥L _ _ _ H _ _ ⊥ _`)。
   ambient `[Invertible (Nat.card ↥H)]` は statement の `induce` 経由で auto-include 済 → **shadowing haveI 不可**
   (key の Finset が `this` を使い goal の ambient と不一致になる)。
2. ✅ **`xSum_le_two_psi_caseB`**(同 commit)= bridge `|L:H|·(|H|-|H:W₂|) ≤ 2ψ(1).re·η(1).re`。brick 3
   `sMember_degreeSqNormReBound` + (1) + `Xdiff ⊆ (range χmem).toFinset` + `sum_toFinset_range_eq` +
   nonneg `inner_self_re_nonneg`。**⚠ S₁ = X(W₂)∪Y 特化**(↓ (3) で general 化が必要)。
3. 🛑 **`false_of_coherentXunionYset_caseB_of_not_coherentS`**(endgame)— **2 構造要件が判明**
   (`:3439` の素朴 mirror は不可):
   - **(a) general S₁**: `exists_coherentBreakPair`(all-irr S 前提)は case-B で不可、`exists_coherentBreakPair_general`
     (`CorePart1:1035`)を使うが **S₁ ⊋ X(W₂)∪Y**(break は chain の最初の破綻点 = より大きい coherent S₁)。
     ⟹ brick 3 + (2) を **任意 conj-closed coherent S₁ ⊆ S**(anchor η∈Yset⊆S₁)に general 化要。
     per-member machinery(`caseB_member_orthoDatum`/`caseB_S_member_column_or_irreducible` dispatch)は
     **既に S-level で general** ゆえ機械的: general `caseB_S_pairwise_orthogonal`(X/Y-split を column/irr dispatch
     に置換)+ general enumerator(`exists_finEnum_general`)+ `caseB_breakChar_fields`/brick 3/bridge を S₁ 化。
   - **(b) irreducible break char**: weighted engine `coherentDegreeSqNormBound_of_not_coherentW` は
     **irreducible** な `χ : IrreducibleCharacter` を adjoin するが、case-B の conjugate-pair cover
     (`exists_conjugatePairCover_general`)は **reducible column pair {columnSum χ₂, columnSum χ₂⁻¹}** を
     pair しうる ⟹ break char が reducible なら engine 不適用。要解決: cover が reducible columns を **base S₀
     に押し込む**(= 全 reducible が X(W₂)∪Y 内)ことを示すか、reducible break を別処理。これは §6 certain-type
     structure(どの column がどの filtration 層か)に依存し **hXanchored gate 近傍**。
   discharge 先 = `hbreak : w1·hZ·(cZ-1) ≤ 2·w1²·d` 整形 → `false_of_caseB_break_of_bounds`
   (`CaseBEndgame:384`、proved)+ Cor 2.30 `d²≤|H:W₂|` + `caseB_fpf_bound`(`:338`)。
4. **`S08:59` c2-math-B dispatch**: X∪Y seed 構成(`coherentXunionYset_caseB_of_glued` `CaseBCoherence2:1616`)
   = `hXanchored` ユーザー管理 gate。
**▶ 次の具体手** = (3)(a) の general 化(brick 2/3/breakChar を S₁ パラメータ化、機械的)→ (3)(b) の cover 構造
精査(reducible break が起きるか)。(1)(2) は landed。

## ✅✅ 2026-06-17 セッション更新 — brick 2 COMPLETE (coupled producer + pairwise + enumerator)

**3 結果着地** (`S08_CaseBEnumeration.lean`、全 build-green 3629 jobs・axiom-clean、commits
`1faf9aec`/`9edad451`/`00450f56`):

1. **`caseB_member_orthoDatum`** (brick 2 core, the genuine hard core): per-member coupled datum
   producer. 入力 = member `x ∈ S₁`, 固定 break char `χ`(+ realness/`H^#`-support)+ member⊥break
   facts `hxχ`/`hxχbar`/`hxbarχ`/`hxbarχbar`。出力 = subtype `{ D : CharacterPsiDecomposition hyp.tau x 0
   // D.imageFamily.Orthogonal (R(χ)) ∧ D.tau1 x = hS₁coh.extension x }`。**= brick 1
   `caseB_member_psiDecomposition` を `hortho`+`htau1` で coupling した版**。
   - **🔑 設計確定 (workflow `scope:enum` agent と私が独立に同結論)**: engine の `Dmem`/`hortho_mem`/
     `htau1Dmem` は **coupled triple**(`hortho_mem` は `(Dmem i).imageFamily` についての主張)。brick 1 を
     black-box で `Dmem` に使い `hortho`/`htau1` を別途証明する経路は **失敗する**(column 枝の `hcol ▸`
     transport + `by_cases` が opaque 化し `htau1=rfl` と imageSet 同定を阻む)。**唯一の正解 = strategy (B):
     1 個の透明な `by_cases` で D・hortho・htau1 を同時生成**。これを実装したのが `caseB_member_orthoDatum`。
   - **`hortho` は ψ-依存だが ψ-universal でない**: column 枝 = `certainTypeR_imageSet_orthogonal_dadeOfDiff`
     (χ の realness/support のみ要、member⊥break 不要、V-vanishing)、irr 枝 =
     `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`(**member⊥break facts を消費**)。⟹ `hortho_mem`
     は **brick 3 で**(break ψ が判明し break⊥S₁ から member⊥break が出る所で)`caseB_member_orthoDatum`
     を呼んで作る。**roadmap 旧記述「brick 2 が hortho_mem を出す」は ψ-依存性ゆえ誤り、brick 3 の仕事**。

2. **`caseB_Sunion_pairwise_orthogonal`**: `X(W₂) ∪ Y` の相異 2 元は直交(weighted Gram off-diagonal)。
   6 case dispatch(`caseB_S_member_column_or_irreducible` で X-member を column/irr に割る): col⊥col
   (`inner_columnSum_cross_eq_zero`)/col⊥irr(`caseB_inner_irr_columnSum_eq_zero`, deg mod |W₁|)/irr⊥irr
   (Kronecker)/X⊥Y(`caseB_Xset_orthogonal_Yset`)/Y⊥Y、非対称順は conj 対称 `inner_conj_symm` で。

3. **`exists_sMemberOrthogonalFamilyW`** (brick 2, the ψ-independent enumerator): `S₁ = X(W₂) ∪ Y` を
   `exists_finEnum_general`(reducible 込み)で `χmem : Fin k → ClassFunction` に列挙 + `mc j =
   (⟨χmem j,χmem j⟩).re`(>0: col=|W₁|, irr=1)+ weighted Gram `⟨χmem i,χmem j⟩ = if i=j then (mc i:ℂ) else 0`
   (diagonal=`inner_self_eq_realCast`, off-diag=pairwise lemma)。**= engine の `χmem`/`mc`/`hmempos`/`hmemortho`
   block**。⚠ tactic 罠: `mc i` は `(fun j=>…) i` で未 beta — goal は `change` で reduce。column 自己 Gram は
   `columnFamily_mu_sum_inner h46 χ₂ χ₂` を hypothesis 化 → `simp only [← columnSum_def] at` で fold(forward
   `rw` は pattern 不一致)。

### ▶▶ 次 = brick 3 = `sMember_degreeSqNormBound_of_not_coherent`(weighted bound assembly)

unweighted テンプレート `sMember_degreeSumBound_of_not_coherent`(`CorePart2:2650`, 8 step)を mirror、step 8 で
engine `coherentDegreeSqNormBound_of_not_coherentW`(`S08_CoherenceWeighted:475`)。差分:
- **enumerator** = brick 2 `exists_sMemberOrthogonalFamilyW`(unweighted は `exists_sMemberOrthonormalFamily`)。
- **anchor** `i₁` = `Yset` member(degree |W₁| 全員、`Yset_apply_one`; irr `isIrreducibleCharacter_of_mem_Yset`;
  `mc i₁=1`)。`Yset` 非空 + `χmem i₁ ∈ Yset ∩ range` を locate。`ha1: deg i₁=1`。
- **degree data**: `sMember_charValue_one_eq_mul_anchor`/`sMember_scaledDiffSupport_of_charValue_eq` は
  `χ ∈ hyp.S`(ClassFunction)で述べられ ClassFunction-typed member にそのまま適用可(workflow `scope:assembly`
  確認)。`deg`/`hmemdegdiffsupp` を per-member で。
- **Dmem/hortho_mem/htau1Dmem** = per-member `caseB_member_orthoDatum hyp h46 hHK … χmem_i hνZ_i χ=ψ hrealψ
  hdiffsuppψ (member⊥break ×4)`。member⊥break ×4 は break-pair fields(`sBreakPair_fields` の weighted 類似 or
  break⊥S₁ + conj 対称 + member∈S₁)から。
- **break pair ψ**: `exists_coherentBreakPair` 系(ψ∉S₁, ψ̄∉S₁)。`hdiffasuppχ`/`htau1_memaχ` =
  `sMember_scaledDiffSupport_of_charValue_eq`/`scaledDiff_dadeImage_mem_ZIrr`。
- **hSgen/hgen** = `span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs` /
  `zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration`(weighting 非依存、verbatim 流用; workflow 確認)。
- 結論 = `∑ (deg j)²/mc j ≤ 2a`、real-part scaling で `∑ (χ(1).re)²/mc ≤ 2ψ(1)χ₁(1)`
  (`sMember_degreeSqReBound_of_not_coherent` mirror)。

その後 brick 4 = c2 endgame `false_of_coherentXunionYset_caseB_of_not_coherentS`(counting
`sum_div_normSq_induce_kernelFilter_eq` + FPF `false_of_caseB_break_of_bounds`)→ S08:59 の 3-way dispatch。
正本詳細 = この note 以下 + workflow `scope:assembly`/`scope:seed` result(transcript wulxxqn5y）。

## ✅ 2026-06-17 セッション更新 — brick 1 COMPLETE (`caseB_member_psiDecomposition`)

**brick 1 = 着地** (`S08_CaseBEnumeration.lean` 末尾、build-green 3628 jobs・axiom-clean `[propext,
Classical.choice, Quot.sound]`)。per-member Dmem dispatcher: `x ∈ S₁ ⊆ hyp.S`(conj-closed coherent)
→ `CharacterPsiDecomposition hyp.tau x 0`。

**実装で確定した roadmap 訂正 (6-agent workflow + 直接 grep で code-verified)**:
1. **classifier は `x ∈ hyp.S` を取る (S₁ でない)** — `caseB_S_member_column_or_irreducible`
   (`S08_CaseBAssembly:1949`) は S-level。brick 1 は `hS₁sub : S₁ ⊆ hyp.S` で橋渡し。
2. **irreducible 枝の facts は `caseB_irr_*` (induce-θ 形) を使う。`xMember_*_of_irreducible_X` は NG** —
   後者は `hX : ∀ φ ∈ Xset Z, IsIrreducibleCharacter φ`(Xset 全 irreducible)を要求するが case-B は
   まさに X が reducible column を含むケースゆえ偽。正しい供給源:
   - hreal = `caseB_irr_nonreal hyp hirr`(`S08_CaseBAssembly:578`、奇位数 Burnside)
   - hdiffsupp = `caseB_irr_conj_diff_support hyp θ`(`S08_CaseBAssembly`)
   - hχχbar = `caseB_irr_conj_inner hyp hirr`(`S08_CaseBAssembly`)
   - column hagree = `caseB_column_mapagree hyp h46 hχ₂`(`:194`、roadmap 既述通り)
   - column hdeg = `(columnSum_inv_apply_one h46 χ₂).symm`、hdiffsupported = `columnDiff_support_subset`
     + `mem_zSupportedSpan_iff`。
3. **Type-vs-Prop 消去の罠 (再調査不要)**: 出力 `CharacterPsiDecomposition` は `Type`。`x ∈ S` の
   `∃`、dispatch の `∨` は `Prop` ⟹ `obtain`/`rcases` で `Type` goal に消去できない
   (`Exists.casesOn can only eliminate into Prop`)。対処:
   - column index χ₂ は `by_cases hcolumn : ∃ χ₂, …` + `hcolumn.choose`/`.choose_spec`(noncomputable
     関数、Type 消去可)。
   - irreducible 判定は `(caseB_S_member_column_or_irreducible …).resolve_left hcolumn`(Prop→Prop)。
   - inducing source θ は **top で抽出しない**(`set θ := choose` は x への循環依存を作り
     `rw [← hcol]`/`rw [hxeq]` が「revert dependencies」で失敗)。irreducible facts は各々 `Prop`-have
     内で `obtain ⟨θ, _, hxeq⟩ := (hxS の S_eq 展開)` → `rw [hxeq]`(θ は fresh、循環なし)。
   - column 主 goal の `columnSum χ₂ → x` 変換は `hcol ▸ (term)`(term-level、循環なし。`rw [← hcol]`
     は χ₂ が x 依存ゆえ NG)。
4. memberExtensionDecomposition は **x をそのまま** χ:=⟨x,hirrx⟩ で渡せる(induce 形不要)。返り値
   `CharacterPsiDecomposition (dade…) x 0` は `hyp.tau` abbrev と defeq ⟹ 変換不要。

## ✅ brick 2a COMPLETE + brick 2/3 詳細設計 (2026-06-17, 3-agent scope workflow code-verified)

**✅ brick 2a = `exists_finEnum_general`**(`S08_CaseBEnumeration.lean`、build-green・axiom-clean)。
一般有限集合 `S : Set (ClassFunction Γ ℂ)` を injective `Fin k`-family に列挙(irreducible 不要)。
= `Set.Finite.fintype` + `Fintype.equivFin` の純 formalization(数学ゼロ)。reducible column を含む
case-B coherent set の列挙プリミティブ。`exists_finEnum_irreducible`(`CorePart1:631`)の一般版。

### brick 2 full = weighted enumerator(次の大物、multi-hundred LOC)

unweighted テンプレート = **`sMember_degreeSumBound_of_not_coherent`**(`CorePart2:2650`、8 step)。
weighted 版 brick 3 = `sMember_degreeSqNormBound_of_not_coherent` はこれを mirror し step 8 で
weighted engine `coherentDegreeSqNormBound_of_not_coherentW`(`S08_CoherenceWeighted:475`、結論
`∑ deg²/mc ≤ 2a`)を叩く。**step 1-7 は generic(orthonormality 非依存)= unweighted をほぼコピー**。

weighted engine が unweighted と異なり要求する **NEW 4 inputs**(= brick 2 が供給):
- **`mc : Fin k → ℝ`** = `(⟨χmem i, χmem i⟩).re`。column = **|W₁|**(`columnFamily_mu_sum_inner`
  `S06_CertainTypeIsometry:1094` = `if χ₂=χ₂' then |W₁| else 0`)、irreducible = **1**。
  `hmempos`(全 > 0)、**`hanchorNorm : mc i₁ = 1`** ⟹ **anchor は irreducible で取る**
  (= Yset メンバー、`isIrreducibleCharacter_of_mem_Yset` + degree |W₁| `Yset_apply_one`。
  reducible column を anchor にしてはいけない)。
- **`Dmem`** = brick 1 `caseB_member_psiDecomposition`(✅ DONE)。
- **`hortho_mem : ∀ i, (Dmem i).imageFamily.Orthogonal (dadeOrthonormalCharacterImageFamilyOfDiff … ψ)`**
  = column は `certainTypeR_imageSet_orthogonal_dadeOfDiff`(`S08_CaseBHortho:44`)、
  irreducible は `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`(`CorePart1:1681`)。
- **`htau1Dmem : ∀ i, (Dmem i).tau1 (χmem i) = hS₁.extension (χmem i)`** = 両 producer とも
  tau1 = `hS₁.extension` ゆえ **rfl**。

**`hmemortho`**(`∀ i j, ⟨χmem i, χmem j⟩ = if i=j then mc i else 0`)の組立 = 全 per-pair 補題実在:
col-col 直交=`inner_columnSum_cross_eq_zero`(`CaseBAssembly:1850`)/col self=上記 Gram/
col-irr=`caseB_inner_irr_columnSum_eq_zero`(`:1801`)+ conj `:1875`/irr-irr=`irreducibleCharacter_inner_eq_ite`/
col-Y=`inner_columnSum_Yset_eq_zero`(`:250`)/irr-Y=`inner_irr_Yset_eq_zero`(`:611`)。
**統合済 X⊥Y = `caseB_Xset_orthogonal_Yset`(`CaseBAssembly:1970`)**。member を column/irr で dispatch して組む。

### brick 2/3 推奨着手順
1. brick 2 enumerator: `exists_finEnum_general` で S₁=X∪Y を列挙 → 各 member に brick 1 で Dmem、
   `mc` を `⟨χmem i,χmem i⟩.re` で定義、`hmemortho` を per-pair dispatch で組む、anchor を Yset から取る。
2. brick 3: unweighted `sMember_degreeSumBound_of_not_coherent` の step 1-7 をコピー、step 8 で
   weighted engine、最後に real-part scaling(`sMember_degreeSqReBound_of_not_coherent` `CorePart2:2738` mirror)。
3. brick 4 = c2 endgame `false_of_coherentXunionYset_caseB_of_not_coherentS`(weighted+FPF mirror)
   → S08:59 の 3-way dispatch。
**正本詳細 = この note + scope workflow result(transcript)。再調査不要: enum/orthogonality 在庫は full。**

## 結論 (一言)

bootstrap 経路は **viable**。`gap_resolution` note の「残務 = glue のみ」は誤りだが、Plan agent の
「(6.5) p-group reduction 未形式化で blocked」**も誤り**。真の残作業は **hard core 1 本 + wiring**:

- **HARD CORE (genuine new math, 未実装)**: `sMember_degreeSqNormBound_of_not_coherent` =
  **reducible 込みの重み付き member-family を break pair から列挙する補題**。unweighted 版
  `sMember_degreeSqReBound_of_not_coherent`(`S08_CoherenceCorePart2:2738`)の重み付き類似。
  これを `xSum_le_two_psi_caseB` → c2 endgame `false_of_coherentXunionYset_caseB_of_not_coherentS` に積む。
  **scope = multi-session 見込み**(unweighted 版が辿った鎖を重み付きで再構築)。
- **それ以外はすべて wiring(既存 green 補題)**。

## S08:59 discharge の構造 (3-way dispatch)

`hyp.cases : Frobenius ∨ ∃ h46 (c2 conditions)`(`S08_CoherenceCorePart1:3321`)で分岐:

1. **Frobenius 枝 (c1)** — **ほぼ完成**。`nonempty_coherent_S_caseA_of_frobenius`
   (`S08_CoherenceCore:3813`)が完全証明済(IsPGroup は内部導出: bound `CorePart2:3828` +
   `isPGroup_of_isFrobeniusGroup_of_card_le` `CorePart1:3120`)。署名 = `(hyp) [H.Normal] (hF)
   (hHnonab : commutator ↥H ≠ ⊥) {p} (hp) (hp3 : 3≤p) (hHp : IsPGroup p ↥H)`。
   ⟹ S08:59 で wiring するには `hHnonab` と `(p, hp, hp3, hHp)` を供給。
   - `hHnonab` = `commutator ↥H ≠ ⊥`: X-nonempty 枝条件 `hyp.Xset ⁅H,H⁆ ≠ ∅`(abelian 枝は既に処理済)
     から出るはず。要 helper(`Xset ⁅H,H⁆ ≠ ∅ → commutator ↥H ≠ ⊥`)or 既存補題確認。
   - `(p, hp, hp3, hHp)`: `isPGroup_of_isFrobeniusGroup_of_card_le hF …` で `∃ p, IsPGroup p ↥H`、
     `three_le_prime_of_isPGroup_of_odd`(`CorePart1:1330`)で `3≤p`。bound 導出は `CorePart2:3828` を参照。
     ※ `nonempty_coherent_S_caseA_of_card_of_frobenius`(`:3746`)が既に bound+prime を内部で組むので
     そちらを使えば `hHp`/`hp` 供給不要かも(署名要確認)。
2. **c2-math-A 枝** (`center ↥H ⊓ W₂.subgroupOf H = ⊥`) — irreducible-X route。
   `Xset_centralCommutator_isCoherent_of_c2_caseA`(`S08_CoherenceCore:1259`)+
   `isIrreducibleCharacter_of_mem_Xset_c2_caseA`(`CorePart2:1886`)で X-coherence は irreducible。
   ⟹ unweighted endgame `false_of_coherentXunionYset_of_not_coherentS`(`CorePart2:3439`)が
   そのまま効く可能性(Frobenius でなく irreducible-X で counting が通るか要確認)。IsPGroup は
   `isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator`(`CorePart1:3159`)で c2 から取れる。
3. **c2-math-B 枝** (`center ↥H ⊓ W₂.subgroupOf H ≠ ⊥`, = `W₂ ⊆ Z(H)`) — **HARD CORE**。
   X-coherence の member に reducible certain-type column が入る ⟹ weighted (5.6) break が必須。
   - X∪Y coherence seed: `coherentXunionYset_caseB_of_glued`(`S08_CaseBCoherence2:1616`)に在る。
   - weighted counting: `sum_div_normSq_induce_kernelFilter_eq`(`CorePart1:2526`, AxiomsCheck 登録)実在。
   - weighted 下端 engine: `coherentDegreeSqNormBound_of_not_coherentW`(`S08_CoherenceWeighted:475`)実在
     (X-adjoin 形)。
   - **欠落 = 中間の `sMember_degreeSqNormBound_of_not_coherent`**(break pair → 重み付き member family
     列挙、各 reducible member に Dmem 分解 data を供給)→ `xSum_le_two_psi_caseB` → c2 endgame。
   - FPF 算術破綻: `false_of_caseB_break_of_bounds`(`S08_CaseBEndgame:384`)+ `caseB_fpf_bound`(`:338`)実在。
   - dispatch: `eq_bot_or_eq_of_le_of_card_prime`(`CorePart1:3354`)で math-A/B 分岐。

## HARD CORE の解剖 (`sMember_degreeSqNormBound_of_not_coherent`)

unweighted テンプレート `sMember_degreeSumBound_of_not_coherent`(`CorePart2:2650`)の構造:
1. `exists_sMemberOrthonormalFamily`(`hF`)で `S₁` を **irreducible(norm 1)member** `χmem : Fin k →
   IrreducibleCharacter ↥L` として列挙 + 各 member の orthonormality (`⟨χmem i,χmem j⟩ = if i=j then 1 else 0`)。
2. `exists_sMemberDegreeData` で degree ratio、`sBreakPair_fields` で break pair ψ,ψ̄。
3. abstract engine `coherentDegreeSumBound_of_not_coherent` に渡す。

**weighted 版の crux** = case-B では `S₁` に **reducible certain-type column** が混ざる ⟹
- `χmem` は `IrreducibleCharacter ↥L` でなく一般 `ClassFunction ↥L ℂ`、norm `‖χmem j‖² = ⟨χmem j,χmem j⟩` 一般。
- **`exists_sMemberOrthogonalFamilyW`(未実装)** = orthonormal でなく **orthogonal** な enumerator で、
  weighted engine `coherentDegreeSqNormBound_of_not_coherentW`(`S08_CoherenceWeighted:475`)が要求する
  **各 member の `CharacterPsiDecomposition` (Dmem) + orthogonality + 重み付き degree bound** を供給する。
- **genuine new math = reducible member の per-member Dmem 構成**: certain-type column の分解は
  certain-type R(χ) 機構(`certainTypeDecompositionDa`/`certainTypeR`, §4/§5 σ-isometry)から作る。
  irreducible member は既存 `memberExtensionDecomposition`。
- counting 側 = `sum_div_normSq_induce_kernelFilter_eq`(weighted, 実在)で `∑_X χ(1)²/‖χ‖²`。

⟹ `xSum_le_two_psi_caseB`(`xSum_le_two_psi` `CorePart2:3229` の weighted mirror)→ c2 endgame に積まれる。

### ⚡ スコープ縮小 (2026-06-17, 追加 grep): per-member producer は実在 ⟹ hard core = **assembly**

`xChainCoherentW` docstring が挙げる per-member producer は **ほぼ全て実装済**(reducible Dmem を
ゼロから作る必要はない):
- **`certainTypeMemberDecomposition`**(`S06_CertainTypeCoherence:740`)= 「`memberExtensionDecomposition`
  の reducible 版」。coherent set `S₁` の reducible certain-type column に per-member
  `CharacterPsiDecomposition` を供給(`ofProjection (certainTypeR …)` 経由)。
- **`certainTypeR`**(`S06:639`)= R(μ_j) image family / `certainTypeDecompositionDa`(`S08_CaseBCoherence2:1360`)。
- **`certainTypeR_imageSet_orthogonal_dadeOfDiff`**(`S08_CaseBHortho:44`)= `hortho_mem` field。
- **`memberExtensionDecomposition`** = irreducible member 用 Dmem。
- engine `coherentDegreeSqNormBound_of_not_coherentW` の per-member 要求 = `mc`(norm)+ `Dmem` +
  `hortho_mem` + `htau1Dmem` は、上記 producer の **dispatch(reducible/irreducible で分岐)で供給可能**。

⟹ **hard core = weighted enumerator `exists_sMemberOrthogonalFamilyW` の ASSEMBLY**
(`exists_sMemberOrthonormalFamily` `CorePart2:2464` を mirror し、IrreducibleCharacter 制約を外して
per-member で `certainTypeMemberDecomposition` / `memberExtensionDecomposition` を dispatch、weight
`mc i = ⟨χmem i, χmem i⟩.re`、orthogonality は coherent set の member 間直交 + `certainTypeR_…orthogonal`)。
**ゼロからの新証明でなく既存 green producer の結線** ⟹ scope は当初見積より縮小(ただし multi-hundred LOC)。

### 次の coding action — 精密設計 (2026-06-17 確定, coding-ready)

**brick 1 (committable green, 最初に書く): per-member Dmem dispatcher `caseB_member_psiDecomposition`**
入力 = case-B coherent `hS₁coh : IsCoherent hyp.tau S₁ A`(A = supportInSubgroup (sharpImage H) L)、
`x ∈ S₁`、`x.conj ∈ S₁`、`hνZ : hS₁coh.extension x ∈ ZIrr G`。出力 = `CharacterPsiDecomposition hyp.tau x 0`。
本体 = `caseB_S_member_column_or_irreducible hyp h46 hHK (hS₁sub hxS₁)`(`S08_CaseBAssembly:1949`)で分岐:
- **column 枝** (`∃ χ₂≠1, columnSum h46 χ₂ = x`): `certainTypeMemberDecomposition h46 hχ₂ hdeg hagree hS₁coh
  hμ_S1 hμbar_S1 hνZ hdiffsupported`(`S06_CertainTypeCoherence:740`)。
  - `hdeg`(column 次数等式)= 既存 `columnDecompositionTau` 系の caller が供給する形(`S08_CaseBCoherence2:1757`
    と同型)。`hagree`/`hmapagree`(μ_j−μ̄_j 上で hyp.tau = certain-type Dade map)= `columnRFamilyTau`
    (`S08_CaseBCoherence2:1791`)が使う `hmapagree` と同源(H^#-supported + c2 K=H で両 map 一致)。
  - 必要 instance: `[NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible …] [Fintype (S06.ticVdiff h46).W] [Invertible …]`。
- **irreducible 枝** (`IsIrreducibleCharacter x`): `memberExtensionDecomposition hyp.dade hyp.hconj hS₁coh
  ⟨x,hirr⟩ hreal hdiffsupp hx_S1 hxbar_S1 hνZ hχχbar`(`S08_CoherenceCorePart1:1585`)。
  - ⚠ `hyp.tau = dadeIntegralCharacterMap hyp.dade (hyp.dade.fullDadeIsometryData hyp.hconj)`(`CorePart2:31`)
    なので memberExtensionDecomposition の τ と一致(defeq 確認要)。
  - `hreal`/`hdiffsupp`/`hχχbar` = case-B 用の member-fact から(Frobenius 専用の `sMember_characterFacts`/
    `sMember_diffSupport hF` は使えない ⟹ case-B 版 member-fact を特定 or 導出する小補題が要る。これが
    irreducible 枝の唯一の未確認点)。

**brick 2: weighted enumerator `exists_sMemberOrthogonalFamilyW`** = `exists_sMemberOrthonormalFamily`
(`CorePart2:2464`)を template に、`χmem : Fin k → ClassFunction ↥L ℂ`(IrreducibleCharacter 制約を外す)、
`mc i := (ClassFunction.inner (χmem i) (χmem i)).re`、`Dmem` = brick 1、`hortho_mem` =
`certainTypeR_imageSet_orthogonal_dadeOfDiff`(`S08_CaseBHortho:44`, column)+ irreducible 版、
`htau1Dmem` = rfl(両 producer とも tau1 = hS₁.extension)、member 間 orthogonality は coherent set の直交。

**brick 3-4**: `xSum_le_two_psi_caseB`(brick 2 + counting `sum_div_normSq_induce_kernelFilter_eq`)→
c2 endgame `false_of_coherentXunionYset_caseB_of_not_coherentS` → S08:59 の 3-way dispatch。

✅ 全部品 verified(未確認点ゼロ): brick 1 irreducible 枝の case-B member-fact は
`xMember_diffSupport_of_irreducible_X`(`S08_CoherenceCore:513`, Frobenius 非依存)+ 次数ベース
support(`sMember_diffSupport_of_charValue_eq`)で供給。`hreal` は irreducible X-member の非実性
(case-B X は奇位数ゆえ非実、既存の X-member fact)。column 枝・instance・classification・engine 側も確認済。
⟹ brick 1 から純粋に coding(新数学なし、既存 green producer の結線)。

## (6.5) p-group reduction — 完備 (Plan agent の「未形式化」は誤り)

- c1: `isPGroup_of_isFrobeniusGroup_of_card_le`(`CorePart1:3120`)
- c2: `isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator`(`CorePart1:3159`) ← c2 の
  fixed-point 条件(`C_H(x)=W₂ ⊆ ⁅H,H⁆`)+ coprime + bound から `∃ p, IsPGroup p H`。
- core: `isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization`(`:3097`)/
  `isPGroup_of_card_le_of_isFrobeniusAction`(`:2997`)。
- 唯一の入力 = bound `|Abelianization H| ≤ 4|W|²+1`(=(6.2)/(6.3),
  `theta_degree_le_index_mul_sqrt_index` `CorePart1:557`; Frobenius 版導出 `CorePart2:3828`)。

## 推奨着手順

1. **(green helper) Frobenius 枝の wiring 部品**: `hHnonab` from X-nonempty + Frobenius discharge を
   呼べる形にする(`nonempty_coherent_S_caseA_of_card_of_frobenius` の署名次第で hHp 供給要否確定)。
2. **(HARD CORE) `sMember_degreeSqNormBound_of_not_coherent`**: unweighted `sMember_degreeSqReBound_of_not_coherent`
   (`CorePart2:2738`)の証明を読み、weighted 鎖
   (`coherentDegreeSumBound` → `sMember_degreeSumBound` → `sMember_degreeSqReBound` の重み付き類似、
   下端は既存 `coherentDegreeSqNormBound_of_not_coherentW`)を構築。reducible member の Dmem は
   `certainTypeDecompositionDa`/`certainTypeR`(certain-type 分解)から、irreducible は
   `memberExtensionDecomposition` から供給。
3. `xSum_le_two_psi_caseB`(`xSum_le_two_psi` `CorePart2:3229` の weighted mirror; counting を
   `sum_div_normSq_induce_kernelFilter_eq` に差替)。
4. c2 endgame `false_of_coherentXunionYset_caseB_of_not_coherentS`(`false_of_coherentXunionYset_of_not_coherentS`
   `CorePart2:3439` の weighted+FPF mirror)。
5. S08:59 で 3-way dispatch を組み `.some` で `CoherenceTarget` 化。

## 再調査不要 (本セッション確定)

- 14 部品在庫は実在 sorry-free(gap_resolution §1)。weighted counting / weighted 下端 engine / (6.5)
  両ケース / Frobenius discharge / c2 X∪Y coherence / FPF break はすべて実在。
- 真 hard core = `sMember_degreeSqNormBound_of_not_coherent` 1 本(+ それを積む endgame)。
- (6.8) は今 FT carrier から orphaned(deferred-payoff prerequisite)= 記憶 [[ft-path-policy]]。
