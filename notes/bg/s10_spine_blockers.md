# BG §10 直列スパイン: ブロッカー精査 (2026-06-07)

worktree `bg-s10-spine` (branch `bg-s10-spine`, `ODD_ISSUE_BASE=4000`)。
対象ファイル `OddOrder/BG/Ch3_MaximalSubgroups/S10_BetaRadical.lean`。

## 着地済み

- **Prop 10.14(d)** `normalizer_le_of_nontrivial_beta_subgroup` (commit `f21eb12`):
  sorry-free, axioms = `[propext, Classical.choice, Quot.sound]`。
  10.14(a)(b)(c) (`beta_global_structure`, 既証) のみに依存する唯一の grounded ターゲットだった。
  併せて base `isSylow_sylowMap_of_mem_sigma` を private→public 化 (σ Sylow-lifting、複数ファイル使用)。

### grounded leaves landed — Lane C session (2026-06-08, branch `c-bg-s10`)

§10 spine 全体が Thm 3.6 (Lane A keystone) に推移ブロックされている中、**axiom 債務ゼロを維持して
landable な grounded prerequisite / helper を 2 件**着地 (full build 3609, axiom-clean):

- **p-length one が p'-quotient に沿って lift** `hasPLengthOne_of_normal_pPrime_quotient`
  (`PLengthTransfer.lean`, commit `7e55283a`): `N ⊴ Γ`, `Γ/N` が p'-group, `↥N` p-length one
  ⟹ `Γ` p-length one。Thm 10.6 r_p≥3 branch の最終 lift (`M_α ⊴ M` Hall α, `M/M_α` p'-group)。
  併せて Lem 1.21(a) `hasPLengthOne_subgroup` も既に landed (下記 Thm 10.6 ゲート 4 を解消)。
- **Lem 6.3(a) 第 1 結論** `commutator_eq_self_of_isComplement'_le_commutator`
  (`S06_Additional.lean` §6.3, commit `5e0e7066`): `G` 可解, `H ⊴ G` 補群 `K`, `H ⊆ G'`
  ⟹ `⁅H,K⁆ = H`。**Thm 10.6 ゲート 3 を解消** (下記)。Thm 10.6 Step 4 (`M_α=⁅M_α,K⁆`) /
  Cor 10.7(a) (`⁅P,V⁆=P`) / §15 (`⁅M_σ,K⁆=M_σ`) が引用。coprime 性は第 1 結論には不要。
  第 2 結論 `C_H(K) ⊆ H'` は §10 critical path 外 (どこからも未引用) ゆえ未着手。
- **GL(2,p) transvection** `exists_pow_map_line_eq` (`S10_Transvection.lean`, commit `0e191635`):
  2 次元 𝔽_p 空間で `φ^p=1, φ≠1`, line `L` を pointwise 固定 ⟹ `⟨φ⟩` が `L` 以外の p 本の line に
  transitive。**Lemma 10.13(c) の FT-block 非依存コア** (下記)。10.13(c) 完成には更に group-level
  wiring (`A` rank-2 elem ab ↔ `Additive A` = 2-dim 𝔽_p, `MulAut.conj x` ↔ φ) + Cor 10.7(b) が要る。

⟹ **Thm 10.6 r_p≥3 branch の残ゲートは Lem 10.4(b) + Thm 3.6 の 2 件のみ** (ゲート 1=Thm 10.2 ✅,
2=Lem 6.3(a) ✅, 3=p-length 単調性 ✅, 4=p'-quotient lift ✅)。両者とも Lane A keystone 系・
forward-axiom 待ち。

### ✅ Lane D first leaf landed — Thm 10.6 forward-wired (2026-06-09, branch `bg-s10-fwd`)

**`proper_hasPLengthOne` (Thm 10.6) を 2 forward-axiom 上に本物の証明として配線** (commit
`a07d9b6e`, full build 3613, AxiomsCheck island OK)。`#print axioms` = `[propext,
Classical.choice, Quot.sound, exists_prime_orderOf_zgroupCentralizer_of_complement,
pLengthOne_commutator_of_zgroupCentralizer]` = expected island ちょうど。

**新ファイル `S10_ForwardFromKeystone.lean`** に 2 forward-axiom (namespace `OddOrder.BG.Ch3.S10`):

1. **`pLengthOne_commutator_of_zgroupCentralizer`** = **BG Thm 3.6** (keystone-gated)。署名 (Lane A
   が解消時にこの statement と一致させること = de-axiom は name swap):
   ```
   {Γ} [Group Γ] [Finite Γ] (hsolv : IsSolvable Γ) (hodd : Odd (Nat.card Γ))
   {H R : Subgroup Γ} (hHnormal : H.Normal) (hHall : Nat.Coprime (Nat.card ↥H) H.index)
   (hcompl : H.IsComplement' R) {R₀ : Subgroup Γ} (hR₀ : R₀ ≤ R) (hR₀prime : (Nat.card ↥R₀).Prime)
   (hZ : IsZGroup ↥(Subgroup.centralizer (R₀ : Set Γ) ⊓ H)) (p : ℕ) [Fact p.Prime] :
   Ch1.hasPLengthOne p ↥⁅H, R⁆
   ```
   normal Hall は `H.Normal` + `Coprime (card H) (index)` でエンコード。**Lane A は §3 で Thm 3.6 を
   landed したらこの署名でこの axiom を置換** (forward_dep_policy)。

   ### 🔎 Thm 3.6 de-axiom contract — Lane A 規約との整合精査 (2026-06-09)

   **(1) faithfulness ✅**: 上記署名は BG mmd L955 と完全一致 (G 可解奇 / H 正規 Hall / R 補群 /
   R₀≤R 素数位数 / C_H(R₀) Z-群 / ∀ prime p, [H,R] p-length one)。`IsZGroup` = mathlib (Sylow 全 cyclic,
   mmd L953 定義と一致)。`Ch1.hasPLengthOne`/`⁅H,R⁆` は §3/§10 共有。
   **内部整合 ✅**: 本 axiom と Lem 10.4(b) axiom は `C_H(R₀) = centralizer(R₀)⊓H` (ambient Subgroup Γ
   形) で一致 — `proper_hasPLengthOne@106` で齟齬なく適用。

   **(2) Lane A 現況**: Thm 3.6 は **未 Lean 化** (a-keystone: 3.4 `thm34` ✅ landed, 3.5 `thm35` WIP,
   3.6 は §3C 予定地のみ)。**現時点で署名衝突は無い**。keystone_plan L629 が「§10 spine が Thm 3.4/3.6 を
   forward-axiom で consume — 境界に注意」と明記、Lane A は境界を認識済み。

   **(3) ⚠ encoding 差分 (vs Lane A landed `thm34`/`thm35` 規約) — すべて shallow・bridgeable**:
   | 項目 | 本 axiom | thm34/35 規約 | 影響 |
   |---|---|---|---|
   | 可解性 | `(hsolv : IsSolvable Γ)` 明示 | `[IsSolvable G]` instance (thm34) | 呼出側 binder 調整 1 行 |
   | normal Hall | `Coprime (card H) H.index` | `Coprime (card K)(card R)` (thm34) | 補群で index=card R、等値・rw 1 行 |
   | 素数位数 | `(card R₀).Prime` | `∃ p, p.Prime ∧ card=p` (thm34/35) | ⟨⟩ 包装 1 行 |
   | 結論 prime | `[Fact p.Prime]` | `(hp : p.Prime)` の可能性 | Fact 化 1 行 |

   いずれも forward_dep_policy の「convention 適応」許容ブリッジ範囲。**数学的ミスマッチは無し**。
   3.4/3.5 は rep-level (`∀g∈⁅⁆, ρg=1`) で Thm 3.6 (group-level) の直接 template でないため、3.6 署名は
   Lane A が新規に書く ⟹ **本 axiom 署名が declared interface (Lane A が match すべき対象)**。

   **(4) 結論 = 不安 LOW**。faithful + 内部整合 + Lane A 認識済 + 差分は trivial bridge。**推奨**: Lane A が
   Thm 3.6 を書く直前に本署名を提示し (a) verbatim 採用、または (b) 上表の convention で書いて §10 側に
   1 行 adapter を置く、のどちらかを事前合意。`S10_ForwardFromKeystone.lean` docstring が contract を明記済。
2. **`exists_prime_orderOf_zgroupCentralizer_of_complement`** = **BG Lem 10.4(b)** (grounded,
   lane a1 領域, keystone-gated でない・deferred)。10.6 用に特化:
   ```
   (hG : IsMinimalSimpleOdd G) {M} (hM : M ∈ maximalSubgroups G) (hMα : Malpha M ≠ ⊥)
   {K : Subgroup ↥M} (hK : ((Malpha M).subgroupOf M).IsComplement' K)
   {q} (hq : q.Prime) (hqK' : q ∈ ((commutator ↥K).index).primeFactors) :
   ∃ x : ↥M, x ∈ K ∧ orderOf x = q ∧
     IsZGroup ↥(Subgroup.centralizer (↑(Subgroup.zpowers x) : Set ↥M) ⊓ (Malpha M).subgroupOf M)
   ```
   `q ∈ π(K/K')` は `(commutator ↥K).index` の primeFactors でエンコード。R₀=⟨x⟩=zpowers x に合わせ
   centralizer は zpowers 形。

**⚠ Lem 10.4(b) 仮説の訂正** (p.87 PDF visual-read で確定, references commit `ded5acd`): 原典は
**「`p ∉ σ(M)` ∧ `M_α ≠ 1` ⇒ ∃ x∈Ω₁(Z(P))#: {M}≠ℳ(C_G(x)) ∧ C_{M_α}(x) Z-群」**。
本ノート/旧 scaffold が (b) を「`p∈α(M)`」と書いていたのは**誤り**。10.6 適用では prime=q・Sylow=Q⊆K で、
`q∈π(K/K') ⟹ q∣|M/M'| (M/M'↠K/K') ⟹ q∉σ(M)` (Lem 10.4(a)=`alpha_criterion`) 経由で (b) が効く。
de-axiom 時はこの還元 + 一般 10.4(b) を組む。

**証明の骨子** (S10_BetaRadical `proper_hasPLengthOne`): M∈ℳ(H) 取得→Lem1.21(a)で H に落とす。
case `p∉α(M)` = `maximal_hasPLengthOne_of_not_mem_alpha` (landed)。case `p∈α(M)`: Nontrivial ↥M
(p∣|M|) → N:=M_α.subgroupOf M は normal Hall (`Malpha_subgroupOf_isHall_of_isHall`) →
`N≤commutator ↥M` (Thm10.2: Malpha≤Msigma≤derived; comap_mono) → `N<⊤`
(`IsSolvable.commutator_lt_top_of_nontrivial`, G 明示引数!) → Schur-Zassenhaus 補群 K → K≠⊥ →
q∈π(K/K') (K solvable nontrivial⟹not perfect) → Lem10.4b axiom で x → Thm3.6 axiom で ⁅N,K⁆
p-length one → Lem6.3a (`Ch1.S06.commutator_eq_self_of_isComplement'_le_commutator`) で ⁅N,K⁆=N →
`Ch1.hasPLengthOne_of_normal_pPrime_quotient` で M へ lift。**地雷: PLengthTransfer helper は `Ch1.`
修飾要; `commutator_lt_top_of_nontrivial` は `variable (G)` で G 明示; `comap_map_eq_self_of_injective`
は H 明示引数。**

**AxiomsCheck に新マクロ `#assert_axioms_island name expecting [ax...]`** 追加 (3 レーン共有, 末尾)。
`#assert_only_allowed_axioms` (標準 3 公理のみ=unconditional 保証) と別に、conditional/island 定理が
**ちょうど** standard∪{列挙 axiom} に依存することを assert (未列挙 axiom=sorry/別 axiom creep を検出、
かつ列挙 axiom が実際に使われることも要求)。keystone landed 時は island 削除→`#assert_only_allowed_axioms`
へ移行。**§10 spine は従来 AxiomsCheck 未カバー** (Ch1-2+AppABC のみ); Lane D が §10 import を追加。

### 次の leaf (Lane D 継続)

Thm 10.6 が landed したので下流が順に unblock (型検査レベル; 数学的には keystone 待ち):
- **Lem 10.8** `isHall_Mbeta` (S10_BetaRadical@168) = 10.6 + Thm 5.6 (✅)。**spine 直列 (10.6→10.8→10.9)、
  ユーザ選択で次の対象**。10.7 は経由しない (下記)。
- **Cor 10.7** `sylow_structure` (@125) = 10.6 + Lem 6.6 (✅)。**5 部結合の大物・spine 直列線外**
  (下流は Prop 10.10 / Lem 10.13 のみ; 10.8 は 10.7 非依存)。各部 Lem 6.6 各成分を ↥M で適用し
  G↔↥M 共役変換で戻すプラグ作業 (推定 300-500 行)。Cor 10.7(b) は更に rep-theory keystone
  (`r(P)=2⇒Z(P) cyclic`、10.13 と同じ)。後回し。
- 10.9 (3 本)/10.10 = 10.7/10.8 経由。

### Lem 10.8 (`isHall_Mbeta`) 実行プラン (2026-06-09 精査)

**4 conjunct**: (1) `IsHallSubgroup (beta M) (Mbeta M)`; (2) ∃W≤M', Hall β(M)' in M', nilpotent;
(3) 同 for M_σ; (4) ∀p∈π(M)−β(M): M' と M_σ が normal p-complement。BG 証明順 = (4)→(1)→(2,3)。

**エンジン = Thm 5.6 `narrow_sylow_solvable_structure` (S05:3268, 5-conjunct, landed)**: solvable odd
G, p∣|G|, S Sylow p **narrow**, (3≤pRank↥S p → hasPLengthOne p G) ⟹ (c) `HasNormalPComplement p
↥(commutator G)` 他。↥M に適用 (hasPLengthOne は `proper_hasPLengthOne` から無条件供給)。

**landed tools**: `hasNormalPComplement_of_subgroup` (Ch05:1984, M_σ⊆M' 継承); `Msigma_le_derived`
(M_σ⊆M'); `proper_hasPLengthOne` (Thm 5.6 の hasPLengthOne 仮説); narrow 特徴づけ
`narrow_iff_exists_maximalElementaryAbelian_card_prime_sq` (S05:2055, pRank≥3 で narrow⟺∃max-elem-ab p²),
`narrow_iff_exists_card_prime_centralizer_pRank_le_two` (S05:2121).

**🛑 GAP 1 (conjunct 4 の本質ブロッカー) = narrowness 補題**
`isNarrow_sylow_of_not_mem_beta`: p∈π(M)−β(M), S Sylow p of M ⟹ `IsNarrow p ↥S`。
- 易: p∉α(M) ⟹ pRank↥M p≤2 ⟹ pRank↥S p≤2 ⟹ narrow (rank disjunct)。
- 易: ¬idealPrime かつ pRank G p<3 ⟹ pRank↥M p<3 ⟹ rank≤2 narrow。
- **✅ 解決: p∈α(M) ∧ ¬idealPrime p G** ⟺ r_p(M)≥3 ∧ **Sylow of G narrow**。当初「narrowness 部分群
  継承が要・非自明」と懸念したが**不要**だった: **p∈α(M) ⊆ σ(M) ⟹ Sylow p of M = Sylow p of G**
  (`isSylow_sylowMap_of_mem_sigma`; p∈σ(M) の witness Sylow は N_G⊆M で p-群の normalizer 成長が M
  内に閉じる ⟹ Sylow of M が Sylow of G)。よって narrowness は**同一群上で transfer** (継承不要)。
  ¬idealPrime + r_p(G)≥3 で Sylow of G に p²-max-elem-ab ⟹ narrow
  (`narrow_iff_exists_maximalElementaryAbelian_card_prime_sq`)、Sylow 共役 iso (`IsNarrow.of_mulEquiv`)
  で当該 S へ、map iso で ↥P へ。**✅ `isNarrow_sylow_of_not_mem_beta` (private, UNCONDITIONAL) landed**
  (commit `e98792c8`)。

**✅ GAP 2 解決 = `hasNormalPComplement_of_mulEquiv` (public, UNCONDITIONAL)** を S10_BetaRadical に
landed (S7B2 private 版を再現)。M_σ は `(Msigma M).subgroupOf (derivedInG M)` +
`hasNormalPComplement_of_subgroup` + iso。

**✅ conjunct 4 (= Lem 10.8(c)) landed** `derived_msigma_hasNormalPComplement_of_not_mem_beta`
(commit `e98792c8`, **forward-conditional via Thm 10.6**, AxiomsCheck §10 island 登録済 = 2 forward
axioms ちょうど)。Thm 5.6(c) を ↥M に適用 (narrow Sylow + proper_hasPLengthOne)。

### ✅✅✅ Lemma 10.8 COMPLETE (2026-06-09, branch `bg-s10-fwd`, 4 commits)

**`isHall_Mbeta` (a)(b)(c) 全 conjunct 配線完了・sorry-free・keystone island ちょうど**
(`#print axioms` = standard 3 + 2 forward = `pLengthOne_commutator_of_zgroupCentralizer`,
`exists_prime_orderOf_zgroupCentralizer_of_complement`)。full build 3613 green + AxiomsCheck OK。

実装は当初の「5-step 交差=M_β」プランより clean な **engine 2 本**に集約された
(交差を M_β と明示同定する step 3/4 は engine 内部で IsPiGroup.le_oPiCore 両方向に吸収):

1. **O_π 交差補題** `Ch03.iInf_oPiCore_compl_singleton` (Ch03 Main, **unconditional**, commit
   `5dc29632`): 有限 G, S:Set ℕ で `⨅ p∈S, O_{p'}(G) = O_{Sᶜ}(G)`。⊇=oPiCore_mono、⊆=交差が
   normal Sᶜ-群 (normal_iInf_normal + oPiCore.isPiGroup)。
2. **Hall engine** `isHall_oPiCore_of_forall_hasNormalPComplement` (S10_BetaRadical,
   **unconditional**, commit `db2af624`): 有限 H が ∀p∈π(H)−π で normal p-complement ⟹
   `O_π(H)` Hall π。O_π(H)=O_{Tᶜ}(H)=⋂O_{p'}(H) (T=π(H)−π)、r∈π が index 割れば Sylow r が各
   normal p-complement (helper `le_of_coprime_card_index`) ⟹ ⊆O_π ⟹ 矛盾。
3. **conjunct 1** `Mbeta_isHall` (commit `77d158d0`, **forward-conditional**): engine を
   H=↥(commutator ↥M) に適用 + step E' `oPiCore_subgroupOf_eq_of_normal` (D◁G' で
   (O_π G').subgroupOf D = O_π ↥D, **一般・unconditional**) + |M:M'| coprime β (M_α⊆M' Hall α⊇β)
   + σ⊇β で G へ lift (`isHallSubgroup_of_subgroupOf_isHall_of_forall_not_dvd_index` ×2)。
4. **nilpotency engine** `isNilpotent_of_forall_hasNormalPComplement` (**unconditional**, commit
   `f31fe53f`): ∀p∈π(H) normal p-complement ⟹ nilpotent (各 p で engine 2 が O_p=Hall{p}=
   正規 Sylow ⟹ 全 Sylow 正規 ⟹ `isNilpotent_of_finite_tfae`; `Sylow.ofCard`/`unique_of_normal`)。
5. **(b) producer** `exists_isNilpotent_isHall_compl` (**unconditional**): 有限可解 K が π(K)−β で
   normal p-complement ⟹ nilpotent Hall βᶜ-部分群 (hall_E_exists + hasNormalPComplement_of_subgroup
   + engine 4)。conjunct 2,3 は K∈{M',M_σ} に適用、W₀ を M.subtype で G へ map
   (solvable=`solvable_of_surjective`∘equivMapOfInjective, nilpotent=`nilpotent_of_surjective`)。

**再利用可能 unconditional 資産** (keystone 非依存、他章でも使える): O_π 交差補題、Hall engine、
nilpotency engine、(b) producer、step E' `oPiCore_subgroupOf_eq_of_normal`、helper
`le_of_coprime_card_index`。

### ✅ Lemma 10.8(c) 完全化 (2026-06-09, commit `4666dbe4`)

isHall_Mbeta docstring で deferred だった **「p は |M/O_{p'}(M)| の最大素因子」**を形式化:
- `largestPrime_quotient_oPiCore_compl_of_not_mem_beta`: Thm 5.6 第1 conjunct を ↥M narrow Sylow に適用。
- `sylow_le_oPiCore_compl_of_lt_of_not_mem_beta`: 帰結「q>p ⟹ Sylow q of M ⊆ O_{p'}(M)」
  (= BG mmd L2862「O_{p'}(M) contains all q-elements」; `le_of_coprime_card_index` 再利用)。
  **Cor 10.9(a) の X⊄M' (p<q) ケースの前提**。両者 forward-conditional、AxiomsCheck §10 island 登録。

### 🛑 次の leaf = Cor 10.9 — **Hall-D + Hall∩normal が前提 (repo 未収載・大物)**

**Cor 10.9 (3 本)**: (a)(1)(2)=`beta_complement_centralizes`, (a)(3)=
`beta_complement_normalizer_derived_contains_sylow`, (b)=
`beta_factorization_of_sylow_normalizer_in_intersection`。すべて (a) の **W nilpotent** が核。

**BG 証明骨子 (p.81, mmd L2860)**: p,q∈β(M)' distinct, X q-部分群 (X⊆M' or p<q)。
W := Hall {p,q}-subgroup of XM' **containing X**。W⊆W* (Hall β'-subgroup)、10.8(b) で W*∩M' nilpotent
⟹ W∩M' nilpotent。**W nilpotent**: X⊆M' なら W=W∩M'; else p<q で
`sylow_le_oPiCore_compl_of_lt_of_not_mem_beta` (✅) より W∩O_{p'}(M)=normal Sylow q of W、
W∩M' nilpotent + W/(W∩M') q-群 ⟹ O_p(W∩M')=normal Sylow p of W ⟹ 両 Sylow normal ⟹ nilpotent
(`isNilpotent_of_forall_hasNormalPComplement` ✅ or tfae)。M_σ◁M' で W∩M_σ Hall {p,q} of M_σ ⟹
(1) X が Sylow p of M_σ を中心化 (W nilpotent ⟹ Sylow 同士可換)。(2)=(1)+Uniqueness。(3): X=Sylow q of M',
M_βX=O_{β∪{q}}(M')◁M, Frattini で M=M_β N_M(X), Lem 6.5 で O_p(W)⊆N_M(X)'。(b)=(a)(2)+(a)(3)。

**🛑 BLOCKER = 2 つの未収載 Hall 補題** (両者 unconditional・一般 Isaacs Ch03 infra・再利用可):
1. **Hall-D (Wielandt)** `∃ Hall π-subgroup ⊇ 任意 π-subgroup` (solvable G)。repo は `hall_E_exists`
   (存在) + `hall_C` (共役 H^g=K) のみ。**containment は無**。W⊇X の構成に必須。`hall_C_strong_aux`
   (Main.lean:857-1207) 級の |G|-induction (~200-350 行)。minimal normal r-group で r∈π/r∉π 場合分け。
2. **Hall ∩ normal = Hall of normal** `IsHallSubgroup π H, N◁G ⟹ IsHallSubgroup π (H∩N の N 内)`。
   W∩M' Hall {p,q} of M' / W∩M_σ Hall {p,q} of M_σ に必須。~50-80 行。

⟹ **Cor 10.9 は Hall-D + Hall∩normal を先に landing してからでないと組めない** (各々別 unconditional leaf)。
**推奨次手 = Hall-D を Isaacs Ch03 に landing** (general infra, Cor 10.9 + §12+ が消費)。その後 Cor 10.9(a)→(b)。

### その他の §10 残ターゲット (keystone gated)
- **Cor 10.7** `sylow_structure` (@125 sorry) = 10.6 + Lem 6.6 (✅)。(a) 配線可だが (b) は rep-theory
  keystone (`r(P)=2⇒Z(P) cyclic`、10.13 と同じ) gated。
- **Prop 10.10** `normalizer_factorization` = §7 (✅) + Cor 10.7 + Lem 6.5 ⟹ Cor 10.7 経由 gated。
- **Prop 10.11** `sigma_complement_rank_le_one` (S10_LocalLemmas@460) = Cor 10.7 経由 keystone gated。
- 旧「残フロンティア conjunct 1-3」は**全消化** (Lemma 10.8 完成)。

### 次の grounded leaf = group-level transvection bridge (scoped, ⚠ Additive 診断ダイヤモンド要注意)

`exists_pow_map_line_eq` (抽象 𝔽_p 形, 着地済) を 10.13(c) が consume する **group 形**
`mulAut_pow_map_orderP_subgroup` (E elem ab rank-2, σ:MulAut E 位数 p が Z₀ を pointwise 固定 ⟹
order-p 部分群 X,Y≠Z₀ が σ^k で結ばれる) に持ち上げる。infra は揃っている:
- `IsElementaryAbelian.zmodModule` (`Additive E` = ZMod p-module), `card_eq_pow_finrank` (⟹ dim=2),
- σ↔φ: `(AddAutAdditive (G:=E)).symm.trans AddAut.toZModLinearEquiv` (PRank `mulAutEquivGeneralLinearGroup`
  と同型、map_pow で `φ^k = β(σ^k)`),
- 部分群↔部分加群 (carrier 保存 ≃o): `Subgroup.toAddSubgroup` ∘ `ZMod.toZModSubmodule`; card p ↔ finrank 1。
- 結論翻訳: `Φ(X.map σ^k) = (Φ X).map φ^k` を **carrier 集合等式**で (`φ a = σ a` synonym).
**⚠ Additive-synonym diamond — 3 層 (2026-06-09 精査)**。`Additive E` + `letI := hE.zmodModule`
の組合せが instance/coercion synthesis を段階的に壊す。判明した layer と fix:
- **Layer 1 (CommGroup) ✅ FIX 判明**: `letI : CommGroup E := inferInstance` が失敗するのは
  `[Group][IsMulCommutative]→CommGroup` が **scoped instance** (`Mathlib/Algebra/Group/Defs.lean`
  L1328-1368, `IsMulCommutative` scope) のため。**`open scoped IsMulCommutative`** で解決 (PRank L16 が
  これを open している)。これで `letI : IsMulCommutative E := .of_comm hE.comm; letI : CommGroup E :=
  inferInstance; letI := hE.zmodModule` が通る。
- **Layer 2 (Mul stuck) ✅ FIX 判明**: `(AddAutAdditive.symm).trans (AddAut.toZModLinearEquiv)` の
  `.trans` (MulEquiv) が `Mul (Additive E ≃ₗ[ZMod p] Additive E)` を metavar で stuck。**β を `.trans`
  で組まず、`φ := AddAut.toZModLinearEquiv (p := p) (M := Additive E) ((AddAutAdditive (G:=E)).symm σ)`
  と直接適用**すれば stuck 回避 (φ:LinearEquiv の型注釈で OK; φ^k は `← map_pow, ← map_pow` で
  `toZModLinearEquiv (AddAutAdditive.symm (σ^k))` に書ける)。
- **Layer 3 (LinearEquiv coercion) ✗ DEEP・未解決**: 上記 φ に対し **`φ a` (bare LinearEquiv 適用) が
  "Function expected" で coerce しない** — letI module 下で `DFunLike (Additive E ≃ₗ[ZMod p] Additive E)`
  の synth が壊れる。PRank は `Additive E` 上で **GL/matrix までしか行かず bare LinearEquiv を coerce
  しない**ので、この層は repo に前例なし。
  - **2026-06-09 精査**: `φ.toEquiv a` (plain `Equiv` coercion, **module 不要**) は **✅ coerce する**;
    `φ.toLinearMap a` は ✗ stuck (LinearMap FunLike が module 依存)。⟹ 直接適用は `.toEquiv` で回避可だが、
    **`Submodule.map (φ^k).toLinearMap` / そのメンバー reasoning (`(φ^k).toLinearMap b`) が pervasively
    stuck** — `.toEquiv` だけでは abstract lemma の結論 (`W.map (φ^k).toLinearMap`) を group 側へ繋げない。
**⟹ 結論 = module route は `Submodule.map` 層で diamond に詰む。diamond-free な道は 2 つ:**
  1. **(推奨) group-theoretic 再証明 (C)**: `Additive E`/module を一切触らず、E を multiplicative group の
     まま `E = Z₀ × ⟨e⟩` 分解 + 指数 (ZMod p) 算術で transvection transitivity を直接証明 (abstract
     `exists_pow_map_line_eq` の証明を group 言語に翻訳, ~160 行, diamond 無だが fresh effort)。
     abstract lemma は 𝔽_p 版として残す (orphan 化だが valid)。
  2. concrete transport: term-level map-commutation 補題 (`Subgroup.toAddSubgroup`/`toZModSubmodule` が
     map と可換) を組んで element coercion を避ける — 可能だが補題群が要り、これも focused session。
- **⚠ ROI 注意**: bridge が済んでも **10.13(c) は更に Cor 10.7(b) (= rep-theory keystone, Lane A) 待ち**
  なので即座には閉じない。bridge は「keystone 着地後に 10.13(c) を即閉じる ingredient」の位置付け。
  Layer 1/2 の fix は確定 (transport ルートでも再利用可)。

## 直列スパインは Theorem 10.6 に全面ブロックされている

ユーザ指定の直列順 `proper_hasPLengthOne (10.6) → isHall_Mbeta (10.8) → 10.14/10.9/10.10` は、
**10.6 を起点に推移的に全滅**している。依存を精査した結論:

| ターゲット (file:line は landing 前の番号) | 直接依存 | 状態 |
|---|---|---|
| **10.6** `proper_hasPLengthOne` | r_p≤2: `maximal_hasPLengthOne_of_not_mem_alpha` (✅ base) + **p-length 部分群単調性** (❌); r_p≥3: **Thm 3.6** (❌) + **Lem 10.4(b)** (❌) + **Lem 6.3(a)** (❌) | **BLOCKED** |
| **10.7** `sylow_structure` | 10.6 ("P ⊆ O_{p',p}(M)") + Lem 6.6 (✅) | BLOCKED via 10.6 |
| **10.8** `isHall_Mbeta` | 10.6 + Thm 5.6 `narrow_sylow_solvable_structure` (✅ S05:3268) | BLOCKED via 10.6 |
| **10.9** `beta_complement_*` (3 本) | 10.8 + Lem 6.5 (✅) + Frattini (✅) + Hall (✅) | BLOCKED via 10.8→10.6 |
| **10.10** `normalizer_factorization` | §7 Prop 7.3/7.4/7.5 (✅) + **Cor 10.7** + Lem 6.5 (✅) | BLOCKED via 10.7→10.6 |

## 未形式化の upstream (10.6 の 4 ゲート)

1. **BG Theorem 3.6** (mmd L955): 「`G` 可解奇数位数, `H ⊴ G` normal Hall, `R` を `H` の補群,
   `R₀ ≤ R` prime order で `C_H(R₀)` が Z-群 ⇒ 任意素数 `p` で `[H,R]` は p-length one」。
   **最小反例法の多ページ証明** (V=F(H) が elementary abelian を示す等、表現論的)。
   §3 の独立した大仕事。リポジトリに無い (S03c は Thm **3.7** = Frobenius kernel nilpotent のみ)。
   → 10.6 の r_p≥3 ケースのエンジン。これが最大ブロッカー。
2. **BG Lemma 10.4(b)** (mmd MISSING_PAGE, PDF p.87): 「`p∈α(M), M_α≠1` ⇒
   `∃ x∈Ω₁(Z(P))#: ℳ(C_G(x))={M} ∧ C_{M_α}(x) Z-群`」。
   **未 statement**。`S10_LocalLemmas.lean` (lane A1) の `alpha_criterion` は (a)(c) のみで (b) は欠落
   (docstring に「Ω₁(Z(P)) の入れ子 encoding は後続」と明記)。Ω₁(Z(P)) encoding が要る。
   → 10.6 の r_p≥3 ケースで「order-q 元 x で C_{M_α}(x) が Z-群」を供給。lane A1 の領域。
3. **BG Lemma 6.3(a)** (mmd L1981): 「`H ⊴ G` normal Hall, `K` 補群, `H⊆G'` ⇒ `H=[H,K]` かつ
   `C_H(K)⊆H'`」。証明は clean (H*=[H,K]⊴G, G/H*=H̄×K̄, H̄⊆Ḡ'=H̄'×K̄' ⇒ H̄=H̄' ⇒ solvable で H̄=1)。
   ~80-150 行で形式化可能。`S06_Additional` の `inf_commutator_eq_of_coprime` は Lem **6.5**(a)、別物。
   → 10.6 で `M_α=[M_α,K]` を供給。
4. **p-length 部分群単調性**: `H ≤ G ∧ hasPLengthOne p G ⇒ hasPLengthOne p ↥H`。
   10.6 の reduction (M∈ℳ(H) を取り l_p(H) ≤ l_p(M)) に必要。isolate された lemma は無い。
   `hasPLengthOne := ¬ p∣|G/O_{p',p}(G)|` encoding で O_{p',p} の部分群版補題が要り、~50-150 行。

## 推奨される次アクション (優先度順)

- **(本命) BG Theorem 3.6 を §3 で形式化** (`OddOrder/BG/Ch1_Preliminary/S03*` に新ファイル)。
  これがスパイン全体の律速。最小反例法 + §1 (Prop 1.5/1.6, Lem 1.21) + §2 表現論 を要する大仕事。
  併せて clean な prerequisite (p-length 単調性, Lem 6.3a) も landing。
- **(代替) lane A1 = `S10_LocalLemmas` を先に進める**: Thm 3.6 と独立。10.4(b) を statement 化 +
  10.3/10.4/10.5/10.11/10.12/10.13 を埋める。10.6 とは別の高レバレッジ leaf 群。
- **(妥協) forward-axiom でスパインを配線**: Thm 3.6 / Lem 10.4b / Lem 6.3a / p-length 単調性を
  named axiom 化し 10.6→10.8→10.9→10.10 を上に組む。§10 ロジックは検証されるが axiom 負債が増える
  ([[scaffold-sorry-free-not-done]] の懸念)。要ユーザ判断。

## 検証済み (✅ 利用可能、再調査不要)

Thm 10.1 `fusion_control_of_mem_sigma` / Thm 10.2 `isHall_Msigma_Malpha`,`Msigma_le_derived`,`Malpha_isHall` /
Thm 4.18 `solvable_structure_of_pRank_le_two` / Thm 5.5 narrow core + Thm 5.6 `narrow_sylow_solvable_structure` (S05) /
Lem 6.5(a) `inf_commutator_eq_of_coprime`, 6.5(c) `exists_conj_eq_of_isHall_subgroupOf`, Lem 6.6
`exists_mem_centralizer_inf_conj_le_sylow` / §7 (sorry-free) / 10.14(a)(b)(c) `beta_global_structure` /
Uniqueness `isUniquelyMaximal_of_mem_e2_not_maximal` / `isSylow_sylowMap_of_mem_sigma` (今 public 化)。

## Lemma 10.13 / §11 も rep-theory keystone に推移ブロック (2026-06-07 検証)

§11.5/11.6/11.7 の単一ゲート **Lemma 10.13** (`nonabelian_pSubgroup_rankTwo_elemAbelian_structure`,
`S10_LocalLemmas.lean:1063`, 全 (a)(b)(c) が 1 sorry) は **独立に landing できない**:
- 証明 (BG p.79-80) の r(S)=2 ケースが **Cor 10.7(b)** (`r(S)=2 ⇒ Z(S) cyclic`) を使う。
- **Cor 10.7** (`sylow_structure`, `S10_BetaRadical.lean:43`, **sorry**) の (a) は "P ⊆ O_{p',p}(M)"
  = **Theorem 10.6** (`proper_hasPLengthOne`, sorry) を使い、(b)=(a)+Thm 4.16。
- Theorem 10.6 → **Theorem 3.6** → **Theorem 3.4** → 代数閉体 extraspecial 表現論 (= rep-theory keystone, `bg-reptower` レーン)。

⟹ **§11.5-7 → 10.13 → Cor 10.7(b) → 10.6 → 3.6 → rep-theory keystone** で推移ブロック。
§10 spine と同じく、§11 の残りも **keystone (Thm 3.4/3.6) がクリティカルパス**。

**ただし self-contained で unblocked な部分**: Lemma 10.13(c) のコア = 「(ℤ/p)² の位数 p の自己同型が
1 本の line を固定すると残り p 本の line を transitive に置換する」(GL(2,p) transvection 事実、純線型代数、
FT のブロックと無関係)。これは独立補題として今でも構築可能で、10.13(c) に最終的に必要 (非無駄)。
GL(2,p) 既存 infra = `Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean`。
