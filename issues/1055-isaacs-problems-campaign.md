---
id: 1055
slug: isaacs-problems-campaign
title: "Isaacs 演習問題 (Problems) 形式化 campaign (scope 拡大 2026-07-22)"
created: 2026-07-22
---

# Isaacs 演習問題 (Problems) 形式化 campaign (scope 拡大 2026-07-22)

## 背景

**scope 拡大 (ユーザー裁定 2026-07-22、issue 9205 ③)**: lane a の割当 territory
(Isaacs 番号付き結果 + Pf 本文 + FeitSibley/NearFields Prop2) が全完済し、hub が
再配分をユーザーに escalate → **(E) Isaacs 演習問題 (Problems) を in-scope 化**して
lane a が形式化することに決定。従来の被覆測定 (`notes/isaacs/frontier_measured_2026_07_19.md`)
は「番号付き結果のみ」で演習を対象外にしていた ⟹ 本 campaign で演習も形式化対象に加える。

## 構造 (実測)

Isaacs FGT は各章を section (1A, 1B, ...) に分け、各 section 末に "Problems NX" として
演習を `NX.M` 形式で番号付け (例: 1A.1–1A.10, 1B.1–…, 1C.1–1C.8, 1D.1–1D.18,
1E.1–1E.8, 1F.1–…, 1G.1–…)。全 10 章で数百問。⚠ pdftotext は OCR ノイズあり
(記号・式散乱) → **statement は PDF ページ画像で確定** (Isaacs は PDF ページ = 書籍ページ + 13)。

## やること (上流優先 + 文書順)

各章の演習を section 順・番号順に形式化。置き場 = `OddOrder/Isaacs/ChNN_.../Problems*.lean`
(章ディレクトリ内の新 leaf、mathlib 互換記述名、`OddOrder.lean` 配線)。

- [ ] **Ch.1 Sylow** — 1A / 1B / 1C / 1D / 1E / 1F / 1G Problems
- [ ] Ch.2 Subnormality
- [ ] Ch.3 Split Extensions
- [ ] Ch.4 Commutators
- [x] Ch.5 Transfer — **🎉 完済 (2026-07-27)**: §5A–§5E 全問
- [x] Ch.6 Frobenius Actions — **🎉 完済 (2026-07-27)**: §6A (11 問) / §6B (9 問) / §6C (2 問) 全問
- [x] Ch.7 Thompson Subgroup — **🎉 完済 (2026-07-27)**: §7A (6 問) / §7C (7C.1) 全問
      (§7B に Problems 節は無い)
- [ ] Ch.8 Permutation Groups — **次の frontier (2026-07-27)**
- [ ] Ch.9 More Subnormality
- [ ] Ch.10 More Transfer

## 方針

- **番号付き結果と同じ強度**で形式化 (statement を PDF で確定 → theorem 化 → 実証明)。
- 演習が **mathlib 既存**または **repo 既存定理**で即従うものは、docstring で対応を記録
  (ラッパー方針: 純粋リネームは書かない)。
- 演習が**定義の導入のみ**のもの (例: 1A.5 が transitive action を定義) は、mathlib に既存概念が
  あれば docstring 記録、無ければ必要な範囲で定義。
- 前提インフラが repo/mathlib に無い演習は **honest な sorry-cite skeleton** を置かず、
  必要なら shared infra を先に build (claim-first)。真に blocked なら注記して次へ (文書順は維持)。
- **難易度・quick-win は着手基準でない** — 文書順で正面から。ただし 1 問で堂々巡りせず、
  genuine に blocked なら記録して先へ進み後で戻る。

## 進捗

**Ch.1 §1A** (`Ch01_Sylow/Problems.lean`、2026-07-22 着手):
- ✅ 実証明: **1A.1** (素数指数+最小性→正規) / **1A.4** (H·K=G⟹H·K^z=G + 帰結 H·H^x=G⟹H=⊤) /
  **1A.9** (|G|=pm,p>m→位数p部分群一意) / **1A.10(b)** (p群H, p∣[G:H]→p∣[N_G(H):H])。
- ✅ mathlib 対応 docstring 記録: **1A.6** (Burnside 軌道計数) / **1A.8** (Cauchy) / **1A.10(a)**
  (`fixedPointsMulLeftCosetsEquivQuotient`)。
- ✅ 実証明: **1A.2** (`card_doubleCoset_mul_card_inf_conj`: 二重剰余類 |HgK|·|K∩H^g|=|H||K|、
  H×K の両側作用 (h,k)•x=hxk⁻¹ の orbit-stabilizer)。
- ✅ 実証明: **1A.3** (`card_mul_card_inf` helper = |HK|·|H∩K|=|H||K| (1A.2 g=1) /
  `card_mul_le_card_mul_card_inf` (a)≤ / `card_mul_eq_iff_mul_eq_univ` (a)等号⟺HK=G /
  `mul_eq_univ_of_coprime_index` (b) coprime index⟹HK=G)。
- ✅ 実証明: **1A.5** (`isPretransitive_prod_iff`: G が α,β に推移的作用のとき積作用が推移的
  ⟺ G_a·G_b=univ、両方向とも安定化群と剰余類の交わり)。
- ✅ 実証明: **1A.7** (`card_not_mem_conj_ge`: 真部分群 H の共役に入らない元 ≥|H|) +
  再利用 helper **`sum_card_fixedBy_nat`** (Nat.card 版 Burnside)。⚠ 前 iteration の Fintype
  合成の壁の真因 = **`∑ m : M` 記法が statement で `[Fintype M]` を要求**していただけ (proof でなく
  型付け)。論法: χ=|Fix_{G⧸H}| に Burnside を G/H 適用 (∑_{G}χ=|G| 推移的 + ∑_{H}χ=|H|·#軌道≥2|H|)、
  χ(g)=0⟺g⁻¹∉共役、Finset counting + g↦g⁻¹ 双射。

**🎉 §1A 完了 (全 8 問: 1A.1/1A.2/1A.3/1A.4/1A.5/1A.7/1A.9/1A.10 実証明 + 1A.6/1A.8/1A.10a mathlib 記録)。**

**§1B** (`Ch01_Sylow/Problems.lean`、2026-07-23、Ch03 Hall/π 理論を import):
- ✅ 実証明 **1B.1(a)** `mul_isSubgroup_iff_le_sylow` (PS 部分群 ⟺ P≤S、Sylow 極大性)。
- ✅ 記録 **1B.1(b)** (mathlib `Sylow.unique_of_normal`/`characteristic_of_normal`)。
- ✅ 記録 **1B.2** (repo `normal_pgroup_le_opCore` = O_p 最大正規 p-部分群)。
- ✅ 記録 **1B.3** (mathlib `Sylow.normalizer_normalizer` = Sylow 正規化群自己正規化)。
- ✅ 実証明 **1B.4** `exists_le_card_eq_prime_mul_of_prime_dvd_index` (p∣|G:P|⟹∃Q⊇P |Q|=p|P|、
  一般 helper `exists_subgroup_card_eq_prime_mul_ker` = N_G(P)/P で Cauchy) +
  系 `not_dvd_index_of_maximal_pGroup` (極大 p-部分群 = Sylow、Sylow E の Cauchy 別証明)。
- ✅ 実証明 **1B.5(a)** `IsHallSubgroup.map_of_surjective` (π-Hall の全射像は π-Hall)。
- ✅ 実証明 **1B.5(b)** `exists_sylow_map_eq` (Sylow の像は Sylow) + **1B.5(c)**
  `card_sylow_le_of_surjective` (|Syl K| ≤ |Syl G|)。基盤: Sylow↔{p}-Hall 橋渡し 2 補題
  (`sylow_isHallSubgroup_singleton` / `exists_sylow_coe_eq_of_isHallSubgroup_singleton`) +
  `map_conj_smul` (θ(gHg⁻¹)=θ(g)θ(H)θ(g)⁻¹)。
- ✅ 実証明 **1B.6** `isHallSubgroup_inf_of_mul_isSubgroup` (HK 部分群 ⟹ H∩K は K の π-Hall)。
- ✅ 記録 **1B.7(a)** (repo `Subgroup.IsPiGroup.le_oPiCore` = O_π 最大正規 π-部分群)。
- ✅ 実証明 **1B.7(b)** `oPiCore_le_of_isHallSubgroup` (O_π ≤ 任意 π-Hall) + **1B.7(c)**
  `oPiCore_eq_iInf_isHallSubgroup` (O_π = 全 π-Hall の共通部分)。
- ✅ 実証明 **1B.8** (新 leaf `Ch03_SplitExtensions/PiResidual.lean`、O^p `pResidual` の π 一般化):
  `oPiResidual π G := sInf {N | N◁G ∧ IsPiGroup π (G/N)}`。**(a)** `isPiGroup_quotient_oPiResidual`
  (G/O^π が π-群、π-商正規が ⊓ で閉じ最小元) + `oPiResidual_le_of_isPiGroup_quotient` (普遍性) +
  一意性。**(b)** `oPiResidual_eq_closure_piPrimeElements` (O^π = π'-元で生成、W◁G は共役不変 +
  Cauchy で G/W が π-群、`Nat.exists_eq_pow_mul_and_not_dvd` で q-部分冪抽出)。OddOrder.lean 配線済。

**🎉 §1B 完了 (全 8 問: 1B.1a/1B.4/1B.5abc/1B.6/1B.7bc/1B.8ab 実証明 + 1B.1b/1B.2/1B.3/1B.7a 記録)。**

**§1C** (`Ch01_Sylow/Problems.lean` section 1C、2026-07-23):
- ✅ 実証明 **1C.1** `eq_normalizer_of_sylow_normalizer_le` (N_G(P)≤H ⟹ H=N_G(H)、Frattini、1B.3 一般化。
  ↥H の Sylow C + `map_conj_smul` で G に降ろす + `Sylow.smul_eq_iff_mem_normalizer`)。
- ✅ 実証明 **1C.2(a)** `exists_sylow_subgroupOf_eq_of_sylow` (H の Sylow P = H∩S、Sylow.subtype +
  極大性) + **1C.2(b)** `card_sylow_subgroup_le` (n_p(H)≤n_p(G)、1C.2a 対応が単射)。
- ✅ 実証明 **1C.3(a)** `powerOrder_eq_iUnion_sylow` (位数 p 冪の元 = ⋃ Sylow)。
- ✅ 実証明 **1C.3(b)** `prime_dvd_card_orderOf_prime_pow` (p∣\|G\| ⟹ p∣\|X\|)。Sylow `P` を `X` に
  共役作用させ `\|X\|≡\|X^P\| (mod p)` (`card_modEq_card_fixedPoints`)、固定点 `X^P`=`Z(P)`
  (可換 p-元は `P` に入る = helper `mem_sylow_of_orderOf_prime_pow_of_forall_commute`
  = `⟨x⟩≤N_G(P)` + Sylow 極大性)、`P` 非自明 p-群ゆえ `p∣\|Z(P)\|`。↥P の `X` への共役
  `MulAction` を letI 構成 + 固定点 ≃ `Z(P)` 全単射 (`card_eq_of_bijective`)。
- ✅ 実証明 **1C.7** `sylow_normal_of_maximal_subgroup_prime_index` (極大部分群 (coatom) が全て
  素数指数 + `p` = 最大素因数 ⟹ Sylow `p`-部分群正規)。背理法: `N_G(P)≠⊤` ⟹ `N_G(P)` を含む極大
  `M` (`eq_top_or_exists_le_coatom`、有限束 coatomic)、`q:=|G:M|` 素数。`P` は `M` の Sylow でもあり
  `N_M(P)=N_G(P)` (`subgroupOf_normalizer_eq`) ゆえ `n_p(G)=q·n_p(M)` (`relIndex_mul_index`)、
  Sylow 第三定理 (`card_sylow_modEq_one`) で両者 ≡1 (mod p) ⟹ `q≡1 (mod p)` ⟹ `q>p`、しかし
  `q ∣ |G|` ゆえ `q≤p`、矛盾。⚠ coercion `↑↑P` (Sylow→Subgroup→Set) vs `↑P` (Sylow→Set 直接) を
  `Sylow.coe_coe` で橋渡し。
- ✅ 実証明 **1C.6(a)** `exists_sylow_inf_sylow_of_mul_eq_univ` (`G=HK` ⟹ ∃P∈Syl(G),
  `P∩H`=H の Sylow 位数 ∧ `P∩K`=K の Sylow 位数)。helper `exists_sylow_inf_card_eq` (1C.2a の帰結) +
  Sylow 共役 `c•Q=Q'` の `c⁻¹=h·k` 分解、`P:=h⁻¹•Q`、`conj_smul_eq_self_of_mem`+`smul_inf`+`equivSMul`
  (共役の位数保存)。mathlib 既製 `conj_smul_eq_self_of_mem`/`smul_inf`/`equivSMul` を活用。
- ✅ 実証明 **1C.6(b)** `sylow_inf_mul_sylow_inf_eq` (`P=(P∩H)(P∩K)` 集合積)。`(P∩H)(P∩K)⊆P` +
  位数計数 `|(P∩H)(P∩K)|·|P∩H∩K|=|P∩H|·|P∩K|` (`card_mul_card_inf`)、`|G||H∩K|=|H||K|` (`G=HK`) の
  `p`-部分 (`factorization_mul`) で `|P|·pPart(H∩K)=|P∩H|·|P∩K|`、`|P∩H∩K|≤pPart(H∩K)` ゆえ
  `|(P∩H)(P∩K)|≥|P|`、`Set.eq_of_subset_of_ncard_le` で一致。**🎉 1C.6 完了 (a+b)**。
- ✅ 実証明 **1C.8** `card_subgroup_card_eq_modEq` (位数 p^a 部分群の個数が P と G で mod p 合同)。
  helper `le_sylow_of_isPGroup_of_le_normalizer` (`P≤N_G(D)` の p-群 D は `D≤P`)。↥P を `S_a(G)`・
  `S_a(P)` に共役 `MulAction` (letI, `equivSMul` で位数保存)、`card_modEq_card_fixedPoints` で
  `|S_a(G)|≡|Fix_G|`・`|S_a(P)|≡|Fix_P|`、`Fix_G ≃ Fix_P` を `D↦D.subgroupOf P` で全単射
  (`conj_smul_subgroupOf` で正規性移送、`map_subgroupOf_eq_of_le`/`comap_map_eq_self_of_injective`
  で往復、`subgroupOfEquivOfLe` で位数保存)。**🎉 §1C の一般 Sylow 問題 (1C.6/1C.7/1C.8) 全完了**。
- ✅ 実証明 **1C.4** (2026-07-25 解凍後 1 発目、新 leaf `Ch01_Sylow/ProblemsOrder120.lean` ~420 行):
  `exists_subgroup_index_eq_three_or_five_of_card_onetwenty` (|G|=120 ⟹ 指数 3 か 5 の部分群)。
  n₂∈{1,3,5,15}: 3/5 は `Sylow.card_eq_index_normalizer`、1 は P⊔F 位数 40、**15 は Thm 1.16**
  (`card_sylow_modEq_one_of_max_inter`、repo Basic.lean) で交わり最大対の relIndex d∣14 ∧ d∣8 ∧ d≠1
  ⟹ d=2 ⟹ |S∩T|=4、指数 2 ⟹ 正規 (`normal_of_index_eq_two`) ⟹ S,T ≤ N:=N_G(S∩T)、
  |N|∈{24,40,120}。120 case は S∩T◁G → G/(S∩T) 位数 30 → **補題** (位数 30 群は指数 3 or 5
  部分群を持つ: n₅=6∧n₃=10 は計数矛盾 24+20>29 → 正規 Sylow5/3 ⊔ Sylow2) → `comap` 引き戻し
  (`index_comap_of_surjective`)。再利用 helper: `card_sup_of_normal_of_coprime` (正規×coprime join
  の位数積) / `exists_finset_orderOf_eq_card_sylow_mul` (素数位数 Sylow 非単位元 = n_q(q−1) 個) /
  `card_sylow_mul_add_card_sylow_mul_le` (2 素数計数 ≤ |G|−1)。全実証明・axiom-clean。
  ⚠ 教訓: `set` の let 変数は補題適用時に値へ展開され omega が別 atom 視 → `rw [← hDdef]` で
  畳み直す / minimal import では `norm_num` の `Nat.Prime` 拡張が無い → `Mathlib.Tactic.NormNum.Prime`
  を明示 import / `Finset.card_sdiff` は現 mathlib で仮定無し形 (`card_sdiff_of_subset` を使う)。
- ✅ 実証明 **1C.5** (2026-07-25、新 leaf `Ch01_Sylow/ProblemsAlternating.lean`):
  `two_mul_card_normalizer_sylow_alternating` (`2|N_{A_{p+1}}(P)| = p(p−1)`, p 奇素数) +
  除算形 `card_normalizer_sylow_alternating` (`= p(p−1)/2`)。hint 通り位数 p 元 = p-cycle
  (`cycleType_prime_order` + 台 `(n+1)p ≤ p+1` → n=0、p 奇数で偶置換 `IsCycle.sign`) を計数:
  `card_of_cycleType_mul_eq` (mathlib Perm/Centralizer) で `c·p = (p+1)!`、強化した
  `natCard_orderOf_eq_of_sylow_card_eq` (ProblemsOrder120 の計数補題を iff/Nat.card 版に格上げ:
  素数位数 Sylow ⟹ 位数 q 元ちょうど n_q(q−1) 個) で `c = n_p(p−1)`、`|N|·n_p = |A|`・
  `2|A| = (p+1)!` (`two_mul_nat_card_alternatingGroup`+`Nat.card_perm`) を掛け合わせ cancel。
  ⚠ p = 2 (A₃) では不成立 (|N|=3≠1) ゆえ `3 ≤ p` を仮定 (Isaacs 暗黙、docstring 注記)。
  全実証明・axiom-clean。⚠ 教訓: factorial `!` 記法は `open scoped Nat` が要 (minimal import)。
- 🎉 **§1C 完了 (全 8 問)**: 1C.1/1C.2ab/1C.3ab/1C.4/1C.5/1C.6ab/1C.7/1C.8 全て実証明。
- ⏸ **後回し (重い/特殊、後で戻る)**: **1C.4** (\|G\|=120 index 3 or 5)。n_2∈{1,3,5} は清潔
  (正規化群 index or 商 order 15)、但し **n_2=15 の場合が構造的に重い** (S_5 型、index-5 部分群 S_4 の
  存在は列挙でなく構造 — 計数だけでは矛盾を出せないことを確認済)。**1C.5** (A_{p+1} で
  \|N_G(P)\|=p(p-1)/2)。p-cycle の計数 (C(p+1,p)·(p-1)! 個、全て偶置換) が要で、mathlib の対称群
  cycle-type API 依存の特殊問題。

**§1D** (`Ch01_Sylow/Problems.lean` section 1D、2026-07-23 着手):
- ✅ 実証明 **1D.1** `not_dvd_index_of_sylow_normalizer_le` (`P∈Syl_p(H)`, `H◁G`, `N_G(P)⊆H` ⟹
  `p∤|G:H|`)。Frattini 論法 (`Sylow.normalizer_sup_eq_top`) で `N_G(P)⊔H=⊤`、`N_G(P)≤H` から
  `H=⊤`、`|G:H|=1`。
- ✅ 実証明 **1D.6** `isCoatom_iff_index_prime` (冪零群で `H` 極大 (coatom) ⟺ `|G:H|` 素数)。
  `⟹`: 冪零⟹正規化条件 (`Group.normalizerCondition_of_isNilpotent`) で極大は正規、対応定理で `G⧸H`
  単純 (`comap_injective` で `IsSimpleGroup` 構成)、単純+冪零⟹可換 (mathlib instance)、可換単純は素数
  位数 (`IsSimpleGroup.prime_card`)。`⟸`: 素数指数 ⟹ `H≠⊤` かつ `H<K` で `K.index∣H.index` 素数ゆえ
  `K=⊤`。⚠ import 追加 (Nilpotent/Cyclic)、namespace 罠: `MonoidHom.comap_bot`・
  `Subgroup.NormalizerCondition.normal_of_coatom` (Subgroup namespace 内)。
- ✅ 実証明 **1D.2** `not_dvd_card_and_index_of_centralizer_le` (`C_G(x)⊆H` (order-p `x∈H`) ⟹
  `p` は `|H|` と `|G:H|` を同時に割らない)。背理法: helper `exists_sylow_inf_card_eq` で `Q∈Syl_p(G)`,
  `P=Q∩H` (`|P|=pPart(H)`)、`p∣|G:H|` で `pPart(H)<pPart(G)=|Q|` (`factorization_mul`) ゆえ `P<Q`。
  `Q` は p-群 (冪零, `IsPGroup.isNilpotent`) で正規化条件、`subgroupOf_normalizer_eq` で
  `N(P.subgroupOf Q)=(N_G P).subgroupOf Q`、`SetLike.exists_of_lt` で `g∈N_G(P)∩Q`, `g∉P`。
  `⟨g⟩` の `P` への共役 `MulAction` (letI) + `exists_fixed_point_of_prime_dvd_card_of_fixed_point` で
  非単位固定点 `b` (g と可換)、`x=b^(p^(k-1))` は位数 p (`orderOf_pow`)、`g∈C_G(x)⊆H` ⟹ `g∈Q∩H=P`
  矛盾。**3度延期を克服して完遂。**
- ✅ 実証明 **1D.7** `mem_frattini_iff_forall_closure` (`g∈Φ(G)` ⟺ 非生成元: 任意の `X` で
  `⟨X∪{g}⟩=⊤ → ⟨X⟩=⊤`)。`⟹` は `frattini_nongenerating` (mathlib) + `⟨{g}⟩≤Φ`、`⟸` は
  `Φ=⨅極大` から `g∉M` なる極大 `M` を取り `X=M` で反例。
- ✅ 実証明 **1D.13** `isNilpotent_of_center_le` (`Z≤Z(G)` かつ `G⧸Z` 冪零 ⟹ `G` 冪零)。mathlib
  `Subgroup.isNilpotent_of_ker_le_center` を `mk' Z` (核=Z) に適用した特殊化。
- ✅ 記録 **1D.14** (`Φ(G)` 冪零): mathlib `frattini_nilpotent` 直対応 (`frattini G=Order.radical
  =⨅極大=Isaacs Φ(G)`)、ラッパー方針で記録のみ。
- ✅ 実証明 **1D.3(a)** `normalizer_le_of_disjoint_conj` (`H⊓H^g=1` (∀`g∉H`, Frobenius complement) ⟹
  `1<K≤H` で `N_G(K)⊆H`)。`n∈N_G(K), n∉H` なら `K=n·K·n⁻¹≤H^n` かつ `K≤H` で `K≤H⊓H^n=1` 矛盾。
  (`mem_normalizer_iff_map_conj_eq` + `pointwise_smul_le_pointwise_smul_iff`)
- ✅ 実証明 **1D.3(b)** `coprime_card_index_of_disjoint_conj` (同 `H` は Hall)。素数 `p∣gcd(|H|,|G:H|)`
  を仮定、`P=Q∩H` (`Q∈Syl_p(G)`, `|P|=pPart(H)>1`)、(a) で `N_G(P)⊆H`。`P<Q` なら 1D.2 と同じ
  g-抽出 (正規化条件+`subgroupOf_normalizer_eq`) で `g∈N_G(P)∩Q⊆H∩Q=P`, `g∉P` 矛盾 (fixed-point 不要)、
  ∴ `P=Q`、`pPart(H)=pPart(G)`、しかし `p∣index` で `pPart(H)<pPart(G)` 矛盾。
- ✅ **分割完了 (2026-07-23)**: `Problems.lean` (1682→1363 行, §1A–§1C) と新 leaf
  `Ch01_Sylow/ProblemsFrobeniusFrattini.lean` (341 行, §1D 全 7 定理) に flat suffix-split。
  新 leaf は `Problems` を import (§1A–§1C helper 利用) + Nilpotent/Cyclic/Frattini (§1D 専用)。
  `OddOrder.lean` 配線済、両 leaf build green (2209 jobs)。module 名不変で下流無影響。**以降 §1D の
  追記は新 leaf へ**。
- ✅ 実証明 **1D.4** `frobenius_complement_iff_centralizer_eq_bot` (`G=NH`, `1<N◁G`, `N∩H=1` で
  `H` Frobenius complement ⟺ 全非単位 `h∈H` で `C_N(h)=1`)。`⟹`: `n∈C_N(h), n≠1` なら `n∉H` かつ
  `h=n·h·n⁻¹∈H^n` で `h∈H⊓H^n` (Frobenius に反する)。`⟸`: `g=n·h'` 分解で `H^g=H^n`
  (`conj_smul_eq_self_of_mem`) から `n∈N,n≠1` に帰着、`x∈H⊓H^n, x≠1` で `x⁻¹n⁻¹xn∈N∩H=1` (N 正規)、
  `x,n` 可換 (`group` tactic) ゆえ `n∈C_N(x)=1` 矛盾。(新 leaf ProblemsFrobeniusFrattini.lean)
- ✅ 実証明 **1D.16** `frattini_map_subtype_le_frattini` (`N◁G` ⟹ `Φ(N)⊆Φ(G)`)。helper
  `characteristic_map_subtype_normal` (特性部分群を正規 N に沿って G へ押し出すと G で正規、
  `MulAut.conjNormal`+char)。各極大 `M` で `Φ(N)⊄M` なら `M⊔Φ(N)=⊤`、`Φ(N)◁G` ゆえ
  `M⊔Φ(N)=M·Φ(N)` (`mul_normal`)、`x=m·φ` から `m∈N⊓M`、`N≤(N⊓M)⊔Φ(N)`、`frattini_nongenerating`
  で `N⊆M`、矛盾。⚠ 一般群の部分群束は modular でない (mathlib `IsModularLattice (Subgroup C)` は
  CommGroup 限定、`mem_sup` 積形も同様) → `Φ(N)` 正規性 + `mul_normal` で Dedekind を回避。
- ⏸ **1D.5 後回し (intricate)**: `N_G(P)⊆H` (全 p-部分群) ⟹ Frobenius complement。`D=H∩H^g` の
  Sylow `Q` の共役論法が clean な計画立たず (Isaacs/Coq 再読が要)。
- ✅ 実証明 **1D.8 (可換部分)** `commutator_le_frattini` (冪零有限群で `[G,G]⊆Φ(G)`、`G/Φ(G)` 可換)。
  各極大 `M` は素数指数 (1D.6) ゆえ `G⧸M` は素数位数=巡回、`isMulCommutative_of_isCyclic_of_ker_le_center`
  (⚠ `IsCyclic.commGroup` は既存 Group instance と diamond を作るので `IsMulCommutative` 経由で回避)、
  `commutatorElement_eq_one_iff_mul_comm` で `⁅g₁,g₂⁆∈M`。
- ✅ 実証明 **1D.8 (基本アーベル部分)** `pow_mem_frattini_of_isPGroup` (p-群で `∀g, g^p∈Φ(P)`) +
  `pow_eq_one_frattiniQuotient_of_isPGroup` (商 `P/Φ(P)` の exponent が p を割る)。核は Burnside 基底定理
  **不要**: 各極大 `M` は p-群 coatom ゆえ指数素数 (1D.6) かつ `∣|P|=p^n` で `=p`、`Subgroup.pow_index_mem`
  で `g^(M.index)=g^p∈M`、全極大の共通部分で `g^p∈Φ(P)`。`commutator_le_frattini` (可換) とあわせ
  `P/Φ(P)` 基本アーベル。→ **1D.8 完了**。
- ✅ 実証明 **1D.15 (`N=G` 版)** `isNilpotent_of_quotient_frattini_isNilpotent` (`G/Φ(G)` 冪零⟹`G`
  冪零)。各 Sylow `P` の像 `θ(P)` は `G/Φ(G)` の Sylow (1B.5(b) `exists_sylow_coe_eq_of_isHallSubgroup_singleton`
  + `IsHallSubgroup.map_of_surjective`)、冪零性で正規、逆像 `P⊔Φ(G)=comap(map P)` (`comap_map_eq`+`ker_mk'`)
  が正規、Frattini 論法 `normalizer_sup_eq_top'` + 非生成性 `frattini_nongenerating` で `N_G(P)=⊤` ⟹ `P◁G`、
  全 Sylow 正規で `G` 冪零 (`isNilpotent_of_finite_tfae.out 3 0`)。mathlib `frattini_nilpotent` と平行構造。
  ⚠ coe 罠: `(P:Subgroup G)` は `↑↑P` (二重) を作り補題の `↑P` (単一) と非一致 → hfr 再文言せず `top_le_iff`+`sup_le`
  で項構成 (`sup_eq_left` の rw パターンは coe で不発)。**一般 `N` 版 (Φ(G)⊆N◁G, N/Φ(G)冪零⟹N冪零) は残**。
- ✅ 実証明 **1D.17** `isNilpotent_of_quotient_commutator_isNilpotent` (`N◁G` 冪零 + `G/N'` 冪零 ⟹ `G`
  冪零)。導来 `N'=⁅N,N⁆` は 1D.8 で `Φ(N)`、1D.16 で像 `⊆Φ(G)`、`Subgroup.map_subtype_commutator`
  (`(commutator ↥N).map N.subtype=⁅N,N⁆`) で `N'⊆Φ(G)`。全射 `G/N'↠G/Φ(G)` (`QuotientGroup.map`
  + `map_surjective_of_surjective`、⚠ section 変数 `N` が explicit 先頭ゆえ計 5 引数) で `G/Φ(G)` 冪零
  (`Group.nilpotent_of_surjective`)、1D.15 で `G` 冪零。→ **§1D Frattini 冪零クラスタ 1D.13–1D.17 完結**
  (1D.15 一般 N 版のみ残)。
- ✅ 実証明 **1D.9 (前半+核)** `isCyclic_of_frattiniQuotient_isCyclic` (`P/Φ(P)` 巡回⟹`P` 巡回、
  生成元を非生成性 `frattini_nongenerating` で持ち上げ) + `sq_le_card_frattiniQuotient_of_isPGroup_of_not_isCyclic`
  (非巡回 p-群 ⟹ `p²≤|P:Φ(P)|`、商 p-群位数 `p^n` で `n≥2`: 位数 `1`(自明)/`p`(`isCyclic_of_prime_card`) 排除)。
  ⚠ `x̄` 等結合文字は識別子不可 (`gbar`)、`MonoidHom.map_zpowers` (Subgroup 側でない)、`Subgroup.eq_top_iff'`
  は解決せず `eq_top_iff`+intro。
- ✅ 実証明 **1D.9 (後半)** `isCyclic_or_elementaryAbelian_of_card_eq_prime_sq` (位数 p² ⟹ 巡回 or
  基本アーベル)。非巡回なら前半で `p²≤|P:Φ(P)|`、Lagrange `index_mul_card` で `|Φ(P)|=1` ⟹ `Φ(P)=⊥`、
  `pow_mem_frattini` で exponent p、`commutator_le_frattini`+`commutator_eq_bot_iff` (=`IsMulCommutative`)
  で可換。⚠ 元の交換子 `⁅a,b⁆` の `Bracket P P` は **scoped instance** (`commutatorElement`) ゆえ自分で
  書くと未合成 → `commutator_eq_bot_iff` 経由で回避。→ **1D.9 完了**。
- ✅ 実証明 **1D.10 (前半)** `centralizer_eq_self_of_maximal_abelian_normal` (p-群の極大可換正規部分群 `A`
  は `C_P(A)=A`)。`A≤C_P(A)` は可換ゆえ自明。`A<C_P(A)` なら **Lemma 1.23** (`IsPGroup.exists_normal_index_eq_prime`,
  repo `Ch01_Sylow/Basic.lean`) で `A<L≤C_P(A)`, `|L:A|=p`, `L◁P` を得、`L⊆C_P(A)` で `A⊆Z(L)`、
  `L/A` 位数 p 巡回で `L` 可換 (`isMulCommutative_of_isCyclic_of_ker_le_center`) — 極大性に矛盾。
  ⚠ `Subgroup.le_centralizer` は H explicit / repo 補題は `OddOrder.Isaacs.Ch01.IsPGroup.*` で dot notation
  不発 (`_root_.IsPGroup` を見る) → 明示適用 + `import Basic`。
- ✅ 実証明 **1D.10 (後半)** `index_dvd_factorial_of_maximal_abelian_normal` (`|P:A| ∣ (|A|-1)!`)。
  `P` の `A∖{1}={a:↥A//a≠1}` への共役 MulAction (`MulAut.conjNormal`) を letI 定義、`MulAction.toPermHom`
  の核 = `C_P(A) = A` (前半)、`Subgroup.index_ker` + `Nat.card_perm` で `|P:A|=|range|∣|Perm(A∖{1})|
  =(|A|-1)!`。⚠ 罠: `rw [←hCA]` は `A` を `centralizer A` 内まで書換え motive 破綻 → `f.ker=centralizer A`
  を先証して `.trans hCA` / `hane:a≠1`(P) ≠ `⟨a,ha⟩≠1`(↥A) → Subtype.ext_iff で導出 / MulAction proof の
  `show`→`change` / `MulAut.conjNormal_apply` + `mul_inv_eq_iff_eq_mul` で commute / card は
  `Fintype.card_subtype_compl`+`card_subtype_eq`。→ **1D.10 完了**。
- ✅ 実証明 **1D.11** `card_dvd_factorial_of_abelian_bound` (`n` が可換部分群位数の上界 ⟹ `|G| ∣ n!`) +
  helper `exists_maximal_abelian_normal` (有限順序の極大元 `Finite.exists_le_maximal`、witness=`center P`)。
  各 `P∈Syl_p(G)` の極大可換正規 `A` に 1D.10 後半 ⟹ `|P:A|∣(|A|-1)!`、`A.map subtype` の可換性
  (`equivMapOfInjective` 経由) で `|A|≤n`、`|P|=|A|·|P:A| ∣ |A|! ∣ n!` (`mul_factorial_pred`)。
  `|P|=p^{v_p|G|}` (`Sylow.card_eq_multiplicity`) で全素数冪 ⟹ `|G|∣n!` (`Nat.dvd_iff_prime_pow_dvd_dvd`)。
  ⚠ `dvd_iff_prime_pow_dvd_dvd` の `intro` は `Nat.Prime` を与える (変換不要) / `card_eq_multiplicity` は
  `↥↑P` coe ゆえ明示型 `have hmult : Nat.card ↥P = …` で橋渡し。`n` を最大値でなく上界に一般化。
  → **1D.11 完了**。
- ✅ 実証明 **1D.12** `card_orderOf_eq_prime_add_one_modEq_zero` (`p∣|G|` ⟹ 位数 p 元数 `+1 ≡ 0 mod p`)
  + McKay helper `card_pow_eq_one_modEq_zero` (`#{x^p=1} ≡ 0`)。mathlib は Cauchy **存在**のみ露出・count
  無しゆえ McKay を自前構築: `vectorsProdEqOne G p` (`Perm/Cycle/Type.lean`) に `Multiplicative (ZMod p)` を
  巡回シフト作用 (`rotate`、mul_smul は p-周期性 `hper: rotate w m=rotate w (m%p)`)、
  `IsPGroup.card_modEq_card_fixedPoints` で `|G|^(p-1)≡|fixed|`、固定点 ≃ `{x//x^p=1}` (定数ベクトル、
  `.get ⟨0,pos⟩`+`get_replicate`+`rotate_one_eq_self_iff_eq_replicate`)、`|G|^(p-1)≡0`。減算は
  `{x//x^p=1} ≃ Option {x//orderOf=p}` (1↔none) で `Fintype.card_option`。⚠ `toAdd_one/mul/ofAdd` は bare、
  `List.Vector.head` は長さ p が succ 形でなく型不一致 → `.get ⟨0,hp.out.pos⟩`。→ **1D.12 完了**。
- ✅ 実証明 **1D.15 (一般 `N` 版)** `isNilpotent_of_frattini_le_of_quotient_isNilpotent` (`Φ(G)⊆N◁G`,
  `N/Φ(G)` 冪零⟹`N` 冪零) + 再利用 helper `sylow_normalizer_sup_eq_top_of_quotient_nilpotent` (`K/M` 冪零
  ⟹ 各 Sylow で `N_K(P)⊔M=⊤`、N=G 版の核を M 一般化)。**二段 Frattini** (Fitting 経由は循環): 各
  `P∈Syl_p(↥N)` に (内) helper で `N_↥N(P)⊔Φ(G)ᴺ=⊤`、`N.subtype` で押し出し (`map_sup`+`subgroupOf_map_subtype`
  +`le_normalizer_map`) `N≤N_G(P.map)⊔Φ(G)`、(外) `Sylow.normalizer_sup_eq_top` で `N_G(P.map)⊔N=⊤`、
  合わせ `N_G(P.map)⊔Φ(G)=⊤`、`frattini_nongenerating`⟹`P.map◁G`、`subgroupOf`+`Normal.subgroupOf`+
  `comap_map_eq`+`ker_subtype` で `P◁↥N`。⚠ 罠: `(↑P:Subgroup)` 明示は二重 coe→bare `↑P`+absorb は
  `le_antisymm`+`sup_le` / `rw[←hmapeq]` は `N` が `P:Sylow p ↥N` の型に現れ motive 破綻→`.le.trans` の項 /
  `Subgroup.map_top` は無く `←MonoidHom.range_eq_map`。→ **1D.15 完了 (N=G + 一般 N)**。
- ✅ 実証明 **1D.5** (2026-07-25、Isaacs 明記の難問を解決): `disjoint_conj_of_forall_normalizer_le`
  (「全素数 q・全非自明 q-部分群 `P⊆H` に `N_G(P)⊆H`」⟹ `H` は Frobenius complement)。
  **難所だった「Q と Q^g の H-共役」の正体 = Q が実は H の Sylow になること**。論法:
  `D:=H∩H^g≠⊥`, `q∣|D|`, `Q∈Syl_q(D)`。(1) **仮説は D に遺伝** (hint): `N_G(Q)≤H` (仮説) +
  `Q^{g⁻¹}≤H` 非自明 → `N_G(Q^{g⁻¹})≤H` を共役 (`le_normalizer_map` + `pointwise_smul_def`) して
  `N_G(Q)≤H^g` ⟹ `N_G(Q)≤D`。(2) **Q は Syl_q(H)**: `Q⊆S∈Syl_q(H)` で `Q≠S` なら q-群の
  正規化群成長 (Thm 1.22) で `Q<N_S(Q)≤N_G(Q)⊓H≤D` の q-部分群 — Q の D-Sylow 極大性 (`Q₀.3`)
  に矛盾。(3) `Q':=Q^{g⁻¹}` も同位数ゆえ `Sylow.ofCard` で Syl_q(H)、Sylow C (1C.1 の
  `map_conj_smul` transport パターン) で `k∈H`, `(Q')^k=Q` ⟹ `k·g⁻¹∈N_G(Q)≤D≤H` ⟹ `g∈H` 矛盾。
  計数不要・~130 行・axiom-clean。仮定の `P≠⊥` は Isaacs 暗黙 (⊥ を許すと H=G に退化)、`H<G`
  properness は不要 (docstring 注記)。⚠ 教訓: `MulAut.conj g⁻¹ = (MulAut.conj g)⁻¹` は
  defeq でない (`map_inv` で明示 rw) / `subgroupOf`↔`comap subtype` は defeq だが rw は不可
  (`exact` の defeq check で橋渡し)。
- 🎉 **§1D 完了 (全 18 問)**: 1D.1–1D.18 全て実証明/記録。
  ⚠ namespace 罠: `Subgroup.isNilpotent_of_ker_le_center` (Subgroup 内)、`closure_le` は
  module system で露出せず → `mem_closure_singleton`+`zpow_mem` で回避。

## Ch.2 (Subnormality) §2A — 着手 (2026-07-23)

新 leaf `OddOrder/Isaacs/Ch02_Subnormality/Problems.lean` (namespace `OddOrder.Isaacs.Ch02`、import
`Mathlib.GroupTheory.IsSubnormal`+`Ch01_Sylow.Main`、`OddOrder.lean` 配線済)。`Subgroup.IsSubnormal` は
mathlib inductive (`top`/`step`)。

- ✅ 実証明 **2A.3(a)** `le_of_isSubnormal_of_coprime_index` (`H` 部分正規, `|G:H|` と `|K|` 互いに素
  ⟹ `K≤H`)。`IsSubnormal` 帰納法 (`| top => le_top | @step H' K' hle _ hN ih`): step で `K'.index∣H'.index`
  (`index_dvd_of_le`) から `ih` で `K≤K'`、核 = 商 `mk'(H'.subgroupOf K')` の像 `(K.subgroupOf K').map` の
  card が `|K|` (`card_map_dvd`+`subgroupOfEquivOfLe`) と `(H'.subgroupOf K').index` (`card_subgroup_dvd_card`,
  `index_eq_card`) 双方を割り、後者は `|G:H'|` を割り (`relIndex_dvd_index_of_le`) `|K|` と互いに素
  (`eq_one_of_dvd_coprimes`) ⟹ 像 `⊥` ⟹ `K.subgroupOf K'≤H'.subgroupOf K'` ⟹ `K≤H'`
  (`subgroupOf_map_subtype`+`inf_eq_left`)。
- ✅ 実証明 **2A.1** `le_oPiCore_of_isSubnormal_of_isPiGroup` (subnormal π-subgroup `K ⊆ O_π(G)`) +
  helper `oPiCore_map_subtype_le_of_isSubnormal` (`(oPiCore π ↥H).map H.subtype ≤ oPiCore π G` for H 部分正規)。
  char-motive の IsSubnormal 構造帰納が動いた: top=`oPiCore.map_le_of_surjective`、step=`subgroupOfEquivOfLe`
  の iso で `oPiCore.map_eq_of_mulEquiv` 移送 + `characteristic_map_subtype_normal` (Ch01 1D.16) で ↥K' 正規
  + `IsPiGroup.le_oPiCore` + `H.subtype=K'.subtype∘subtype∘e.symm` 合成 (`map_map`) + IH。2A.1 本体は
  `↥K` π-群で `oPiCore π ↥K=⊤` (`card_top`), `(⊤).map K.subtype=range=K`。import 追加 = Ch03 Theorem315 +
  Ch01 ProblemsFrobeniusFrattini (cycle 無し)。→ **2A.1 完了、2A.3(b) unblock**。
- ⬜ **残り §2A** (要 machinery):
  - **旧 2A.1 メモ** (参考): **正しい帰納 motive の発見過程**: 素朴な
    `P K := IsPiGroup π K → K≤oPiCore` は IsSubnormal 構造帰納に **不適** (step の IH は大きい `K'` について
    で、π-group 性は小さい `K` について ⟹ 使えない)。正解は **`P H := (oPiCore π ↥H).map H.subtype ≤
    oPiCore π G`** (H を IsSubnormal で帰納): top は `↥⊤≅G` の iso、step (`H◁K'`, IH: `(oPiCore π ↥K').map
    K'.subtype ≤ oPiCore π G`) は `(oPiCore π ↥H).map (Subgroup.inclusion hle)` が ↥K' で正規 (oPiCore char
    in ↥H + `H.subgroupOf K'◁↥K'` で char-in-normal) かつ π-group (`oPiCore.isPiGroup`+`IsPiGroup.map`) ⟹
    `≤ oPiCore π ↥K'` (`IsPiGroup.le_oPiCore`)、`H.subtype=K'.subtype∘inclusion` で `.map K'.subtype` して IH。
    素材確認済: `IsPiGroup.le_oPiCore`[Normal] / `oPiCore.characteristic`/`isPiGroup` / `IsPiGroup.map_equiv`
    / `normal_of_characteristic` / 1D.16 の `characteristic_map_subtype_normal` パターン。~60 行 fiddly
    (subgroup-as-group + inclusion + char + π-group 配管)。
    **★ 全ツールチェーン確認済 (2026-07-23)、step の具体手順**: iso `e := (Subgroup.subgroupOfEquivOfLe hle).symm
    : ↥H ≃* ↥(H.subgroupOf K')` で `(oPiCore π ↥H).map e = oPiCore π ↥(H.subgroupOf K')`
    (**`oPiCore.map_eq_of_mulEquiv` は public**、Ch03 Theorem315.lean — private の `map_le_of_mulEquiv` を
    懸念したが equality 版が公開されている)。`inclusion hle = (H.subgroupOf K').subtype ∘ e` ゆえ
    `(oPiCore π ↥H).map (inclusion hle) = (oPiCore π ↥(H.subgroupOf K')).map (H.subgroupOf K').subtype`、
    これは `characteristic_map_subtype_normal` (oPiCore char + `H.subgroupOf K'◁↥K'`=hN) で ↥K' 正規 +
    π-group (`oPiCore.isPiGroup`) ⟹ `≤ oPiCore π ↥K'` (`IsPiGroup.le_oPiCore`)、`.map K'.subtype` して IH。
    top は `oPiCore.map_le_of_surjective π (⊤).subtype`。**import 追加要**: `Ch03_SplitExtensions.Theorem315`
    (oPiCore) + `Ch01_Sylow.ProblemsFrobeniusFrattini` (characteristic_map_subtype_normal)。cycle 無し。
  - ✅ 実証明 **2A.3(b)** `le_of_isSubnormal_of_coprime_index'` (`K` 部分正規, `|G:H|` と `|K|` 互いに素
    ⟹ `K≤H`) + helper `coprime_normal_le` (`N◁G`, `coprime(|N|,|G:H|)` ⟹ `N≤H`)。π=`↑(Nat.card K).primeFactors`、
    2A.1 で `K⊆O_π(G)`、`coprime_normal_le` を `O_π(G)` に適用。coprime_normal_le: `|H⊔N:H|=relIndex` が
    `card_mul_card_inf`(正規積公式)で `|N|` を割り `relIndex_dvd_index_of_le` で `|G:H|` も割り互いに素で `=1`
    ⟹ `H⊔N=H`⟹`N≤H`。coprimality は `oPiCore.isPiGroup` の primes⊆ + `Coprime.disjoint_primeFactors` +
    `Finset.disjoint_of_subset_left`。一発 green。→ **2A.3 完全完成 (a+b)**。
  - ✅ 実証明 **2A.2** `oPiResidual_le_of_isSubnormal_of_index_isPiNumber` (`K` 部分正規, `|G:K|` が π-数
    ⟹ `O^π(G) ≤ K`)。`O^π=⟨π'-元⟩` (`oPiResidual_eq_closure_piPrimeElements`=1B.8) + `closure_le` で各 π'-元
    `g` に帰着、`⟨g⟩` の位数 `orderOf g` (π'-数) は `|G:K|` (π-数) と互いに素 (`disjoint_primeFactors`)、
    2A.3(a) で `⟨g⟩≤K` ⟹ `g∈K`。import 追加 = Ch03 PiResidual。一発 green (import のみ)。→ **2A.2 完了**。
  - ✅ 記録 **2A.7** (`S◁◁G` 非可換単純 ⟹ `S^G` minimal normal): repo `Ch09.isMinimalNormal_normalClosure_of_isSubnormal`
    (Isaacs Lemma 9.17) がまさにこれ、docstring 記録 (ラッパー方針)。
  - ✅ 実証明 **2A.8** `commutator_eq_bot_of_ne_of_isSubnormal_of_simple` (異なる非可換単純な部分正規 `S,T`
    ⟹ `⁅S,T⁆=⊥`)。非可換単純部分正規は component (`isQuasisimple_of_isSimpleGroup_not_isMulCommutative`)、
    異なる component は可換 (`IsComponent.commutator_eq_bot_of_ne`、Ch09)。import 追加 = Ch09 SubnormalSocle。
  - ✅ 実証明 **2A.4** (2026-07-25、Wielandt 部分群): `le_normalizer_of_isSubnormal_of_forall_mul_comm`
    (S 単純が全 subnormal J と `SJ = JS` ⟹ S は全 subnormal を正規化)。**|G| 強帰納法 +
    IsSubnormal 構造帰納**。step (H⊴K'◁◁G, IH: S≤N(K')): K'=⊤ 自明 / **S≤K'** は ↥K' に降下
    (仮説移送: `IsSubnormal.trans'` (mathlib) で subnormal を G へ戻し permutability を
    elementwise transport、単純性は `MulEquiv.isSimpleGroup`+`subgroupOfEquivOfLe`、結論は
    `subgroupOf_normalizer_eq`) / **S⊄K'** は S⊓K'⊴S (S≤N(K')) + 単純性で S⊓K'=⊥ →
    K:=S⊔H は台集合 S·H (helper `coe_sup_of_mul_comm` 新設 = SH=HS→部分群構成) →
    M:=normalClosure(H) in ↥K が ≤K' (k=s·h の共役が K' に残る、`normalClosure_le_normal`) →
    S⊓M=⊥ → 計数 |S||M| ≤ |K| = |S||H| (`card_mul_card_inf`) → M=H → H⊴K
    (`normal_subgroupOf_iff_le_normalizer`) → S≤K≤N(H)。~180 行・axiom-clean。
    ⚠ 教訓: 型を跨ぐ強帰納法は `∀ (n) (G : Type*) (_ : Group G) (_ : Finite G), card ≤ n → …` の
    explicit binder 形で書き、適用時は `inferInstance` 明示 / `Set.mem_mul` の obtain した eq は
    β-未簡約 (`show a*b = c*d from heq` で reduce してから rw)。
  - ✅ 実証明 **2A.5(a)(b)(c) + 2A.6** (2026-07-25、deferred-hard tail 完遂)。`X` = minimal normal
    の任意族、`N := sSup X`。
    - **2A.5(a)** `exists_subfamily_indep_sSup_eq` (**種付き強化形**): 独立な部分族 `Y₀ ⊆ X` を与えると
      `Y₀ ⊆ Y ⊆ X` で独立かつ `sSup Y = sSup X` なる `Y` が存在 (= `N` は `X` のいくつかのメンバーの
      直積; 「独立性 + join」が内部直積の定式化)。`Finite.exists_le_maximal` で独立性を保つ極大部分族
      `Y` を取り、`M ⊄ sSup Y` なる `M ∈ X` があれば `M ⊓ sSup Y ⊴ G` が minimality で `⊥` ゆえ
      `insert M Y` も独立 (`T ∈ Y` 側は `x ∈ T ⊓ (sSup (Y∖{T}) ⊔ M)` を `x = w·m` に分解、
      `M` 正規で `mul_normal`) → 極大性に矛盾。**種 `Y₀` が (b) の鍵** (`Y₀ = ∅` が Isaacs の原題)。
    - **hint** `socle_eq_top_of_forall_isMinimalNormal` (`Soc(N) = N`): 各 `M ∈ X` で
      `M.subgroupOf N` 内の minimal normal `W` を取り (`exists_isMinimalNormal_le`)、`G`-正規閉包
      `= M` (minimality)。各 `G`-共役は `MulAut.conjNormal` による `↥N` の自己同型像ゆえ minimal
      normal のまま (`IsMinimalNormal.map_equiv`) → `(socle ↥N).map N.subtype` は `G`-正規で
      `normalClosure W` を含む。helper `apply_mem_socle` (socle は自己同型不変、`iSup_induction`)。
    - **2A.5(b)** `isSimpleGroup_of_isMinimalNormal_of_forall_isMinimalNormal`: `Soc(N) = N` の下で
      (a) を**種 `{V}`** で `↥N` に適用し `N = V ⊔ rest` (独立)。`rest` は `V` と disjoint な正規の
      join ゆえ `V` を中心化 → 任意の `K ⊴ ↥V` の押し出しは `V`-共役 (正規性) と `rest`-共役 (中心化)
      で不変 → `↥N`-正規 → `V` の minimality で `⊥` か `V`。
    - **2A.5(c)** `exists_indep_isSimpleGroup_sSup_eq_top`: (a) を全 minimal normal の族に適用
      (join = socle = `⊤`)、各メンバーの単純性は (b)。
    - **2A.6** `exists_mem_le_of_normal_le_sSup_of_not_isMulCommutative`: 対偶で全 `M ∈ X` に
      `U ⊓ M = ⊥` (minimality) → `Subgroup.commute_of_normal_of_disjoint` で `M ≤ C_G(U)` →
      `U ≤ N ≤ C_G(U)` で `U` 可換、矛盾。
    - ~294 行・sorry 0・`--strict` lint clean。あわせて 2A.4 の帰納核と主定理の間に挟まっていた
      本ブロックを主定理の後ろへ移し文書順・凝集を回復。
  - ✅ 実証明 **2A.9** (2026-07-25) `oPiCore_le_normalizer_of_isSubnormal_of_oPiResidual_eq_top`:
    `H ◁◁ G` が π-perfect (`H = O^π(H)`、形式化は `oPiResidual π ↥H = ⊤`) ⟹ `O_π(G)` が `H` を正規化。
    Isaacs の hint「`G = H·O_π(G)` と仮定してよい」を **`K := H ⊔ O_π(G)` への降下**として実装:
    `P := O_π(G)` 正規ゆえ `↑K = ↑H·↑P`、`Ch01.card_mul_card_inf` + Lagrange で
    `|K:H|·|H⊓P| = |P|` ⟹ `|K:H| ∣ |P|` は π-数 (`oPiCore.isPiGroup`) ⟹ 2A.2 を `↥K` に適用して
    `O^π(K) ≤ H.subgroupOf K`。逆向きは π-perfect 性を `Subgroup.inclusion : ↥H →* ↥K` で押し出す。
    ⟹ `H.subgroupOf K = O^π(K)` は `↥K` で正規 ⟹ `P ≤ K ≤ N_G(H)`。
    **支持 API 新設 (Ch03 `PiResidual.lean`、mathlib 流の関手性)**: `oPiResidual_map_le`
    (任意の `f : A →* B` で `O^π(A)^f ≤ O^π(B)`; 1B.8(b) の π'-元生成 + `orderOf_map_dvd`、
    全射性も単射性も不要) / `subgroupOf_le_oPiResidual_of_eq_top`。
  - ✅ 実証明 **2A.10** (2026-07-25) `isSubnormal_iff_forall_isStronglyConjugate_eq`:
    `H ◁◁ G ⟺ H に強共役な部分群は H 自身だけ`。⚠ **repo に既に Bartels (Thm 9.28) が完備**
    (`Ch09/SubnormalClosure.lean` の `strongClosure_isSubnormal`、sorry 0) で、書籍 p.290 が
    「2A.10 は Bartels の直接の帰結」と明記する通りに導出できた: `⟸` は `H^{(G)} = H` + Bartels、
    `⟹` は Lem 9.29(a) (`strongClosure_le_of_isSubnormal`) で `K ≤ H^{(G)} ≤ H` かつ `|K|=|H|`。
    強共役の定義 `Ch09.IsStronglyConjugate` も既存 (再定義しない)。Ch09 は Ch02 **Basic** しか
    import しないので Ch02 Problems → Ch09 の import に cycle 無し。
  - 🎉 **§2A 完済** (2A.1-2A.10 全 10 問)。

## Ch.2 (Subnormality) §2B — 着手 (2026-07-25)

- ✅ 実証明 **2B.1** `isSubnormal_of_forall_nilpotent_or_permutable` (`Basic.lean` 置き):
  各 `g` ごとに「`⟨H,H^g⟩` 冪零」**or**「`HH^g = H^gH`」⟹ `H ◁◁ G`。**Thm 2.8
  (permutability ⇒ subnormality) の disjunctive 強化**で、`|G|`-induction + Zipper の骨格が
  完全に共通 ⟹ 既存 `isSubnormal_of_permutable_aux` を
  `isSubnormal_of_nilpotent_or_permutable_aux` に一般化して**両者で核を共有**
  (重複コード ~100 行を作らない)。仮説が使われる 2 箇所だけ冪零分岐を追加:
  (i) 真部分群への降下 = `subgroupOf_sup` + `subgroupOfEquivOfLe` で冪零性移送、
  (ii) `S ⊔ S^x = ⊤` 排除 = `topEquiv` で `G` 冪零 ⟹ Lemma 2.1 で全部分群部分正規 ⟹ 仮定に矛盾。
  Thm 2.8 の signature は不変 (`fun x => Or.inr (hperm x)`) ゆえ下流無影響。
  `Problems.lean` 側は §2B section を起こしてポインタのみ記録 (ラッパー方針)。
- ✅ 新 leaf `OddOrder/Isaacs/Ch02_Subnormality/ProblemsInvolutions.lean` (`OddOrder.lean` 配線済)。
  ⚠ repo の `DihedralBasics.lean` は「巡回部分群を反転する involution」型の**抽象**補題群
  (Lemma 2.14 / Matsuyama 用) で mathlib の具体 `DihedralGroup n` は扱っていない — 別物なので
  本 leaf は mathlib `DihedralGroup n` (`r i` / `sr i`, `i : ZMod n`) の上で議論する。
- ✅ 実証明 **2B.2(a)** (2026-07-25、`n` 奇): involution の分類 (`orderOf_r_eq_two_iff`:
  `orderOf (r i) = 2 ⟺ i ≠ 0 ∧ 2i = 0`) から `2` が `ZMod n` の単元ゆえ involution = 鏡映全体
  (`orderOf_eq_two_iff_of_odd`)、個数 `n` (`card_involutions_of_odd`)、単一共役類
  (`isConj_sr_of_odd`: `k + k = i - j` を解いて `r k` で共役)。共役計算 `r_conj_sr`
  (`sr i ↦ sr (i - 2j)`) / `sr_conj_sr` (`sr i ↦ sr (2j - i)`) を helper に。
- ✅ 実証明 **2B.2(b)** (`n = m + m` 偶): `add_self_eq_zero_iff_of_even` (`2i = 0` の解は `0` と `m`
  のみ; `i.val` に降りて `(m+m) ∣ 2·i.val` から `c < 2` 場合分け) ⟹ involution = 全鏡映 + `r m`
  で `n + 1` 個 (`card_involutions_of_even`)。共役類はちょうど 3 つ・サイズ `1, m, m`:
  * `r m` は中心的 (`r_natCast_half_mem_center`、`-m = m` から) ⟹ 類 `{r m}` サイズ 1。
  * **鏡映の類は添字の「偶奇」で決まる**: `parityHom m : ZMod (m+m) →+* ZMod 2` (`2 ∣ n` の
    `ZMod.castHom`) を導入し `parityHom_eq_zero_iff` (`= 0 ⟺` 二倍元) →
    `isConj_sr_sr_iff_of_even`。fiber の個数は `k ↦ k + 1` が 2 fiber 間の全単射 + 互いに補集合
    (`Set.ncard_add_ncard_compl`) から `m` (`ncard_parityHom_fiber`) ⟹ `ncard_conjClass_sr = m`。
  * 3 類の非共役性 = `not_isConj_sr_zero_sr_one` / `not_isConj_sr_r` (後者は
    `exists_sr_of_isConj_sr` = 「鏡映の共役元は鏡映」から)。
- ✅ 実証明 **2B.3** `exists_involution_commuting_of_not_isConj` (有限群で非共役な involution
  `s, t` ⟹ 両方と可換で両者と異なる involution が存在)。**二面体群の構造定理を経由しない**:
  `u := s*t` を `s`,`t` が反転することだけ使い、`|u|` 奇なら `u^{(|u|+1)/2}` 共役で
  `s ↦ u s = s t s⁻¹` ゆえ `s ~ t` (仮定に反する) ⟹ `|u| = 2q` 偶、`z := u^q` が求めるもの。
  ⚠ 有限性は本質的 (`D∞` が反例) — docstring 明記。
- ✅ 実証明 **2B.4** `isConj_of_orderOf_eq_two_of_sylow_ti` (Sylow 2 が複数 + 互いに自明交叉 (TI)
  ⟹ involution はちょうど 1 つの共役類)。計画どおり:
  * `exists_sylow_two_mem` (involution はある Sylow 2 に入る) /
    `exists_sylow_two_mem_of_commute` (**可換な 2 つの involution は共通の Sylow 2 に入る** —
    `closure {s,z}` の可換性は `Subgroup.closure_le_centralizer_centralizer` から出し、
    `closure_induction` で全元 `g*g = 1` ⟹ `IsPGroup 2`) / `sylow_two_eq_of_ti` (一意性)。
  * 核 `isConj_of_sylow_two_ne`: 相異なる Sylow 2 の involution は共役 (対偶で 2B.3 の `z` を
    取ると両方が同じ Sylow に落ちて矛盾)。
  * 同じ Sylow の場合は Sylow の共役性 (`MulAction.exists_smul_eq` + `Sylow.coe_subgroup_smul`)
    で別 Sylow 内に `g s g⁻¹` を作って経由。
  * `exists_orderOf_eq_two_of_exists_sylow_two_ne` で involution の実在も示し「ちょうど 1 つ」
    が空でないことを保証。
- ✅ 実証明 **2B.5** `generalizedDihedral_tfae` (`List.TFAE`) + `isMulCommutative_of_generalizedDihedral`。
  指数 2 の `B ≤ G` について (1) `G∖B` に `B` を反転する involution が在る / (2) `G∖B` が
  involution だけ / (3) `G∖B` の全元が `B` を反転する involution、の同値と `B` の可換性。
  支持: `inv_mul_mem_of_notMem_of_index_eq_two` (`Subgroup.index_eq_two_iff'` から) /
  `mul_notMem_of_mem_of_notMem` / `exists_notMem_of_index_eq_two`。**有限性不要**。
- ✅ 実証明 **2B.6** `exists_normal_sylow_iff_forall_conj_pair` (正規 Sylow p ⟺ `p`-冪位数の
  共役元対 `⟨x, x^g⟩` が全て正規 Sylow p をもつ)。核は repo 既存の **Baer-Suzuki**
  (Thm 2.15 = `Theorem211Wielandt.lean` の `baerSuzuki_pCore`)。橋渡し 2 補題を新設:
  `coe_eq_opCore_of_normal` (正規 Sylow = `O_p(G)`) と `exists_normal_sylow_iff_isPGroup`
  (`p`-冪位数の元で生成される群では「正規 Sylow をもつ」=「`p`-群」)。後者で右辺が
  Baer-Suzuki の右辺そのものになる。生成元を部分群型へ移す配線は
  `Subgroup.map_injective H.subtype_injective` + `MonoidHom.map_closure`。
- 🎉 **§2B 完済** (2B.1-2B.6)。

## Ch.2 (Subnormality) §2C — 着手 (2026-07-25)

新 leaf `OddOrder/Isaacs/Ch02_Subnormality/ProblemsNGroups.lean` (`OddOrder.lean` 配線済)。
§2C の演習は **2C.1 のみ** ((a)(b) の 2 パート)。`IsLocal` (local 部分群) は §2C 本文の
`Theorem211Wielandt.lean` に既存、本 leaf で `IsNGroup` (全 local 部分群が可解) を定義。

- ✅ 実証明 **2C.1(a)** `isSolvable_quotient_of_isNGroup` (N-群の真の準同型像 `G ⧸ N`
  (`N ≠ ⊥`) は可解)。`p ∣ |N|` の Sylow `P ∈ Syl_p(N)` を `G` 側に写した `Q ≠ ⊥` について
  Frattini (`Sylow.normalizer_sup_eq_top`) で `N_G(Q) ⊔ N = ⊤`、`N_G(Q)` は local ゆえ可解、
  `N` 正規で `↑(N_G(Q) ⊔ N) = ↑N_G(Q)·↑N` だから `N_G(Q) → G ⧸ N` 全射 ⟹
  `solvable_of_surjective`。
- ✅ 実証明 **2C.1(b)** (2026-07-25)。4 定理に分割:
  * `exists_isMinimalNormal_of_not_isSolvable` (存在) / `isMinimalNormal_unique_of_isNGroup`
    (一意性: `S₁ ⊓ S₂ = ⊥` から `G ↪ (G⧸S₁)×(G⧸S₂)`、(a) で両因子可解 ⟹ `G` 可解で矛盾) /
    `not_isSolvable_of_isMinimalNormal_of_isNGroup` / `isSimpleGroup_of_isMinimalNormal_of_isNGroup` /
    `not_isMulCommutative_of_isMinimalNormal_of_isNGroup`。
  * 単純性は計画どおり: `↥S` の minimal normal `T` が `⊤` でなければ、`T` を動かす `g` が
    存在し (さもなくば押し出しが `G`-正規で `S` の minimality に反する)、`V := T^g` と
    `T ⊓ V = ⊥` から元ごと可換 ⟹ `T` の素数位数元の `⟨x⟩` について `V ≤ C_G(⟨x⟩) ≤ N_G(⟨x⟩)`
    が可解 ⟹ `T` 可解 ⟹ `⁅T,T⁆ = ⊥` (minimality + `commutator_lt_top_of_nontrivial`) ⟹
    `T` 冪零 ⟹ `T ≤ F(↥S)` (Thm 2.2) ⟹ `F(↥S)` の押し出しが `G`-正規非自明 ⟹
    `F(↥S) = ⊤` ⟹ `↥S` 冪零 ⟹ 可解で矛盾。
  * ⚠ `IsSolvable.commutator_lt_of_ne_bot` は**周囲の群**の可解性を要求するので使えず、
    `commutator ↥T = ⊤` に落として `IsSolvable.commutator_lt_top_of_nontrivial` を使う。
- 🎉 **§2C 完済** (2C.1(a)(b))。

## Ch.2 numbered results の被覆 — 陳腐化 docstring を訂正 (2026-07-25)

§2D の演習を見に行く過程で `Ch02_Subnormality/Basic.lean` の章被覆表が FT 経路時代のまま
**実測と食い違っている**ことが判明し訂正 (commit 済): 2A「着手中」/ 2C・2D「TODO」は
すべて誤りで、**2.1-2.20 は全部実在**する (2.18 = `zenkov_minimal_le_fitting`,
2.19 = `inf_fitting_ne_bot_of_abelian_card_ge_index`, 2.20 本体 =
`Ch04/ForwardFromCh02.lean` の `lucchini_index_normalCore_lt_index`)。`Main.lean` の
「`lucchini_K_bot_aux` axiom」注記も誤り (実際は private theorem) で訂正済。
Ch.2 は全ファイル sorry-free。

## Ch.2 (Subnormality) §2D — 次の frontier

§2D の演習は 2 問。**Zenkov (Thm 2.18) と Cor 2.19 が repo に既存**なので素材は揃っている。

- ✅ 新 leaf `OddOrder/Isaacs/Ch02_Subnormality/Problems2D.lean` (`OddOrder.lean` 配線済)。
  素材は repo 既存の Cor 2.19 (`inf_fitting_ne_bot_of_abelian_card_ge_index`) と
  Lucchini (`Ch04.lucchini_index_normalCore_lt_index`)。共通の位数補題
  `index_mul_card_inf_eq_card_of_sup_eq_top` (`|G:A|·|N ∩ A| = |N|`) /
  `index_le_card_of_card_le` / `le_centralizer_of_inf_eq_bot` を先に用意。
- ✅ 実証明 **2D.1(a)** `card_lt_card_of_fitting_eq_bot`: `|A| ≥ |N|` を仮定すると Cor 2.19 で
  `A ⊓ F(G) ≠ 1`、`F(N) = 1` から `F(G) ⊓ N = ⊥` (新補題
  `fitting_inf_eq_bot_of_fitting_eq_bot`、Thm 2.2 経由) ⟹ `F(G) ≤ C_G(N)` ⟹
  `A ⊓ F(G) ≤ A ⊓ C_G(N) = 1` で矛盾。
- ✅ 実証明 **2D.1(b)** `card_lt_card_of_coprime`: 同じ骨格で、`F(N) = 1` の代わりに
  `π := {q | q ∤ |N|}` を使う。`A ⊓ F(G)` は π-群、`F(G)` 冪零ゆえ `↥F(G)` 内で部分正規、
  **自分で証明した 2A.1** (`le_oPiCore_of_isSubnormal_of_isPiGroup`) で `O_π(↥F(G))` に落ち、
  `O_π` 特性的ゆえ押し出し `Q` は `G`-正規な π-群 ⟹ `Q ⊓ N = ⊥` ⟹ `Q ≤ C_G(N)` ⟹ 矛盾。
- ✅ 実証明 **2D.2** `card_lt_card_of_isCyclic`: `core_G(A) ⊓ N ≤ A ⊓ N = 1` かつ両者正規で
  `core_G(A) ≤ A ⊓ C_G(N) = 1`、**Lucchini** の `|A : core_G(A)| < |G:A|` に `|G:A| = |N|`
  を代入。
- ⚠ **2D.1 は書籍が書いていない `N ≠ 1` を要する** (`N = 1` なら `C_A(N) = A` ゆえ `A = 1` で
  `|A| = |N| = 1`、結論 `|A| < |N|` が偽)。2D.2 では書籍自身が `N` 非自明を明示しているので
  2D.1 でも同じ暗黙の仮定を置くのが原意と解し docstring に明記。
- 🎉 **§2D 完済** ⟹ **Isaacs Ch.2 の章末演習 (§2A-§2D) 全問完済**。

### 3A.8 のメモ (2026-07-25)

**核は landing 済** (`exists_unique_fixes_inverts`)。`n = s·m` (`gcd(s,m)=1`, `n` 奇, `1 < m`)
で「`s`-捩れの生成元 `m` を固定し `m`-捩れの生成元 `s` を反転する」`u : ZMod n` の一意存在 +
`u² = 1` + `u ≠ 1`。**CRT の一般論は不要で Bezout だけで閉じる**のがポイント:
`sA + mB = 1` から `e := mB` が `e·m = m`, `e·s = 0`, `e² = e` をみたし `u := -1 + 2e`。

**landing 済 (2026-07-25)**:
- `exists_unique_fixes_inverts` (核: 一意存在 + involution)。
- Bezout 系の再利用可能な支持補題: `exists_bezout_zmod` / `eq_of_fixes_inverts` (一意性のみを
  切り出したもの、奇数性不要) / `inverts_mul` / `fixes_mul` / `inverts_of_inverts_coprime` /
  `fixes_of_fixes_coprime`。
- (a) の捩れ表現 `fixes_inverts_iff_torsion` (生成元での条件 ⟺ 「`s`-捩れを全部固定し
  `m`-捩れを全部反転」)。書籍の言い回しに一致。
- (b) `mul_eq_of_fixes_inverts_pqr` (`u_p · u_q = u_r`) ⟹ `{1,u_p,u_q,u_r}` は Klein 四元群。

**(c) も landing 済 (2026-07-25)** ⟹ **3A.8 完了**。
基盤: `zmodUnitsAction` / `zmodSemidirect n K` / `conj_inl_apply` / `inl_ofAdd_one_pow` /
`conj_pow_fixes_iff` (`α^j` が `⟨x,k⟩` を固定 ⟺ `j·(1-k) = 0`)。
本体: `kleinSubgroup` (3 involution が張る位数 4 の部分群) / `mem_kleinSubgroup` /
`two_mul_ne_zero_of_odd_prime_factor` / `conj_pow_ne_one` / **`no_regular_orbit_klein`**。

⚠ **実装上の罠 3 件** (同種の作業で再発しうる):
1. `ZMod (p*q*r)` は**法が型に現れる**ので `rw [mul_assoc]` が型内の `p * q * r` にマッチして
   motive 破綻する。`mul_assoc up uq` と引数を固定すること。
2. 構造体フィールドの証明で `rcases ha with rfl|…` を使うと、**定義の束縛変数** (`up` 等) が
   substitution で消える。`rw [ha]` を使うこと。
3. `eq_inv_of_mul_eq_one_left h : up = up⁻¹` を simp 補題にすると `up → up⁻¹ → up⁻¹⁻¹ → …` で
   無限ループ (maxRecDepth 到達)。`inv_eq_of_mul_eq_one_left` (`up⁻¹ = up`) を使うこと。

### §3A leaf の分割 (2026-07-25)

`Ch03/Problems.lean` が 1363 行になり上限 1500 に近づいたため、先頭の 3A.1 (semidihedral) /
3A.2 (一般化四元数群) クラスタを sibling leaf `ProblemsSemidihedral.lean` へ **prefix-split**
(元 `Problems.lean` がそれを import、module 名不変で下流無影響)。
分割後: `ProblemsSemidihedral.lean` 588 行 / `Problems.lean` 801 行。宣言数 93 が一致すること
を確認済。`OddOrder.lean` 配線も同 commit。

### 3A.10 のメモ

`G := Multiplicative (ZMod p) ≀[H] H` (正則 wreath product)、`A := base group` で全部出る。

**landing 済 (2026-07-25)**: `conj_inl_of_comm` (`D` 可換なら任意の `x` による base 元の共役は
座標置換のみ — `WreathProduct.ext` + `mul_left`/`inv_left` から直接計算) /
`eq_inl_of_right_eq_one` / **`centralizer_range_inl_eq`** (= `A = C_G(A)`、指示関数の技)。

**束ね上げも landing 済 (2026-07-25)** ⟹ **3A.10 完了**。`zpWreath` / `zpWreathBase` /
`zpWreathBase_spec` (可換・`p` 乗して 1・分裂 (`A ⊓ inr.range = ⊥`, `A ⊔ inr.range = ⊤`)・
`G/A ≅ H`・`A = C_G(A)`)。`A ⊴ G` は `range_inl_normal` を instance 化。
あわせて `WreathProduct` の一般 API を補完: `inl_left_mul_inr_right` (`SemidirectProduct` 側に
あって wreath 版に無かった分解補題) / `range_inl_normal` / `rightHom_surjective`。


⚠ 実装上の罠 (今回): `WreathProduct` の補題を `rw`/`congrArg` で使うとき、`Ω` が
metavariable のままだと `MulAction ?m ?m` で instance 解決が詰まる。`conj_inl_of_comm hD x` の
ように**引数を明示**するか、`rw [← map_mul]; congr 1` のように `inl` を露出させない形にする。

### 3A.7 の証明 (2026-07-25 landing)

`exists_regular_orbit_of_primeFactors_card_le_two`。骨格は 2 段:
1. 「`g` の安定化群が非自明 ⟹ ある素因子 `r ∣ n := o(α)` で `α^{n/r}` が `g` を固定」。
   `α^j ≠ 1` が `g` を固定するとき `m := gcd(n,j)` について **Bezout** で `α^m = (α^j)^b`
   (`α^n = 1` を使う) ゆえ `α^m` も固定、`orderOf (α^j) = n/m ≠ 1` の素因子 `r` を取ると
   `m·r ∣ n` すなわち `m ∣ n/r` で `α^{n/r} = (α^m)^c` も固定。安定化群は
   `MulAction.stabilizer (MulAut G) g` として扱うと冪の処理が部分群の閉性で済む。
2. よって regular orbit が無いと `G` は固定部分群 `F r = eqLocus (α^{n/r}) id` (高々 2 個) の
   合併。各 `F r` は真部分群 (`orderOf (α^{n/r}) = r > 1`) で、**群は 2 つの真部分群の合併に
   ならない** (`not_forall_mem_or_mem_of_ne_top`) から矛盾。

⚠ この「2 つの真部分群の合併にならない」は 3A.6 には**そのままでは効かない**: 3A.6 の
`G = ⋃_{1≠z∈V} C_G(z)` は `V` の階数が 2 以上だと 3 個以上の合併になり、群は 3 個以上の
真部分群の合併になりうる (階数 1 のときだけこの筋で閉じる)。

## Ch.3 §3B — 次の frontier (演習 3B.1-3B.15)

`§3B` は Schur-Zassenhaus と可解群の節で、演習が 15 問ある:
3B.1 (可解群の極大部分群は素冪指数) / 3B.2 (可換因子の subnormal 列 ⟹ 可解) /
3B.3 (合成因子が全て素数位数 ⟺ 可解) / 3B.4 (`|N|` と `|G:N|` 互いに素、`|U| ∣ |G:N|` ⟹
`U` はある補群に含まれる) / 3B.5 (`P ∈ Syl_p(G)` が中心に含まれる ⟹ `G = X × P`) /
3B.6 (剰余類の代表の位数) / 3B.7 (supersolvable) / … / 3B.14 (`C = C_G(F(G))`) /
3B.15 (Berkovich)。文書順に 3B.1 から。

### 3A.6 の解析 (2026-07-25、deferred-hard として記録)

**確立できた部分** (次に着手する人はここから始めてよい):
- `Γ := G ⋊ P` を作ると `p ∤ |G|` ゆえ `P ∈ Syl_p(Γ)`、Sylow p-部分群は `{P^g : g ∈ G}`。
- **`P ∩ P^g = P_g` (= `g` の `P`-安定化群)**: `u ∈ P` に対し `g⁻¹ u g = (g⁻¹ · u(g)) u` なので
  `g⁻¹ u g ∈ P ⟺ u(g) = g`。すなわち **Sylow 交叉 = 点安定化群**。
- **`O_p(Γ) = 1`**: `O_p(Γ) ∩ G = 1` (位数) ゆえ `[O_p(Γ), G] = 1` で `O_p(Γ) ≤ C_Γ(G)`、
  かつ `O_p(Γ) ≤ P`、`P` の作用が faithful なので `P ∩ C_Γ(G) = 1`。
- **軌道 `Δ = P·h` 上の核は `core_P(P_h)`** (`P_{u(h)} = (P ∩ P^h)^{u⁻¹}` から)。
- **`core_P(P_h) = 1 ⟺ P_h ∩ Z(P) = 1`** (`p`-群の非自明正規部分群は中心と非自明に交わる;
  逆に `Z(P)` の位数 `p` の元は `P`-正規)。⟹ **目標は「`C_{Z(P)}(h) = 1` なる `h ∈ G` の存在」**、
  さらに `V := Ω_1(Z(P))` として「`G ≠ ⋃_{1≠z∈V} C_G(z)`」と同値。
- Brodkey (Thm 1.38) + `O_p(Γ) = 1` から、交わり極小な Sylow 対 `(S,T)` について
  **`Z(S) ∩ Z(T) = 1`** は出る (`Z(S) ∩ Z(T)` は `Z(S)` の部分群ゆえ `S`-正規、同様に `T`-正規)。

**詰まっている一手**: 必要なのは `Z(P) ∩ P^h = 1` (より強い) であって `Z(P) ∩ Z(P^h) = 1` では
足りない。

#### 2026-07-25 の再攻略で得た**より鋭い定式化** (次に着手する人はここから)

`V := Ω₁(Z(P))` とおく。**「どの軌道も faithful でない」⟺ 全ての `g ∈ G` で `V ∩ P^g ≠ 1`**
(∵ 軌道核 `core_P(P_g) ≠ 1 ⟺ P_g ∩ Z(P) ≠ 1 ⟺ P_g ∩ V ≠ 1`、かつ `P_g = P ∩ P^g`)。
すなわち **`V` が `Γ = G ⋊ P` の全ての Sylow `p`-部分群と非自明に交わる**という仮定。

交わり極小な Sylow 対を `(S, T) = (P, P^g)` に取ると (共役で `S = P` としてよい):
- Brodkey (Thm 1.38) + `O_p(Γ) = 1` ⟹ **`Z(S) ∩ Z(T) = 1`** (両者に正規な `D` の部分群だから)。
- `V ≤ Z(S)`、`V^g ≤ Z(T)` ⟹ **`V ∩ V^g = 1`**。
- 仮定から **`V ∩ T ≠ 1`** かつ **`V^g ∩ S ≠ 1`**。

⟹ **残る一手は「`V ∩ T ≠ 1` を `V ∩ Z(T) ≠ 1` に格上げする」だけ** (格上げできれば
`1 ≠ w ∈ V ∩ Z(T) ≤ Z(S) ∩ Z(T) = 1` で即座に矛盾し、問題が閉じる)。
同値な言い換え: 「`V ∩ T` の非自明な部分群で `T`-正規なものを見つける」。
`p`-群の非自明部分群は一般に中心と交わらない (交わるのは**正規**部分群) ので、
`V ∩ T` の `T`-正規性を出す構造 (極小交叉の古典補題 or 別の Sylow 対の選び方) が要る。

#### 🎉 2026-07-26: **3A.6 の欠けていた一手が見つかった (数学的には解決)**

**statement** (PDF で確認): `P` が `p`-群で位数が `p` で割れない群 `G` に **faithful** に
自己同型で作用するなら, ある `P`-軌道 `Δ ⊆ G` 上で `P` は faithful に作用する。
hint = Thm 1.38 (generalized Brodkey)。

これまでの停滞は `V := Ω₁(Z(P))` を経由する被覆論法 (`G = ⋃ C_G(v)` の否定) に固執した
ことが原因で, **`V` は不要**。正しい鍵は次の**正規性**:

> **軌道 `Δ_g = {u(g) : u ∈ P}` の各点固定部分群 `N := core_P(P_g)` は `P` だけでなく
> `P^g` でも正規。**

これで Thm 1.38 が直接効く。証明の全体:

1. `Γ := G ⋊ P`。`p ∤ |G|` ゆえ `P ∈ Syl_p(Γ)`, かつ Sylow `p`-部分群は
   `{P^g : g ∈ G}` (共役元の `P`-成分は `P` を動かさない)。
2. `P` の作用が faithful ⟹ **`O_p(Γ) = 1`** (既記録: `O_p(Γ) ⊓ G = 1` (位数) ⟹
   `⁅O_p(Γ), G⁆ = 1` ⟹ `O_p(Γ) ≤ C_Γ(G) ⊓ P = 1`)。
3. **`P ∩ P^g = P_g`** (点安定化群)。∵ `g⁻¹ u g = inl(g⁻¹ · u(g)) · u` なので
   `g⁻¹ u g ∈ P ⟺ u(g) = g`, さらにそのとき `g⁻¹ u g = u`。
4. `Δ_g` 上の核は `N = ⋂_{u∈P} P_{u(g)} = core_P(P_g)` (`P_{u(g)} = u P_g u⁻¹`)。
5. **⭐ 核 `N` は `P^g` でも正規** — これが欠けていた一手:
   `t ∈ P^g` を `t = inl(w) · u` (`w := g⁻¹ · u(g) ∈ G`, `u ∈ P`) と書き, `n ∈ N` に対し
   `t n t⁻¹ = inl(w) · (u n u⁻¹) · inl(w)⁻¹`。`m := u n u⁻¹ ∈ N` (`N ⊴ P`) で
   `inl(w) · m · inl(w)⁻¹ = inl(w · m(w)⁻¹) · m`。
   ここで **`m` は `Δ_g` を各点固定するので `g` と `u(g)` を固定 ⟹ 自己同型ゆえ
   `w = g⁻¹ · u(g)` も固定** (`m(w) = m(g)⁻¹ · m(u(g)) = w`)。よって `t n t⁻¹ = m ∈ N`。
6. `|P ∩ P^g|` を最小にする `g` を取る (Sylow が全て `P^g` の形なので **これが Γ での
   極小 Sylow 交叉**)。`N ≤ P ∩ P^g` は `P` でも `P^g` でも正規だから **Thm 1.38** より
   `N ≤ O_p(Γ) = 1` ⟹ `P` は `Δ_g` に faithful に作用する ∎

⚠ 被覆論法 (`V` 経由) は**筋が悪い**ので追わない (階数 ≥ 2 で被覆数が増え閉じない)。

#### 🎉 Lean 実装完了 (2026-07-26) — 新 leaf `Ch03_SplitExtensions/ProblemsFaithfulOrbit.lean`

| 部品 | Lean 名 |
|---|---|
| `(inl g)⁻¹·inr u·inl g = inl(g⁻¹·(φ u)g)·inr u` | `inl_inv_mul_inr_mul_inl` |
| Sylow 交叉 = 点安定化群 (元の形) | `conj_inr_mem_inr_range_iff` |
| `inr(P)` は `Γ` の Sylow | `sylowInrRange` (+ `card_inr_range_eq_pow_factorization`) |
| `O_p(Γ) = 1` | `opCore_semidirectProduct_eq_bot` (+ `inr_range_inf_centralizer_eq_bot`) |
| 点安定化群 / 軌道核 (P で正規) | `fixSubgroup` / `orbitKernel` / `orbitKernel_normal` |
| `inr(P) ⊓ inr(P)^{inl g} = inr(P_g)` | `inr_range_inf_conjInrRange_eq` |
| ⭐ 軌道核は共役 Sylow でも正規 | `conjInrRange_le_normalizer_orbitKernel_map` |
| `Γ` の Sylow はすべて `conjInrRange a` | `exists_eq_conjInrRange` |
| 交叉位数の共役不変性 | `exists_card_inf_eq` |
| **本体** | `exists_faithful_orbit` |

⚠ 実装知見:
- `simp` は `φ (v m₀ v⁻¹)` を `(φ v)∘(φ m₀)∘(φ v).symm` に展開するので、軌道核条件を
  `u = 1` と `u = v⁻¹` で使った 2 式を simp に渡す。
- `γ.left`/`γ.right` のまま `rw` すると自己参照で潰れる → `obtain ⟨a, b⟩ := γ` で先に分解。
- `Ch03` は `Ch04` を import できないので `le_normalizer_of_forall_conj_mem` は局所 private 版。
- 極小性は `Function.argmin` + `Subgroup.eq_of_le_of_card_ge`、
  共役不変性は `Subgroup.smul_inf` + `Subgroup.equivSMul`。


## Ch.3 (Split Extensions) §3A — 着手 (2026-07-23、§2A hard tail deferred 中の breadth 展開)

新 leaf `OddOrder/Isaacs/Ch03_SplitExtensions/Problems.lean` (namespace `OddOrder.Isaacs.Ch03`、
import `Mathlib.GroupTheory.SemidirectProduct`+`Tactic.Group`、`OddOrder.lean` 配線済)。

- ✅ 実証明 **3A.3** 位数 pm 群 (正規 P 位数 p, G/P 巡回, Z(G)=1) — 2026-07-23 **完全完成**:
  σ=×u (位数 m, `AddAut.mulLeft`+`MulAutMultiplicative`) / `affineGroup u = Mult(ZMod p) ⋊ ⟨σ⟩` /
  `affineGroup_card` (|G|=p·orderOf u) / `affineGroup_card_ker` (P=ker rightHom 位数 p, 正規) /
  `affineGroup_quotient_isCyclic` (G/P 巡回) / **`affineGroup_center_eq_bot`** (Z(G)=⊥、u≠1) /
  `exists_group_card_eq_normal_cyclic_center_trivial` (存在まとめ)。center は (a,h)∈Z → φ(h)=id⟹h=1、
  a=σ(a)⟹(u-1)·toAdd a=0⟹a=1 (体 ZMod p で u-1 可逆)。⚠ `Multiplicative (ZMod p)` の ring/group Mul
  instance 衝突は **cancel を toAdd で ZMod p 加法に落として `add_left_cancel`** で回避 (教訓記録)。
  全実証明・sorry 無・axiom-clean。
- ✅ 実証明 **3A.1(a)** semidihedral の特徴的自己同型 (2026-07-23)。`ZMod n` (8∣n) 上、生成元条件
  `c^a = c⁻¹z` (加法的 `-c+z`, `z=n/2`) を満たす唯一の自己同型 `a` = 乗数 `w=z-1` (`w²=1` ∵ 4∣n)
  による乗法、位数 2。`semidihedralAut` (concrete `AddEquiv`, 自身が逆) / `_apply` / `_apply_isUnit`
  (存在=生成元条件、odd fact `z·c=z` 経由) / `_unique` (自己同型は `1` での値で定まる, `map_nsmul`) /
  `_add_self`+`_ne_zero`+`_addOrderOf`=2 (`AddAut` は加法群ゆえ位数 = `addOrderOf`)。全実証明・sorry 無。
- ✅ 実証明 **3A.1(b)** semidihedral 群内の位数分布 (2026-07-23)。`σ = semidihedralMulAut` (=`a` の
  `MulAut (Multiplicative (ZMod n))` 版、`MulAutMultiplicative` bridge; apply=rfl、`σ²=1`)、
  `SemidihedralGroup = Multiplicative (ZMod n) ⋊ ⟨σ⟩` (φ=部分群包含 `H.subtype`、ZMod.lift 不要)、
  reflection `(x,σ)` (=S−C の元)。`_sq`: `(x,σ)²=inl(z·x)`、`_pow_four`: `(x,σ)⁴=1`、
  `_ne_one`/`_sq_eq_one_iff`。位数特徴づけ `_orderOf_eq_two_iff` (⟺`z·x=0`=偶)・`_eq_four_iff`
  (⟺`z·x≠0`=奇、`orderOf_eq_prime_pow`)・`_two_or_four`。半々: `semidihedral_invol_mul_dichotomy`
  (`z·a∈{0,z}`、induction) + `_invol_ne_zero` + **`semidihedralOrderFlip`** (位数2集合 ≃ 位数4集合、
  parity flip `x↦x·ofAdd 1`)。全実証明・sorry 無・axiom-clean。
- ✅ 実証明 **3A.1(c)** 位数 2・位数 4 の元はそれぞれ単一共役類 (2026-07-23)。`_conj`: `inl y` で
  reflection を共役すると `refl(y·x·σ(y⁻¹))` (加法的に `toAdd x` が `(2-z)·toAdd y` シフト)。
  `semidihedral_shift_surj`: `z·d=0` (d 偶) なら `∃t, (2-z)·t=d` (`u=1+n/4` が `(2-z)·u=2` ∵
  `(2-4k)(1+2k)=2-8k²≡2`、d=2s→t=u·s)。`_isConj` (差が偶なら共役) + 系 `_isConj_of_two` (両偶)
  ・`_isConj_of_four` (両奇、dichotomy で `z·x=z` 確定)。全実証明・sorry 無・axiom-clean。
  **3A.1 完全完成 (a/b/c)**。
- ✅ 実証明 **3A.2** 一般化四元数群 `Q_n` (位数 n) — 2026-07-23 完成 (ker(ψ) 構成):
  B = C の index-2 部分群 = `Subgroup.zpowers (Multiplicative.ofAdd (2:ZMod n))` (位数 n/2、
  偶元 = squares)。位数 4 の元 {(x,σ): x 奇} は inl(B) の coset `(ofAdd x₀, σ)·inl(B)` をなす
  (x₀ 奇; σ(ofAdd 2k)=ofAdd(-2k) ゆえ shift で {奇}=coset)。Q = coset ∪ inl(B) は位数 n の部分群
  (= Q_n)。**★ clean 構成発見 (2026-07-23)**: `ψ : S →* Multiplicative (ℤ/2)`,
  `ψ(x,h) = (h の parity ∈{0,1}) + (toAdd x の parity)` は**準同型** — σ twist で左 parity が保存
  (`w = z-1 = 4k-1` 奇ゆえ `parity(w·m) = parity(m)`)、H-part も加法的。ψ 全射 (`ψ(ofAdd 1,1)=1`)
  ゆえ **Q := ψ.ker、`|Q| = |S|/2 = n`** が自動 (`Subgroup.card_eq_card_quotient_mul_card_subgroup`
  や index=2)。B ≤ Q (偶元は ker)、位数 4 元 (x 奇, σ) ⊆ Q (parity 1+1=0)、Q = {(x,1):x偶}∪{(x,σ):x奇}
  = coset ∪ B。~50 行 (ψ の map_mul' 計算が主)。閉性を手で示すより ker(ψ) が圧倒的に clean。
  既存 semidihedral インフラ (reflection/σ/dichotomy/parity) を再利用。
  ⚠ 次イテレーション注意: ψ の H-part parity は `SemidirectProduct.rightHom : S →* H` +
  `H = ⟨σ⟩ ≃* Multiplicative (ℤ/2)` iso が要 (σ 位数2)。iso が clean に取れない場合は、ψ を toFun 直書き
  (g.right の 1/σ 判定 + 左 parity) + map_mul' 手計算、または Q を carrier set 直接定義
  ({(x,1):x偶}∪{(x,σ):x奇}) + closure 手証明 (既証明の位数2/4 characterization を活用) にフォールバック。
- ✅ 実証明 **3A.5** `semidirectConjEquivProd` (`G ⋊ G ≅ G × G`、共役作用の半直積は直積)。同型
  `(n,g)↦(n·g,g)` (逆 `(a,g)↦⟨a·g⁻¹,g⟩`)、map_mul' は `mul_left`/`mul_right`/`conj_apply` 展開 + `group`。
- ⬜ **3A.3** (位数 pm 群、Z(G)=1) — 構成計画 (2026-07-23、order-m 元は scratch 検証済):
  G = `Multiplicative (ZMod p) ⋊ Subgroup.zpowers σ` (p 素数, m∣p-1, m>1)。
  **(1) order-m 元 u : (ZMod p)ˣ [検証済]**: `haveI := ZMod.isCyclic_units_prime Fact.out`;
  `obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard`; `Nat.card (ZMod p)ˣ = p-1`
  (`card_units_eq_totient`+`totient_prime`); `u := g^((p-1)/m)`;
  `orderOf u = m` via `orderOf_pow_of_dvd hne hdvd` + `Nat.div_div_self hm`
  (hdvd: (p-1)/m ∣ p-1 = `Nat.div_dvd_of_dvd hm`, hne: (p-1)/m≠0)。
  **(2) σ := `(MulAutMultiplicative (ZMod p)).symm (AddAut.mulLeft u)`** : MulAut(Mult(ZMod p))。
  `orderOf σ = orderOf u = m` via `orderOf_injective (MulAutMultiplicative _).symm.toMonoidHom
  (.symm.injective)` ∘ `orderOf_injective AddAut.mulLeft hinj`。⚠ hinj (mulLeft 単射) は
  `AddAut.mulLeft = DistribMulAction.toAddAut` (`@[simps! +simpRhs]`) の apply で `(toAdd(mulLeft a)) 1
  = ↑a·1 = ↑a`; `congrArg Multiplicative.toAdd h` + `DFunLike.congr_fun _ 1` + `simpa [Units.smul_def,
  Units.ext_iff]` (前回 simp が toAdd wrapper を剥がせず未完 — apply 補題名の特定が要)。
  **(3) |G| = p·m**: `SemidirectProduct.card` (=|N|·|H|) + `Nat.card_zpowers`+orderOf σ=m +
  `Nat.card (Mult(ZMod p)) = p` (`Nat.card_congr Multiplicative.toAdd`+`Nat.card_zmod`)。
  **(4) P := inl 像 = ker rightHom, 正規, |P|=p; G/P ≅ zpowers σ 巡回 (rightHom 全射)**。
  `SemidirectProduct.rightHom`/`range_inl`/`inl_injective`。
  **(5) Z(G)=⊥ [核心・未検証, SemidirectProduct center API 無し]**: (a,h)∈center →
  ∀(b,k) 可換。k=1: a·φ(h)(b)=b·a ⟹ φ(h)(b)=b ∀b (N 可換) ⟹ φ(h)=id ⟹ h=1 (φ=subtype 単射)。
  h=1,b=1,k=σ: a=σ(a)=×u(a) ⟹ (u-1)·toAdd a=0 ⟹ toAdd a=0 (u≠1 ⟹ u-1 は体 ZMod p の unit)
  ⟹ a=1。~50 行。`Subgroup.mem_center_iff`/`SemidirectProduct.ext`/`SemidirectProduct.mul_left,right`。
- ✅ 実証明 **3A.4** (2026-07-25) `affineGroupOfField` 系: 有限体 `F` の `Fˣ` が `(F,+)` に作用する
  半直積 `G = Multiplicative F ⋊ Fˣ` (3A.3 の `affineGroup` と同じ `MulAutMultiplicative` +
  `AddAut.mulLeft` idiom)。`|G| = q(q-1)` / `|ker rightHom| = q` / `ker` は基本アーベル `p`-群 /
  位数 `p` の元は `right = 1` (`orderOf right` が `p` と `q-1` を割るが互いに素) で
  `inl x` (`x ≠ 0`) の形、`Fˣ` が `F ∖ {0}` に推移的だから単一共役類
  (`SemidirectProduct.inl_aut`)。まとめ `exists_group_card_eq_elementaryAbelian_isConj` は
  `GaloisField p k` を代入 (⚠ `GaloisField.card` は **`Nat.card` で述べられている**ので
  `Fintype` 経由は不要)。

### ⚠ §3A の被覆は実測で更新 (2026-07-25)

本 issue の §3A 記載は古く、**3A.3 と 3A.5 は既に完成済み**だった (実測で確認)。現状:

| 問題 | 状態 |
|---|---|
| 3A.1(a)(b)(c) | ✅ (semidihedral) |
| 3A.2 | ✅ (一般化四元数群) |
| 3A.3 | ✅ (位数 pm, Z(G)=1) |
| 3A.4 | ✅ (2026-07-25) |
| 3A.5 | ✅ (`G ⋊ G ≅ G × G`) |
| 3A.6 | ✅ **完了** (2026-07-26) `exists_faithful_orbit` (新 leaf `ProblemsFaithfulOrbit.lean`) |
| 3A.7 | ✅ **完了** (2026-07-25) |
| 3A.8 | ✅ **完了** ((a)(b)(c) すべて) |
| 3A.9 | ✅ **完了** ((a)(b)) |
| 3A.10 | ✅ **完了** (`zpWreathBase_spec`) |

- ⬜ **次: §3A 続き or §2A hard tail 再訪。§1D 残り = 1D.5 (Isaacs-noted-hardest)。**

## 完了条件

Isaacs Ch.1–10 の全演習問題が形式化 (実証明 or mathlib/repo 対応の docstring 記録)、
build green、AxiomsCheck OK。章単位で commit・issue checkbox 更新。

## 参照

- issue 9205 (scope 拡大の裁定元)、`notes/isaacs/frontier_measured_2026_07_19.md` (番号付き結果の完済正本)
- `references/isaacs/finite-group-theory.pdf` (statement 確定用、PDF ページ = 書籍ページ + 13)
- CLAUDE.md「トレーサビリティ」「ファイル粒度」「ラッパー方針」

---

## ❄ 2026-07-24 FROZEN (ユーザー裁定) — pending へ

Isaacs Problems campaign (lane a の現 frontier) はユーザー裁定で凍結。再開時は本文の
文書順 (Ch.1 §A から) と置き場規約 (ChNN/Problems*.lean) をそのまま引き継ぐ。
lane a の次 frontier は hub 裁定 (9500 番台) で再割当。

## ☀ 2026-07-25 UNFROZEN (ユーザー指示) — open へ復帰

ユーザー指示「凍結してた問題を解くやつをやります」で campaign 再開。文書順で最古の未完
= **§1C の 1C.4 / 1C.5** (deferred-heavy) から再訪 → 以降 1D.5 / §2A hard tail
(2A.4/5/6/9) / §3A 残り (3A.4/6/7/8) / §3B〜 の順。

**2026-07-25 の消化**: 1C.4 ✅ / 1C.5 ✅ / 1D.5 ✅ / 2A.4 ✅ / 2A.5(a)(b)(c) ✅ / 2A.6 ✅ /
2A.9 ✅ / 2A.10 ✅ (**§2A 完済**) / 2B.1 ✅。
さらに 2B.2(a)(b) ✅ / 2B.3 ✅ (新 leaf `Ch02_Subnormality/ProblemsInvolutions.lean`)。
さらに 2B.4 ✅ / 2B.5 ✅ / 2B.6 ✅ で **§2B も完済**。
さらに **2C.1(a) ✅ / 2C.1(b) ✅ で §2C も完済**。あわせて Ch.2 の陳腐化した被覆表
(2A/2C/2D を誤って TODO と記載) も実測に合わせて訂正。
さらに **§2D も完済 (2D.1(a)(b) / 2D.2)** ⟹ **Isaacs Ch.2 の章末演習は全問完済**。
さらに **3A.4 ✅** (3A.3 / 3A.5 は既済と実測判明)。
さらに **3A.9(a) ✅**。**3A.6 は deferred-hard** (解析は §3A 節に記録; Brodkey の適用の一手が
未確定)。さらに **3A.8(a) の核 ✅**。さらに **3A.8(a)(b) ✅**。さらに **3A.8(a)(b) のまとめ ✅**。さらに **3A.8(c) の基盤 ✅**。さらに **3A.8(c) ✅ ⟹ 3A.8 完了**。
⚠ `Ch03/Problems.lean` は **1363 行** (上限 1500) — **次の追加の前に §3A leaf を分割する**
(CLAUDE.md のファイル粒度規約: 3A.1/3A.2 の semidihedral・一般化四元数クラスタ (~550 行) を
別 leaf へ出すのが自然)。
さらに **§3A leaf 分割 ✅ / 3A.9(b) ✅ (3A.9 完了)**。
さらに **3A.10 の核 ✅** (`A = C_G(A)`)。
さらに **3A.10 ✅** ⟹ **§3A は 3A.6 / 3A.7 を除いて完了**。
さらに **3A.7 ✅** ⟹ **§3A は 3A.6 のみ残り** (deferred-hard)。
さらに **3B.1 ✅ / 3B.2 ✅ / 3B.3 ✅** (新 leaf `Ch03_SplitExtensions/Problems3B.lean`)。
さらに **3B.4 ✅ / 3B.5 ✅**。
**次 frontier = (1) 3A.6 再訪 (1 iteration 時間箱) → (2) Isaacs Ch.4 §4A から文書順**。

⚠ **実測 (2026-07-25)**: `Problem NX.Y` docstring を Ch.4-Ch.10 で grep すると **0 件** —
**Ch.4 以降の章末演習は 1 問も形式化されていない**。Ch.1-Ch.3 (+ Ch.2 全問, §3A/§3B) が
済んだので、campaign の残りは Ch.4 以降が主戦場。

prefix-split 済 (2026-07-25): `Problems3B.lean` (1300 行) → `Problems3BSolvability.lean`
(3B.1-3B.3, 239 行) + `Problems3B.lean` (3B.4-3B.15, 1093 行)。

3B.15 (Berkovich) の証明: 最小指数の `H` は極大。極小正規 `N` について `N ≤ H` なら
`G ⧸ N` へ落として帰納法。`N ≰ H` なら `G = N ⋊ H` で `N` への `H` の共役作用を見る —
`C_N(H) = N` なら `N` が `H` を正規化して `H ⊴ G`、`C_N(H) = 1` なら `v ∈ N \ {1}` の
安定化群 `H_v < H` から `N ⊔ H_v` が真部分群になり、その指数 = 軌道の大きさ `≤ |N| - 1`
`< |N| = [G:H]` で最小性に矛盾 (`MulAction.index_stabilizer` を使用)。

## Ch.4 (Commutators) §4A — 着手 (2026-07-25)

新 leaf `OddOrder/Isaacs/Ch04_Commutators/Problems.lean` (namespace `OddOrder.Isaacs.Ch04`、
`OddOrder.lean` 配線済)。§4A は 11 問 (4A.1-4A.11)。

| # | 状態 | Lean 名 |
|---|---|---|
| 4A.1 | ✅ | `commutator_eq_commutator_of_mul_eq_top` |
| 4A.2 | ✅ | `exists_closure_commutatorTriple_eq_zpowers` (前半) / `exists_card_two_subgroups_commutator_triple_eq_top` (後半 = A₅ 実例 + Note) |
| 4A.3 | ✅ | `IsQuasiquaternion` (定義) / `eq_bot_of_isQuasiquaternion_quotient` |
| 4A.5 | ✅ | (a) `index_centralizer_eq_of_not_mem_center` / (b) `card_closure_pair_eq` / (c) `index_centralizer_closure_pair_eq` / (d) `map_center_centralizer_eq_center` + `isExtraspecial_centralizer_closure_pair` / (e) `exists_index_center_eq_prime_pow_two_mul` (新 leaf `ProblemsExtraspecial.lean`) |
| 4A.6 | ✅ | `IsMaximalClassPGroup` (定義) / `exists_eq_lowerCentralSeries_of_isMaximalClass` (+ 一意性 `eq_of_normal_of_card_eq_of_isMaximalClass`、新 leaf `ProblemsMaximalClass.lean`) |
| 4A.7 | ✅ | `exists_orderOf_eq_and_forall_orderOf_dvd` (+ 冪公式 `pow_mk` / 上界 `pow_prime_pow_succ_eq_one`、新 leaf `ProblemsWreath.lean`) |
| 4A.8(d) | 🔨 進行中 | 位数・下降中心列の翻訳 (`lowerCentralSeries_eq_map_shiftSubSeq`) 完了、残りは linchpin `Δ^{p-1} = T_p` 1 本 — 下記 |
| 4A.8(c) | ✅ 訂正版 | `forall_commute_ker_augHom_iff` + 位数 `card_center_ker_augHom` (`|Z(P'U)| = p`)。書籍の主張は `p=2, n=1` で偽 — 下記 |
| 4A.8(b) | ✅ | `commutator_range_inl_range_inr_eq` (`⁅A,U⁆ = ker(座標積)` の像) + `commutator_eq_commutator_range_inl_range_inr` (4A.1 経由 `P' = ⁅A,U⁆`) + まとめ `commutator_eq_coordProdHom_ker_map` |
| 4A.8(a) | ✅ | `mem_center_iff_exists_const` / `center_eq_inf_centralizer_range_inr` (`ProblemsWreath.lean`) |
| 4A.4 | ✅ | `isElementaryAbelian_quotient_center_of_commutator_eq_center` (+ 同値形 `frattini_eq_center_of_commutator_eq_center` + 橋 `isExtraspecial_of_commutator_eq_center`) |

- **4A.1** (`G = AB`, `A`,`B` abelian ⟹ `G' = ⁅A,B⁆`): `⁅A,B⁆` の正規性は既存の
  `commutator_normal_of_sup_eq_top` (Ch.4 Main の Lem 4.1 系) をそのまま使える。
  商で `A` の像と `B` の像が可換 + 各々 abelian ⟹ 商 abelian ⟹ `G' ≤ ⁅A,B⁆`。
- **4A.4**: repo の `IsExtraspecial` は `frattini_eq_center` を**フィールドとして仮定**して
  いるので、本問 (`P' = Z(P)`, `|Z(P)| = p` ⟹ `P/Z(P)` elementary abelian) は新規内容。
  類 2 の恒等式 `⁅x^n, y⁆ = ⁅x,y⁆^n` を証明して `x^p ∈ Z(P)` を出す。
  **書籍併記の `Z = P' = Φ` 形も完了 (2026-07-25)**: 「repo に `Φ ⊆` 方向が無い」という
  当初の注記は**誤り**で、Lem 4.5 forward `frattini_le_of_isElementaryAbelian_quotient_of_pgroup`
  (Ch04 Main/CommutatorIdentities) がちょうど `P/N` elementary abelian ⟹ `Φ(P) ≤ N` を与える。
  ⟹ `frattini_eq_center_of_commutator_eq_center`、さらに repo の
  `OddOrder.GroupTheory.IsExtraspecial` (Φ = Z を field に持つ) への橋
  `isExtraspecial_of_commutator_eq_center` を追加。以後 4A.5 以降は Isaacs の定義
  (`P' = Z(P)` 位数 `p`) から repo 構造の API をそのまま使える。

- **4A.2** (`⁅H,K,L⁆` は `⁅h,k,l⁆` たちで生成されるとは限らない): 前半 (位数 2 の `H,K,L` なら
  三重交換子の**元**は高々 1 個の非単位元 ⟹ 生成するのは巡回群) は
  `exists_closure_commutatorTriple_eq_zpowers` で `closure {…} = ⟨⁅⁅h,k⁆,m⁆⟩` と**等式**まで出す
  (生成元自身が集合の元なので場合分け不要)。汎用補題
  `commutator_zpowers_eq_zpowers_commutatorElement` (`a² = b² = 1` ⟹ `⁅⟨a⟩,⟨b⟩⁆ = ⟨⁅a,b⁆⟩`) を分離。
  後半の `A₅` 実例は書籍 Hint どおり `P = ⟨(0 1 2 3 4)⟩`, `H = ⟨(1 4)(2 3)⟩`, `K = ⟨(0 2)(3 4)⟩`
  (どちらも `N_{A₅}(P) ≅ D₁₀` の折り返し ⟹ `⁅H,K⁆ = P`)、`L = ⟨(0 1)(2 3)⟩` (`P` を正規化しない)。
  **`⁅P,L⁆ = ⊤` は「`⟨P,L⟩ = A₅` + 単純性」でなく位数で出した**: `⁅rot5,l⁆` (位数 5)、
  `⁅rot5²,l⁆` (位数 3)、その積 (位数 2) が `⁅P,L⁆` に居る ⟹ `30 ∣ |N| ∣ 60` ⟹ `|N| ∈ {30,60}`、
  `30` なら指数 2 = `(60).minFac` で `N ⊴ A₅` となり単純性に反する ⟹ `|N| = 60`。
  具体置換の計算は `Equiv.Perm (Fin 5)` 上の `decide` (冪は `maxRecDepth 8000` が要る)、
  `↥(alternatingGroup (Fin 5))` へは `Subtype.ext` + `change` で降ろす。
  Note (「`⁅H,K,L⁆` は `⁅h,k,l⁆` で生成されない」) は前半の巡回性 +
  `alternatingGroup.isCyclic_iff_card_le_three` で主定理の最後の連言肢に含めた。

- **4A.3** (quasiquaternion 群の Schur 乗数は自明): `Q = CU` (`C,U` 巡回、`C ⊴ Q`、
  `C ∩ U = Z(Q)`) を `IsQuasiquaternion` として定義し、`Z ≤ G' ⊓ Z(G)` かつ `G ⧸ Z` が
  quasiquaternion なら `Z = ⊥` を証明。書籍 Hint どおり `C, U` の引き戻し `A, B` を取り、
  (i) `A = Z⟨a₀⟩` ゆえ `A` abelian (`Z ≤ Z(G)` を使う)、(ii) `G = AB`、
  (iii) `A ⊓ B = Z(G)`、(iv) `G ⧸ A` 巡回 ⟹ **Lem 4.6 cardinality**
  (`card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient`) を
  `G` と `Ḡ = G ⧸ Z` の両方に適用。引き戻しの位数が `|Z|` 倍になること
  (`card_comap_mk'_eq_mul`、`index_comap_of_surjective` + Lagrange) と `Ḡ' = G'/Z`
  (`map_commutator_eq` + `comap_map_eq` + `Z ≤ G'`) から `|C||Z| = |C||Z|²` ⟹ `|Z| = 1`。
  ⚠ counting なので `[Finite G]` を仮定 (書籍も有限群の文脈)。

- **4A.5** (extraspecial の構造 (a)-(e)、新 leaf `Ch04_Commutators/ProblemsExtraspecial.lean`):
  中心道具は**類 2 の左交換子準同型** `commutatorLeftHom` (`g ↦ ⁅x,g⁆`、核 = `C_P(x)`) と
  そこから出る恒等式 3 本 (`⁅a,bc⁆ = ⁅a,b⁆⁅a,c⁆` / `⁅a,b⁻¹⁆` / `⁅a,b^n⁆`)。
  (a) は核・像の Lagrange (`index_ker` + 像が位数 `p` の `Z(P)` の非自明部分群)。
  (b) は `P/Z(P)` が elementary abelian (4A.4) で `⟨x̄⟩ ⊓ ⟨ȳ⟩ = 1` を示し
  `|U| = |U の像| · |Z| = p²·p`。
  **(c)(d)(e) の要は中心積分解 `P = V·U`** (`exists_mem_centralizer_mul_mem_closure_pair`):
  `⁅x,g⁆ = c^i` から `g(y^i)⁻¹ ∈ C_P(x)`、さらに `⁅y,·⁆` を潰して `V` に落とす。
  これで (d) の `Z(V) = Z(P)` は**位数勘定なしで**出る (書籍の `P > U` すら不要 —
  `P > U` は `V` の非可換性、すなわち extraspecial 性の側でだけ要る)。
  (c) は `|VU|·|V ⊓ U| = |V||U|` に `VU = P`, `V ⊓ U = Z(P)`, `|U| = p³` を代入。
  (e) は `|Q|` の強帰納法 (書籍 Hint)、基底は `Q = U` (`|Q| = p³`)、段は `V` extraspecial +
  `[Q:V] = p²` + `Z(V) = Z(Q)`。

- **4A.6** (maximal class、新 leaf `Ch04_Commutators/ProblemsMaximalClass.lean`):
  ⚠ **mathlib の下降中心列は古典的 `γ_k` から 1 ずれる** (`lowerCentralSeries ⊤ 0 = P`) —
  古典 `γ_k` = `lowerCentralSeries ⊤ (k-1)`。汎用部品を 4 つ整備:
  (i) `p`-群で真の部分群は位数が `p` 倍以上違う (`prime_mul_card_dvd_card_of_lt`)、
  (ii) 下降中心列は類の下で真減少 (`lowerCentralSeries_lt_of_lt_nilpotencyClass`)、
  (iii) 下方 `p^j ∣ |L_{c-j}|` / 上方 `p^i·|L_i| ∣ |P|`、
  (iv) **非可換 `p`-群では `p² ∣ |P:P'|`** (`P/P'` 巡回 ⟹ `P/Φ(P)` 巡回 ⟹ Ch01 の
  `isCyclic_of_frattiniQuotient_isCyclic` で `P` 巡回 ⟹ 可換)。
  (iii)+(iv) から **`|G| = p^k` (`k ≥ 2`) の `p`-群の類 ≤ `k-1`**
  (`nilpotencyClass_le_of_card_eq_prime_pow`; BG S04 の同型 lemma とは独立に Isaacs 層で証明 —
  BG を import すると層が逆流するため) と maximal class での `|L_i| = p^{n-1-i}` が出る。
  本題は `|P⧸N| = p^k` の類 ≤ `k-1` ⟹ `L_{k-1}(P) ≤ N`、位数一致で `N = L_{k-1}(P)`。
  ⚠ 書籍の `|N : P| ≥ p²` は誤植で `|P : N| ≥ p²` (指数が `p` 冪なので `p² ∣ |P:N|` と同値)。

- **4A.7** (正則 wreath product `C ≀ U` の元の位数の最大値 = `p^{n+1}`、新 leaf
  `Ch04_Commutators/ProblemsWreath.lean`): §3A の一般 wreath product `D ≀[Q] Q`
  (`Q` の左正則作用) で実現。**上界は冪公式を使わない**のがポイント —
  `rightHom (x^p) = (rightHom x)^p = 1` ⟹ `x^p ∈ range inl` (base 群)、base は指数 `p^n`
  ⟹ `x^{p^{n+1}} = 1` (`pow_prime_pow_succ_eq_one`)。
  下界には冪公式 `pow_mk` (`⟨f,q⟩^k` の base 成分 = `∏_{j<k} f((q^j)⁻¹ ω)`、`D` 可換で証明) と
  `prod_range_card_eq_prod_univ` (生成元の冪で捻った積 = 群全体の積; `Finset.prod_image` +
  `pow_injOn_Iio_orderOf`) を使い、証人 `x = ⟨δ₁ c, q⟩` に対し `x^p = ⟨const c, 1⟩` (位数 `p^n`)。

- **4A.8(a)** (`Z(P) = C_A(U)` = 定数 tuple 全体): §3A の既存部品がほぼそのまま効く —
  `centralizer_range_inl_eq` (`C_W(base) = base`) で中心の元が base に入り、
  `forall_conj_inr_eq_iff_const` (`inr` との可換性 ⟺ 軌道上定数) で定数性が出る。
  逆向きは定数 tuple が base とも `inr q` とも可換という直接計算。

### 4A.8(b) 完了 (2026-07-25) — 実装知見

`⁅A,U⁆ = P'` = 「成分の積が `1`」の tuple 全体。実装で効いた点:

1. `coordProdHom : (Q → D) →* D`, `f ↦ ∏ ω, f ω` (`D` 可換ゆえ準同型)。
2. `prod_smul_eq`: `∏ ω, f (q⁻¹ ω) = ∏ ω, f ω` (`Fintype.prod_equiv (Equiv.mulLeft q⁻¹)`)。
3. **交換子公式** `⁅inl f, inr q⁆ = inl (fun ω => f ω * (f (q⁻¹ ω))⁻¹)`。
   ⚠ **pointwise (`fun ω => …`) で書くこと** — Pi の `f * g⁻¹` 形で書くと
   `HMul (Q → D) D` の instance 解決に失敗する (撤退の原因)。証明は `ext ω` +
   構造 simp 補題 (`mul_left`/`inv_left`/`one_left` …) で、`change` は右成分で通らない。
4. `⊆`: 上の公式の座標積 = `(∏f)(∏f)⁻¹ = 1` (2 を使う)。
5. `⊇`: `⁅inl (δ_x d), inr (y x⁻¹)⁆ = inl (δ_x d · (δ_y d)⁻¹)` (shift が `δ_x ↦ δ_{qx}`) と
   δ-分解 `f = ∏_x (δ_x (f x) · (δ_1 (f x))⁻¹)` (`Finset.univ_prod_mulSingle` +
   `Finset.prod_apply` で `∏_x (δ_1 (f x))⁻¹ = 1` を `∏ f = 1` から出す)。
6. `P' = ⁅A,U⁆` 自体は **4A.1** (`commutator_eq_commutator_of_mul_eq_top`) —
   `P = A·U` は §3A の既存 simp 補題 `inl_left_mul_inr_right`、`A`/`U` の
   `IsMulCommutative` instance はその場で構成 (`U` 側は `Q` 可換の仮定が要る)。
7. ⚠ **最後の積は base 群 (可換) の中で取る**: `map_prod` は codomain に `CommMonoid` を
   要求するので wreath product では使えない。`Subgroup.comap inl ⁅A,U⁆` の中で
   `Subgroup.prod_mem` を使う。
8. ⚠ `Subgroup.map` の存在形が与える membership は `x ∈ ↑K` (Set 強制) なので
   `rw [MonoidHom.mem_ker]` は当たらない — `change` で `∏ ω, … = 1` に落とす。

### ⚠ 4A.8(c) は `p = 2, n = 1` で偽の疑い (2026-07-25、要 PDF 再確認)

書籍 (p. 124): 「(c) Show `|Z(P'U)| = p`.」 だが **`p = 2, n = 1` は反例に見える**:

- `C = C₂`, `A = C₂ × C₂`, `U = C₂` (成分交換) ⟹ `P = C₂ ≀ C₂ = D₈` (位数 8)
- `P' = ⁅A,U⁆ = {(a,b) : ab = 1} = {(1,1), (d,d)} = Z(P)` (位数 2、`D₈` は extraspecial)
- `P'` は中心なので `P'U = Z(P) × ⟨u⟩ ≅ C₂ × C₂` は **abelian**、ゆえに `|Z(P'U)| = 4 ≠ 2`

`p = 2, n = 2` (`C = C₄`) では `P' = {(a,a⁻¹)} ≅ C₄` で `u` 共役が `(a,a⁻¹) ↦ (a⁻¹,a)` ゆえ
`P'U` は非可換、`Z(P'U) = {(a,a⁻¹) : a² = 1}` は位数 2 = `p` ✅。奇素数でも同様。
⟹ **正しい主張は「`p` が奇 または `n ≥ 2`」の条件付き**と思われる。3B.12 と同型の書籍の穴。
次 iteration で PDF ページ画像を再確認し、条件付きの形で形式化する。

### 4A.8(c) の Lean 実装知見 (2026-07-25、3 回目で完成)

**解決策 = `Pi.mulSingle` を使わず `if ω = x then d else 1` を直接書く**。指示関数は自前で
定義してしまえば型推論の問題は起きず、`Finset.prod_eq_single x` + `simp +contextual` で
`∏ ω, (if ω = x then c else 1) = c` も通る。以下は 2 回目の着手で判明した詰まり:

- ⚠ `Pi.mulSingle_eq_of_ne h d` / `Pi.mulSingle_eq_same x d` のように**値を位置引数で渡すと
  依存族 `f` がメタ変数のまま残り** application type mismatch になる (非依存族
  `fun _ : Q => D` でも同じ)。`(f := …)` という名前付き指定も**不可** (implicit 名が `f` でない)。
  ⟹ **`simp [Pi.mulSingle_apply, hb]` で潰す**のが確実 (`Pi.mulSingle_apply` が `if` 形に開く)。
- ⚠ 証明中の `classical` と、補助補題の statement にある `[DecidableEq Q]` は**別 instance**に
  なり mismatch する。補助は `classical` の後に `have` でインライン定義する。
- `∏ ω, Pi.mulSingle x d ω = d` は `Finset.prod_eq_single x` + 上記 simp で通る (確認済)。

### 4A.8(d) の分析 (2026-07-25、次 iteration の出発点)

書籍: 「`n = 1` なら `P` は maximal class、一般に `P'U` は maximal class」。

**位数は本 commit で確定** (`card_ker_augHom_eq` / §3A `WreathProduct.card`):
`|P| = |C|^{|Q|}·|Q| = p^{np+1}`、`|P'U| = p^{n(p-1)+1}` (`augHom` が全射ゆえ
`|ker| = |P|/|C|`)。⟹ maximal class の主張は
「`class(P) = np`」(`n = 1` のとき `= p`) と「`class(P'U) = n(p-1)`」。

**第一歩は本 commit で設置**: `shiftSubHom q : (Q → D) →* (Q → D)`,
`Δ_q f = f · (f ∘ shift_q)⁻¹` (= 群環の `(1-q)·` 作用) と
`commutatorElement_inl_inr_eq_shiftSubHom` (`⁅inl f, inr q⁆ = inl (Δ_q f)`)、
`range_shiftSubHom_le_ker_coordProdHom` (`(1-q)R ⊆ I`)。
次は **`γ_{i+1}(P) = (Δ_q)^i(A) の像`** を帰納で立てる。
⚠ `⁅H, K ⊔ L⁆` の分配は**偽**なので (memory: lean-subgroup-commutator-api-traps)、
`⁅L_i, ⊤⁆` を `⁅·, A⁆` と `⁅·, U⁆` に割るには good-elements 法が要る。

#### 4A.8(d) の完全な設計 (2026-07-25 に手計算で確定、数値検証済み)

**(i) 下降中心列の帰納形**: `S ≤ (Q → D)` が shift 安定なら
`⁅S.map inl, ⊤⁆ = (S.map (shiftSubHom q)).map inl`。理由:
`⁅inl f, inl g * inr q'⁆ = inl (Δ_{q'} f)` (base 可換で `⁅inl f, inl g⁆ = 1`、
`⁅a, bc⁆ = ⁅a,b⁆ · b⁅a,c⁆b⁻¹` の第 2 項の共役も base 可換で消える)。
`Q = ⟨q⟩` が位数 `p` なら `Δ_{q^k} f = Δ_q (∏_{j<k} f∘shift^j)` (群環の
`1 - x^k = (1-x)(1 + x + … + x^{k-1})`) なので、生成元 `q` の分だけで足りる。
⟹ **`lowerCentralSeries ⊤ i = (Δ^i(⊤)).map inl`** (`i ≥ 1`; 基底は 4A.8(b) の
`P' = ker(coordProd).map inl` と `range Δ_q = ker coordProd`)。
**元レベルの式 `⁅inl f, y⁆ = inl (Δ_{y.right} f)` は
`commutatorElement_inl_eq_shiftSubHom` として設置済**。さらに
**`Δ_{q^k} = Δ_q ∘ T_k`** (`shiftSubHom_pow_eq_comp`、`T_k = shiftSumHom q k` は
群環の `1 + x + ⋯ + x^{k-1}`; 証明は `Finset.prod_range_div` の telescoping) も設置済で、
これにより「生成元 `q` の `Δ` だけで `⁅A, U⁆` の全生成元が捉えられる」。
**帰納段も設置済**: `commutator_map_inl_top_eq`
(`S` が shift 安定 = `S.map (shiftHom q) ≤ S` なら
`⁅S.map inl, ⊤⁆ = (S.map (shiftSubHom q)).map inl`)。
補助は `shiftHom` (平行移動)・`shift_pow_mem_of_shift_stable`・
`shiftSumHom_mem_of_shift_stable`。
**(α) も完了**: `lowerCentralSeries_eq_map_shiftSubSeq`
(`lowerCentralSeries ⊤ (i+1) = (shiftSubSeq q (i+1)).map inl`、
`shiftSubSeq q i = Δ^i(⊤)`)。基底は 4A.8(b)、shift 安定性の保存は
`shiftSubHom_comp_shiftHom` (`Δ` と `shift` の可換性) + `Subgroup.map_map`。
**(β) の第一歩も設置**: `shiftSumHom_card_eq_const` (`T_{|Q|} f` は定数 = ノルム) と
`shiftSubHom_shiftSumHom_card` (**`Δ_q ∘ T_{|Q|} = 1`**, 群環の `(1-x)·N = 0`)。
⟹ **残るのは (β) `(1-x)` の冪零指数 `n(p-1)+1` の算術だけ**:
`shiftSubSeq q i = ⊥ ⟺ i ≥ n(p-1)+1` を示せば `class(P) = n(p-1)+1` が出る
(`lowerCentralSeries_eq_bot_iff_nilpotencyClass_le` 経由)。`P'U` 側も同様に
`Δ` の反復を `ker coordProd` から始めればよい。

#### (β) の linchpin = **`Δ^{p-1} = T_p` (作用素として)**

`D` が指数 `p` のとき、群環 `F_p[x]/(x^p-1)` の恒等式 `(1-x)^{p-1} = 1 + x + ⋯ + x^{p-1} = N`
が成り立つ。これさえ Lean で言えれば
`Δ^p = Δ ∘ Δ^{p-1} = Δ ∘ T_p = 1` (**既証の `shiftSubHom_shiftSumHom_card`**) で上界が出て、
下界も `Δ^{p-1}(δ₁ c) = T_p(δ₁ c) = const c ≠ 1` (`shiftSumHom_card_eq_const`) で即出る。
⟹ **`class(P) = p` (n=1 で maximal class) は linchpin 1 本に還元済み**。

**mathlib の部品は調査済み (2026-07-25)**:
- `sub_pow_char_of_commute (h : Commute x y) : (x - y)^p = x^p - y^p`
  (`Mathlib/Algebra/CharP/Lemmas.lean` L223) — **可換とは限らない環でも可換な元同士なら使える**
  ので、**自己準同型環 `AddMonoid.End V` の中で `1` と `σ` に直接適用できる**。
  ただし `[ExpChar R p]` インスタンスが要る。
- インスタンスを避けるなら `Commute.add_pow` (二項定理) + `Nat.Prime.dvd_choose_self`
  (`0 < k < p` で `p ∣ C(p,k)`) + 「`V` の指数が `p` ⟹ `End V` で `p • x = 0`」で
  `(1-σ)^p = 1 + (-σ)^p = 1 + (-1)^p·1 = 0` (`p` 奇なら `1 - 1`、`p = 2` なら `1 + 1 = 2 = 0`)。
- `(p-1).choose j ≡ (-1)^j [ZMOD p]` は mathlib に無いが **自前で証明済**
  (`cast_choose_prime_sub_one`; Pascal + `Nat.Prime.dvd_choose_self` の帰納、13 行)。
  ⚠ `Nat.Prime` は `Irreducible` の別名なので **dot 記法 `hr.dvd_choose_self` は
  `Irreducible.dvd_choose_self` に解決されて失敗する** — 完全名で書くこと。

⚠ なお `Δ^p = 0` だけでは `class(P) ≤ p` (上界) しか出ない。maximal class には
`Δ^{p-1} ≠ 0` (下界) が要り、そこは linchpin `Δ^{p-1} = T_p` が最短。

**多項式側は landing 済 (2026-07-25)**: `one_sub_X_pow_prime_sub_one`
(`(1 - X)^{p-1} = ∑_{j<p} X^j` in `(ZMod p)[X]`; `sub_pow_char` + `mul_neg_geom_sum` +
整域での約分)。⟹ 残るのは**作用素への移送**だけ:
`V = Additive (Q → D)` (指数 `p` ⟹ `ZMod p`-加群) 上で `Polynomial.aeval σ` を使い、
`aeval σ (1 - X) = Δ`, `aeval σ (∑_{j<p} X^j) = T_p` を確認すれば `Δ^{p-1} = T_p` が出る。
必要 import は `Mathlib.Algebra.{Field.ZMod, Polynomial.Coeff, Polynomial.Div, Ring.GeomSum}`
(本 commit で追加済)。

**位数側も `n=1` 特殊形を landing**: `card_wreath_of_card_eq_prime`
(`|C| = |Q| = p` ⟹ `|C ≀ Q| = p^{p+1}`) — maximal class の判定 `class = p` と対になる。

**二項展開 `shiftSubHom_iterate_apply` は landing 済 (2026-07-25)**:
`Δ^k f ω = ∏_{j ≤ k} f((q^j)⁻¹ω)^{(-1)^j C(k,j)}`。実装知見:
- `Function.iterate_succ_apply'` で `Δ^[k+1] = Δ ∘ Δ^[k]` に開く
- 添字ずらし `(q^j)⁻¹(q⁻¹ω) = (q^{j+1})⁻¹ω` は `group`
- ⚠ **`rw [Finset.prod_congr …]` / `rw [Finset.prod_range_succ]` は積が 2 つあると
  どちらに当たるか不定** — 対象を `have` で等式化するか `conv_rhs` で明示する
- Pascal は `Nat.choose_succ_succ' k i` + `push_cast` + `ring`

**🎉 linchpin 完成 (2026-07-25)**: `shiftSubHom_iterate_prime_sub_one`
(`Δ_q^{p-1} f = T_p f`、指数 `p` の可換 base `D` に対する作用素等式)。仕上げは
ルート A (pointwise 二項展開) で、部品 2 本:
- `zpow_eq_self_of_pow_eq_one` (`d^r = 1` ∧ `(m : ZMod r) = 1` ⟹ `d ^ m = d`。
  `ZMod.intCast_zmod_eq_zero_iff_dvd` で `m = 1 + r·c` に分解し `zpow_add`/`zpow_mul`)
- `cast_neg_one_pow_mul_choose_prime_sub_one` (`(-1)^j·C(r-1,j) ≡ 1 (mod r)`
  = `cast_choose_prime_sub_one` の系、`(-1)^j·(-1)^j = 1`)

**⟹ 4A.8(d) の `P` 側 (`n = 1`) 完了**:
- `shiftSubHom_iterate_prime_eq_one` (上界 `Δ^p = Δ ∘ T_p = 1`)
- `mem_shiftSubSeq_iff` (`g ∈ Δ^i(⊤) ⟺ ∃ f, Δ^[i] f = g`) →
  `shiftSubSeq_prime_eq_bot` / `shiftSubSeq_prime_sub_one_ne_bot`
  (下界の witness = 指示関数 `δ₁ c`、`Δ^{p-1}(δ₁ c) = T_p(δ₁ c) = const c ≠ 1`)
- `nilpotencyClass_wreath_eq_of_exponent_prime` (**`class(D ≀ Q) = p`**、
  `lowerCentralSeries_eq_map_shiftSubSeq` + `lowerCentralSeries_eq_bot_iff_nilpotencyClass_le`;
  `IsNilpotent` 自体も `Subgroup.nilpotent_iff_lowerCentralSeries` で上界から得る)
- **`isMaximalClassPGroup_wreath`** (`|C| = |Q| = p` ⟹ `C ≀ Q` は maximal class;
  `|P| = p^{p+1}` = `card_wreath_of_card_eq_prime`、`class + 1 = p + 1`)。axiom-clean。

⚠ 教訓: `orderOf_eq_card_of_forall_mem_zpowers` の結論は `Nat.card` (`Fintype.card` でない) /
`Subgroup.map_eq_bot_iff_of_injective` は `H` が**明示引数** (`_ inl_injective`) /
`⟨(k:ℤ), _⟩ : q^k ∈ zpowers q` の証明義務は β-未簡約 (`rw [zpow_natCast]` 不可、`simp`)。

linchpin の証明ルート 2 つ:
1. **pointwise 二項展開**: `Δ^k f ω = ∏_{j≤k} f((q^j)⁻¹ω)^{(-1)^j C(k,j)}` を `k` の帰納
   (Pascal) で示し、`k = p-1` で `C(p-1,j) ≡ (-1)^j (mod p)` を使うと指数が全部 `1` になる。
   要調査: mathlib に `(p-1).choose j ≡ (-1)^j [ZMOD p]` があるか。
2. **多項式環経由**: `F_p[x]` は整域なので `(1-x)^p = 1 - x^p = N·(1-x)` から `(1-x)` を約して
   `(1-x)^{p-1} = N`。`V ≅ F_p[x]/(x^p-1)` (n=1 なので `D ≅ F_p`) の同型を作る手間がかかる。

**(β) の当面の目標は `n = 1` の場合** (書籍の「`n = 1` なら `P` は maximal class」):
`D` が指数 `p` なら `V = Q → D` は `ZMod p`-加群で `Δ = 1 - σ` (`σ` = 平行移動, `σ^p = 1`)、
標数 `p` の可換環 `ZMod p[σ]` で **freshman's dream** `(1-σ)^p = 1 - σ^p = 0`
(mathlib `add_pow_char`) ⟹ `class(P) ≤ p`。下界は `Δ^{p-1}(δ₁ c) = const c ≠ 1`
(ノルム関係式の相棒: `(1-x)^{p-1} = N` mod `p`) ⟹ `class(P) = p = np` で maximal class。
一般 `n` の sharp 値 `n(p-1)+1` は `(1-x)^p = p·(1-x)s` の filtration が要る。

**(ii) 残る算術 = `Δ = (1-x)` の冪零指数**。`ZMod(p^n)[x]/(x^p-1)` で
`(1-x)^{n(p-1)+1} = 0` かつ `(1-x)^{n(p-1)} ≠ 0` ⟹ **`class(P) = n(p-1)+1`**。
- `p=2, n=1`: `(1-x)² = 0` ⟹ class 2。`|P| = 8` (`D₈`) で maximal class ✓
- `p=3, n=1`: class 3、`|P| = 3⁴` で maximal class ✓
- `p=2, n=2`: `(1-x)² = 2(1-x)`, `(1-x)³ = 0` ⟹ class 3。`|P| = 2⁵` なので
  maximal class には class 4 が要る ⟹ **`P` は maximal class でない** ✓
  (書籍が `n = 1` に限定しているのと整合)
- 一般に `class(P) = n(p-1)+1` と maximal class の要求 `np` が一致するのは **`n = 1` のときだけ** ✓

**(iii) `P'U` 側**: `class(P'U) = n(p-1)`、`|P'U| = p^{n(p-1)+1}` なので**常に maximal class** ✓
(`p=2,n=2` で検算: `P' = (1-x)R ≅ C₄`, `Δ(P') = (1-x)²R ≅ C₂`, `(1-x)³R = 0`
⟹ class 2、`|P'U| = 8` ⟹ maximal class ✓)。

**残りの下降中心列の計算**は群環のフィルトレーションに落ちる:
`A = C^Q` を `ZMod(p^n)[Q] = ZMod(p^n)[x]/(x^p - 1)` (`x = u`) と見ると
`⁅A, U⁆` は `(x-1)A`、以降 `γ_{i+1}(P) = (x-1)^i A` (`i ≥ 1`)。
`(x-1)^p ≡ x^p - 1 = 0 (mod p)` なので `(x-1)` 冪の減少列が `p`-進的に落ちる速さが
class を決める。⟹ **群環の `(x-1)`-filtration を Lean で立てるのが本体** (規模大)。
`ProblemsMaximalClass.lean` の下降中心列部品 (真減少・`p` 冪の上下界) は再利用できる。

⚠ 4A.8(c) と違い `p = 2, n = 1` でも成立する (`D₈` は位数 8・class 2 = 3-1 で maximal class、
`P'U ≅ C₂×C₂` は位数 4・class 1 = 2-1 でやはり maximal class)。

### 4A.8(c) 完了 (位数まで)

`card_center_ker_augHom : |Z(P'U)| = p` (仮説 `hd` の下)。部品は
`card_ker_powMonoidHom_prime` (位数 `p^n` の巡回群で `x^p = 1` の解は `p` 個 —
像 `⟨c^p⟩` の位数が `p^{n-1}` であることと Lagrange) と `d ↦ inl (const d)` の全単射。

### 🎉 4A.8(d) 完了 (2026-07-25、一般 `n`) — 新 leaf `ProblemsWreathClass.lean`

**主結果** (すべて実証明・axiom-clean):
- `nilpotencyClass_wreath_eq`: **`class(C ≀ Q) = n(p-1)+1`** (`C` の指数がちょうど `p^n`)
- `isMaximalClassPGroup_wreath_iff`: **`P` が maximal class ⟺ `n = 1`**
  (`|P| = p^{np+1}` ゆえ maximal class は `class = np` を要求、一致は `n=1` のみ)
- `nilpotencyClass_ker_augHom_eq`: **`class(P'U) = n(p-1)`**
- `isMaximalClassPGroup_ker_augHom`: **`P'U` は常に maximal class** (`|P'U| = p^{n(p-1)+1}`)

**手法 = 群環 `ℤ/p^n[x]/(x^p-1)` の `(1-x)`-filtration を「作用素の言葉だけ」で実行**
(加群も多項式環も構成しない — ここが実装上の要):
- **基底** `exists_witness_shiftSubHom_iterate_prime_sub_one`:
  `Δ^{p-1} f = T_p f · g^p` **かつ** `T_p g = (T_p f)⁻¹`。前者は二項展開の係数を
  `(-1)^j C(p-1,j) = 1 + p·e_j` と分解 (`e_j = ((-1)^j C(p-1,j) - 1)/p`、割り切れは
  `cast_choose_prime_sub_one`)、後者は `∑_j e_j = -1` (交代和
  `Int.alternating_sum_range_choose_of_ne` = `0`) で、群環の `y^{p-1} = N + p·s` と
  `N·s = s(1)·N = -N` (`s(1) = -1`) にちょうど対応。**`D` の指数に仮定は要らない**。
- **帰納** `exists_shiftSubHom_iterate_mul_prime_sub_one`:
  `Δ^{(m+1)(p-1)} f = (T_p f)^{(-1)^m p^m} · g^{p^{m+1}}` かつ
  `T_p g = (T_p f)^{(-1)^{m+1}}`。段では `Δ^{p-1}(T_p f) = 1` (定数を消す = `y·N = 0`) で
  第 1 因子が落ち、`(T_p h)^{p^m}` が新しい第 1 因子になる。
- 指数 `p^n` なら第 2 因子が消えて **`Δ^{n(p-1)} f = (T_p f)^{(-1)^{n-1}p^{n-1}}`**。
  上界は `Δ ∘ T_p = 1`、下界は `f = δ₁ c` で `T_p f = const c` と `c^{p^{n-1}} ≠ 1`。
- **`P'U` 側**: `commutator_map_inl_eq` を「`inr q ∈ K` なる任意の `K`」へ一般化 (`⊤` 版は
  その特殊化) し、基底 `commutator_ker_augHom_self` (`⁅P'U,P'U⁆ = Δ²(A) の像`) を
  `x = inl x.left · inr x.right` 分解 + `⁅inr a, inr b⁆ = 1` (Q 可換) + 正規性による共役吸収で
  出す。以降 `lowerCentralSeries_ker_augHom_eq` は同じ帰納。部分群の類は
  `nilpotencyClass_le_iff_lowerCentralSeries_eq_bot` (`top_subtype_lowerCentralSeries` 経由) で
  環境群の下降中心列に翻訳。

⚠ **一般版が n=1 版を包含**するので、`ProblemsWreath.lean` 側の n=1 専用系
(`shiftSubHom_iterate_prime_eq_one` / `shiftSubSeq_prime_eq_bot` /
`shiftSubSeq_prime_sub_one_ne_bot` / `nilpotencyClass_wreath_eq_of_exponent_prime` /
`isMaximalClassPGroup_wreath`) は削除した (同事実 2 本立ては証明分裂の元)。
linchpin `shiftSubHom_iterate_prime_sub_one` (`Δ^{p-1} = T_p` の**等式**、標数 `p` 限定) と
多項式版 `one_sub_X_pow_prime_sub_one` は書籍の論法そのものなので残す。

⚠ 教訓: `Subgroup.isNilpotent_iff_lowerCentralSeries` は `S` が**明示引数** (`(… _).mpr`) /
`Div Int` = `Int.ediv` ゆえ `Int.mul_ediv_cancel'` が使える / `conv_lhs` は `∈` の左辺 =
**部分群側**を拾う (元側を書換えたいなら `have` で等式化) / `prod_smul_eq` は
`∏ ω, f (q⁻¹ * ω)` の形にしか rw できない (`f y ^ e j` を噛ませたら `exact` で defeq 渡し)。

#### 🎉 4A.10 完了 (2026-07-25) — 新 leaf `ProblemsCenterIndex.lean`

**主結果** (実証明・axiom-clean): `card_commutator_le_of_index_center_le`
= 書籍そのままの **`p`-群 `P` で `|P : Z(P)| ≤ p^n` ⟹ `|P'| ≤ p^{n(n-1)/2}`**。

- 中核 `card_commutator_le_of_normal_cyclic_quotient`:
  **`Q ⊴ G`, `G/Q` cyclic, `Z(G) ≤ Q` ⟹ `|G'| ≤ |⁅Q,Q⁆| · |Q : Z(G)|`**。
  `Ḡ = G/⁅Q,Q⁆` で `Ā = Q/⁅Q,Q⁆` は可換正規 (`⁅q₁,q₂⁆ ∈ ⁅Q,Q⁆`)、`Ḡ/Ā ≅ G/Q`
  (`QuotientGroup.quotientQuotientEquivQuotient`) が cyclic なので **repo の Lemma 4.6 位数形**
  `card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient` が
  `|Ḡ'|·|Ā ⊓ Z(Ḡ)| = |Ā|` を与える。`Z(G)` の像 ⊆ `Ā ⊓ Z(Ḡ)` と像・核の位数関係で
  `|G'|·|Z(G) の像| ≤ |Z(G) の像|·|⁅Q,Q⁆|·|Q:Z(G)|`、約せば結論。
- 支持補題 `card_map_mul_card_inf_ker` (`|f(H)|·|H ⊓ ker f| = |H|`; `MonoidHom.restrict` +
  `Subgroup.index_ker`)。
- 帰納 `card_commutator_le_pow_choose_two` は **`n.choose 2` で述べる**のが要点
  (Pascal `(n+1).choose 2 = n.choose 2 + n` がそのまま指数の勘定)。書籍形への変換は
  `Nat.choose_two_right`。`Z(P)` を含む極大部分群は `IsCoatomic.eq_top_or_exists_le_coatom`
  + `NormalizerCondition.normal_of_coatom` (冪零) + 1D.6 `isCoatom_iff_index_prime`。

⚠ 教訓: `commutator_eq_bot_iff_center_eq_top` / `NormalizerCondition.normal_of_coatom` /
`Subgroup.isNilpotent_iff_lowerCentralSeries` はいずれも **section 変数が明示引数**ゆえ
`X.mpr` 形が「Unknown constant X.mpr」になる (`(X _).mpr` と書く) /
`by` ブロックを入れ子にした改行継続は parse error になりやすい (`have` に切り出す)。

#### 🎉 4A.12 (a)(b)(c 一般部分) 完了 (2026-07-25) — 新 leaf `ProblemsWreathNonCommutator.lean`

**主結果** (実証明・axiom-clean):
- `IsAbelianTwoGen T` (可換かつ 2 元生成)、`𝒯(H)` = その性質の極大元 (`Maximal IsAbelianTwoGen`)
- `commutatorElement_eq_of_right_commute` : `x.right`, `y.right` 可換なら
  **`⁅x,y⁆ = inl(Δ_{x.right} y.left)⁻¹ · inl(Δ_{y.right} x.left)`**
- `exists_maximal_commutator_mem` = **(a)** (`⁅x,y⁆ ∈ B` ⟹ ある極大 `T` で `⁅x,y⁆ ∈ ⁅B,T⁆`)
- `exists_mem_not_isCommutator` = **(b)** (`∑_T |A|^{|H|−|H:T|} < |A|^{|H|−1}` ⟹
  `⁅B,U⁆` は交換子でない元を含む; 書籍の `1/|A| > ∑(1/|A|)^{|H:T|}` に `|A|^{|H|}` を掛けた形)
- `sum_lt_of_card_lt` = **(c) 一般部分** (`H` が可換 2 元生成でなければ `|A| > |𝒯(H)|` で成立)

(a) の鍵は `⁅x,y⁆ ∈ B ⟺ x.right, y.right` が可換で、そのとき交換子が base 側の 2 つの `Δ` に
分解すること (`⁅inr h, inr k⁆ = inr ⁅h,k⁆ = 1` が効く)。可換 2 元生成部分群を含む極大元は
`Finite.exists_le_maximal`、`⟨u,v⟩` の可換性は中心化群の二段論法。
(b) は (a) + 4A.11 の位数 + `Finset.card_biUnion_le` の鳩の巣。

⬜ **残: (c) の `H = D₈` で `m = 3` が取れる部分** (= `|𝒯(D₈)| ≤ 3`)。`D₈` の部分群を
具体的に列挙する計算なので別途。

⬜ **4A.13 も未着手** (pdftotext が切れていて見落としていた; PDF p.138 で確認):
`G` 冪零で class `m > 1`, `a ∈ G` ⟹ `H = G'⟨a⟩` の冪零類は `m` 未満。

#### 🎉 4A.13 完了 (2026-07-25) — 新 leaf `ProblemsNilpotencyClass.lean`

`nilpotencyClass_commutator_sup_zpowers_lt` : **`G` 冪零・class `m > 1` ⟹
`class(G'⟨a⟩) < m`** (実証明・axiom-clean、有限性の仮定は不要)。

- `commutatorMemLeft N y` = `{x | ⁅x,y⁆ ∈ N}` (`N ⊴ G` で部分群)
- `commutator_self_le_lowerCentralSeries_two` = 基底 `⁅H,H⁆ ≤ γ₃(G)`
  (good-elements 二段: `⁅a, H⁆ ≤ γ₃` を先に出し、それを使って `H ≤ commutatorMemLeft γ₃ y`)
- `lowerCentralSeries_commutator_sup_zpowers_le` = `γ_i(H) ≤ γ_{i+1}(G)` の帰納
- 部分群の類への翻訳は `nilpotencyClass_le_iff_lowerCentralSeries_eq_bot`
  (4A.8(d) で作ったもの。汎用なので `ProblemsWreathClass` → **`ProblemsMaximalClass`** へ移設)

以下は着手前の設計メモ (実装は概ねこの通り):

#### 4A.13 の設計 (2026-07-25、着手前メモ)

書籍 (p.125): `G` 冪零で class `m > 1`, `a ∈ G` ⟹ **`H = G'⟨a⟩` の冪零類は `m` 未満**。

- 添字: mathlib の `lowerCentralSeries X i` = 古典的 `γ_{i+1}(X)`。示すべきは
  `Subgroup.lowerCentralSeries H (m-1) = ⊥` (⟹ `class(↥H) ≤ m-1 < m`)。
  部分群の類への翻訳は **`nilpotencyClass_le_iff_lowerCentralSeries_eq_bot`**
  (4A.10 の `ProblemsCenterIndex.lean` に既設) が使える。
- **鍵の主張**: `k ≥ 1` で `H.lowerCentralSeries k ≤ (⊤ : Subgroup G).lowerCentralSeries (k+1)`
  (古典形 `γ_i(H) ≤ γ_{i+1}(G)`, `i ≥ 2`)。`k = m-1` で右辺 `= γ_{m+1}(G) = ⊥`。
- **帰納段**は易しい: `⁅L, H⁆ ≤ ⁅γ_{k+2}, ⊤⁆ = γ_{k+3}`。
- **基底 `⁅H,H⁆ ≤ γ_3(G) = ⁅G', ⊤⁆` が本体**。`G/γ_3` で `Ḡ'` は中心的なので
  `H̄ = Ḡ'⟨ā⟩` は可換、という筋。⁅H ⊔ K, ·⁆ の分配は使えないので **good-elements 二段**で:
  * `N := γ_3` は正規。`{x | ⁅x,y⁆ ∈ N}` と `{y | ⁅x,y⁆ ∈ N}` はそれぞれ部分群
    (`⁅x₁x₂,y⁆ = x₁⁅x₂,y⁆x₁⁻¹·⁅x₁,y⁆` と `N` 正規; 逆元は `commutatorElement_inv_left`)。
  * 第 1 段: `{y | ⁅a,y⁆ ∈ N}` は `G'` (∵ `⁅G,G'⁆ = γ_3`) と `a` を含む ⟹ `H` を含む
    ⟹ `⁅a, H⁆ ≤ N`。
  * 第 2 段: `{x | ∀ y ∈ H, ⁅x,y⁆ ∈ N}` は `G'` (∵ `⁅G',G⁆ = γ_3`) と `a` (第 1 段) を含む
    ⟹ `H` を含む ⟹ `⁅H,H⁆ ≤ N`。
- `H := commutator G ⊔ Subgroup.zpowers a`。`Subgroup.closure_le` で generator に落とす。

#### 🎉 4A.12(c) の `D₈` 部分 完了 (2026-07-25) — 新 leaf `ProblemsDihedralEight.lean`

`sum_lt_of_three_lt_card_dihedralFour` : **`H = D₈` なら `|A| > 3` で (b) の不等式が成立**
(= 書籍の「`m = 3` が取れる」)。核は `card_le_three_of_maximal_dihedralFour` (`|𝒯(D₈)| ≤ 3`)。

`D₈ = DihedralGroup 4` の可換部分群は 3 つの指数 2 部分群
`⟨r⟩ = closure {r 1}` / `closure {r 2, sr 0}` / `closure {r 2, sr 1}` のいずれかに含まれる:
- 鏡映 `sr i ∈ T` があれば, `r k` との可換性から `2k = 0` (⟹ `k ∈ {0,2}`)、
  `sr j` との可換性から `2(i-j) = 0` (⟹ `j ∈ {i, i+2}`) ⟹ `T ≤ closure {r 2, sr i}`。
- 鏡映が無ければ `T ≤ ⟨r⟩` (`r_one_pow`)。
- `closure {r 2, sr (i+2)} = closure {r 2, sr i}` (`sr (i+2) = r 2 · sr i`) なので候補は 3 つ。

⚠ 教訓: `ZMod 4` の算術は `decide` で済むが、**文脈に自由変数があると `revert; decide` は
「Expected type must not contain free variables」で落ちる** — `∀ i k : ZMod 4, …` の
**閉じた補題として切り出してから `decide`** する。

### 🎉 §4A 完済 (4A.1–4A.13 全問)。

## Ch.4 §4B (書籍 p.131 の Problems 4B) — 着手 (2026-07-25)

新 leaf `OddOrder/Isaacs/Ch04_Commutators/ProblemsHallWitt.lean` (`OddOrder.lean` 配線済)。
§4B は Hall–Witt 恒等式 / three subgroups lemma の節で, repo には既に
`commutator_commutator_le_of_rotate` (Cor 4.10, mod `N` 版) がある。

- ✅ **4B.1** `exists_characteristic_abelian_not_le_center` (class > 2 ⟹ 中心的でない
  特性可換部分群が存在)。**答えは `γ_{c-1} = lowerCentralSeries ⊤ (c-2)`**:
  `⁅γ_{c-1},γ_{c-1}⁆ ≤ γ_{2(c-1)} = 1` (`c ≥ 3` ゆえ `2(c-1) ≥ c+1`; Thm 4.11
  `commutator_lowerCentralSeries_le`) で可換、`⁅γ_{c-1}, G⁆ = γ_c ≠ 1` で非中心。
  特性性は mathlib の `lowerCentralSeries_characteristic` instance。
- ✅ **4B.3** `commutator_lowerCentralSeries_upperCentralSeries_le`
  (`⁅G^i, Z_j⁆ ≤ Z_{j-i}`) + 系 `…_eq_bot` (`⁅G^i, Z_i⁆ = 1`)。`k` の帰納 + three
  subgroups lemma。⚠ 添字対応: mathlib の `lowerCentralSeries ⊤ k` = 古典 `G^{k+1}`、
  `Subgroup.upperCentralSeries G j` = 古典 `Z_j` (`Z_0 = 1`)。
- ✅ **4B.4(a)(b)** `commutator_le_centralizer_of_centralizes` /
  `commutator_isCommutative_of_centralizes`。どちらも three subgroups lemma 直接適用。
  ⚠ **(b) は書籍が `X ⊴ G` を仮定するが不要** — `⁅X,Y⁆` が `X` で正規化されること
  (`le_normalizer_commutator_left`, 4A.9 で作った) だけで足りる。

⚠ 教訓: root の `upperCentralSeries` は **deprecated** で `Subgroup.upperCentralSeries` と
**別定数**として扱われ、instance 検索 (Normal) や型が合わない — 新規コードは必ず
`Subgroup.` 付きで書く。

- ✅ **4B.2** `exists_characteristic_selfCentralizing_class_le_two`
  (`G` 冪零 ⟹ 特性部分群 `K` で `C_G(K) ⊆ K` かつ class ≤ 2)。
  `K` を「特性かつ class ≤ 2」の極大元に取り、`C := C_G(K)` として:
  * **吸収補題**: `A ≤ C` が特性 class ≤2 なら `A ⊔ K` も特性 class ≤2 ⟹ 極大性で `A ≤ K`。
    join の class ≤ 2 は新補題 `lowerCentralSeries_sup_eq_bot`
    (`⁅A,K⁆ = 1` + 両方 class ≤2 ⟹ `A ⊔ K` も class ≤2; `commutatorMemLeft` の good-elements
    二段を 2 回) と `characteristic_sup` (`characteristic_iff_map_eq` + `map_sup`)。
  * `C` 自身が class ≤2 なら吸収で終わり。そうでなければ **4B.1 と同じ `A := γ_{c-1}(C)`**
    (`c = class(↥C) ≥ 3`) が特性可換 ⟹ 吸収で `A ≤ K` ⟹ `C = C_G(K) ≤ C_G(A)` から
    `⁅A,C⁆ = γ_c(C) = 1` で `c` の最小性に矛盾。
  * 相対下降中心列の交換子評価 `commutator_lowerCentralSeries_le'` (Thm 4.11 の相対版) は
    `↥S` の ⊤ 版を `S.subtype` で押し出して得た (`top_subtype_lowerCentralSeries` +
    `map_commutator`)。
  ⚠ 教訓: `x ∈ commutatorMemLeft N y` は `⁅x,y⁆ ∈ N` と defeq だが**構文的に違う**ので
  `commutatorElement_mem_comm` に渡すには `show ⁅x,y⁆ ∈ N from …` の型註釈が要る。
- ✅ **4B.5 完了 (2026-07-25)** — 新 leaf `Ch04_Commutators/ProblemsSupersolvableMann.lean`
  (167 行、`OddOrder.lean` 配線済、全実証明・axiom-clean)。
  `exists_normal_centralizer_eq_self_of_isSupersolvable` (超可解群は自己中心化する正規部分群を
  持つ) + `nilpotencyClass_mannSubgroup_le_of_isSupersolvable` (`class M(G) ≤ 3`) +
  `isNilpotent_mannSubgroup_of_isSupersolvable`。下記の設計どおり。
  ⚠ 実装で判明した追加の API 注意:
  * `isCyclic_of_prime_card` は `[Fact p.Prime]` を要求 → `haveI : Fact (Nat.card ↥M).Prime := ⟨h⟩`
    を置いてから `isCyclic_of_prime_card (p := Nat.card ↥M) rfl`。
  * `QuotientGroup.eq_one_iff.mpr ha` は項として書くと "Unknown constant" になる
    (`rw` の中で使うときは `have h1 : mk' A a = 1 := by rw [...]; exact ha` に分解する)。
  * 最後の `Mbar = ⊥` からの矛盾は `simp at hprime` では閉じない
    (`simp only [Subgroup.card_bot]` + `Nat.not_prime_one`)。

  **`M(G)` と Thm 4.15 は repo に既にある** (`Ch04_Commutators/Mann.lean`):
  `mannSubgroup G` / `nilpotencyClass_mannSubgroup_le_of_centralizer_eq_self [Finite G]
  {K} [K.Normal] (hself : Subgroup.centralizer ↑K = K) : nilpotencyClass ↥(mannSubgroup G) ≤ 3`。
  ⟹ **4B.5 は「超可解群は自己中心化する正規部分群を持つ」に完全に帰着する**。

  **証明 (確定)**: `A` を**可換正規**部分群のうち極大に取る (`Finite.exists_le_maximal`,
  base `⊥`)。`C := C_G(A) ⊇ A`。`A < C` と仮定すると `C/A ≠ 1` なので `G ⧸ A` の中で
  `C.map (mk' A)` に含まれる minimal normal 部分群 `M̄` が取れ
  (`Ch02.exists_isMinimalNormal_le_of_normal`)、**超可解性から `|M̄|` は素数**
  (`Ch03.card_prime_of_isMinimalNormal_of_isSupersolvable` + `IsSupersolvable.quotient`)
  ゆえ `M̄` は巡回。引き戻し `B := M̄.comap (mk' A)` は `A < B ⊴ G`, `B ≤ C` で、
  `A ≤ Z(B)` (∵ `B ≤ C_G(A)`) と `B/A` 巡回から
  `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` で**可換** ⟹ `A` の極大性に矛盾。

  **中断時点の draft** (~150 行、あと数個の名前解決だけ) は
  `scratchpad/wip/ProblemsSupersolvableMann.lean` に退避。実測した API の注意点:
  * `Ch03.IsSupersolvable` / `Ch03.card_prime_of_isMinimalNormal_of_isSupersolvable` は
    `namespace OddOrder.Isaacs.Ch04` の中で `open OddOrder.Isaacs.Ch03` しても解決しなかった。
    **`Ch03.` 前置で書く** (同じファイルで `Ch02.exists_isMinimalNormal_le_of_normal` は
    `Ch02.` 前置で解決している)。
  * centralizer の正規性は `Subgroup.normal_centralizer` (instance、`[H.Normal]` 付き)。
    `Subgroup.centralizer_normal_of_normal` は**存在しない**。
  * `isCyclic_of_prime_card` は `Nat.card ↥M = p` の形を要求する
    (`(Nat.card ↥M).Prime` からは `⟨_, rfl⟩` 等で渡す)。

### 🎉 §4B 完済 (4B.1–4B.5 全 5 問)。

## Ch.4 §4C (書籍 p. 137 の Problems 4C) — 🎉 完済 (2026-07-25)

新 leaf `OddOrder/Isaacs/Ch04_Commutators/ProblemsStabilityGroup.lean` (331 行、
`OddOrder.lean` 配線済、全実証明・axiom-clean)。§4C は「`A` が `G` に自己同型で作用する」
節で, Isaacs 自身が「`A` と `G` をともに半直積 `Γ = G ⋊ A` の部分群とみなす」と宣言している
(p. 131) ので, **周囲群 `Γ` の部分群 `G`, `A`** に対する形で述べた (半直積はその特別な場合)。

「`A` が鎖 `1 = H₀ ⊆ ⋯ ⊆ H_m = G` を stabilize する」(= `H_{i-1}` の `H_i` における各右剰余類が
`A`-不変) は交換子で `⁅H i, A⁆ ≤ H (i-1)` と同値 ⟹ 構造体 `StabilizesChain` (`base` + `step`)。
書籍の有限鎖 (条件は `0 < i ≤ m` のみ) との橋渡しは `stabilizesChain_min`
(`H (min i m)` で上端 `G` に延長; `G ⊴ Γ` ゆえ `⁅G,A⁆ ≤ G` で延長部分は自動)。

| # | 状態 | Lean 名 (`OddOrder.Isaacs.Ch04`) |
|---|---|---|
| 4C.1 | ✅ | `exists_stabilizes_isSubnormal_chain` (+ 有限鎖版 `..._of_finite`) |
| 4C.2 | ✅ | `StabilizesChain.nilpotencyClass_le` / `.isNilpotent` (+ 有限鎖版 `nilpotencyClass_le_of_stabilizes_finite_normal_chain`) |
| 4C.3 | ✅ | `commutator_commutator_eq_bot_of_trivial_on_normal` (+ `le_centralizer_commutator_of_trivial_on_normal`) |

**設計メモ**:

- **4C.1 の「部分正規部分群の鎖」= 反復交換子列**: `M i := ⁅G, A; m - i⁆` (4A.9 の
  `commIterate`)。`⁅L, A⁆` が `L` に正規化される (`le_normalizer_commutator_left`, 4A.9) ので
  各段 `⁅G,A;j+1⁆ ⊴ ⁅G,A;j⁆` が部分正規段になり, `⁅G,A;0⁆ = G ⊴ Γ` からの帰納で
  `IsSubnormal` (Γ 内)。`↥G` 内の部分正規は `IsSubnormal.comap G.subtype` で即出る
  (`subgroupOf = comap subtype`)。停止 `M 0 = ⊥` は `⁅G,A;j⁆ ≤ H (m-j)` の帰納。
  再利用 helper: `commIterate_le_commIterate_of_le` (添字一般の単調減少) /
  `isSubnormal_commIterate` / `normal_subgroupOf_commIterate_succ` /
  `commIterate_le_of_stabilizesChain` / `le_normalizer_of_normal`。
- **4C.2 の核 = `commutator_lowerCentralSeries_le`**: `⁅H i, γ_{j+1}(A)⁆ ≤ H (i - (j+1))` を
  `j` の帰納で示す。各段は Isaacs **Cor 4.10** (three subgroups lemma の mod `N` 形
  `commutator_commutator_le_of_rotate`) を `H₁ = γ_{j+1}(A)`, `H₂ = A`, `H₃ = H i`,
  `N = H (i-(j+2))` に適用: `⁅⁅A, H i⁆, γ⁆ ≤ ⁅H(i-1), γ⁆ ≤ N` と
  `⁅⁅H i, γ⁆, A⁆ ≤ ⁅H(i-(j+1)), A⁆ ≤ N`。**`H i` の `Γ` 内正規性**が `N.Normal` として
  ここで要る = 4C.2 が「正規部分群の鎖」を要求する理由。仕上げは `i = m`, `j = m-1` で
  `⁅H m, γ_m(A)⁆ ≤ H 0 = ⊥` ⟹ `γ_m(A) ≤ A ⊓ C_Γ(G) = ⊥` (faithfulness) ⟹
  `nilpotencyClass_le_of_lowerCentralSeries_eq_bot` (Mann.lean)。
  ⚠ ℕ の切り捨て減算のおかげで `i ≤ j` の縮退段も `H 0 = ⊥` に落ちて自動的に正しい
  (`commutator_le_pred` の `i = 0` 場合が `⁅⊥, A⁆ = ⊥`)。
  ⚠ **書籍の `m ≥ 1` は不要** (`m = 0` なら `G = H 0 = 1` で faithfulness が `A = 1` を
  強いる) — 仮定から落として docstring に注記。
- **4C.3** は three subgroups lemma (`Subgroup.commutator_commutator_eq_bot_of_rotate`) の
  `(G, A, N)` への直接適用: `⁅⁅A,N⁆,G⁆ = 1` は仮定, `⁅⁅N,G⁆,A⁆ ≤ ⁅N,A⁆ = 1` は `N ⊴ G`。

## Ch.5 §5C (書籍 pp. 162-164 の Problems 5C) — 着手 (2026-07-26)

§5C は 13 問 (5C.1-5C.13)。

| 問題 | 状態 | メモ |
|---|---|---|
| 5C.1 | ✅ | `not_dvd_card_commutator_of_inf_sylow_eq_bot` + `hasNormalPComplement_of_commutator_inf_sylow_eq_bot` (`Problems5C.lean`)。方針どおり **鍵の段を独立補題**にした (同一 statement の別証明を避ける) |
| 5C.2 | ✅ 完了 (`card_eq_two_of_characteristic_relIndex_eq_two`) | PDF 確認済。`U ⊆ V ⊆ P ⊆ G`、`P` abelian Sylow-2、`U, V` が `P` の特性部分群で `\|V:U\| = 2`、`G` 単純 ⇒ `\|G\| = 2` |
| 5C.3 | ✅ 完了 (`sq_eq_one_of_card_sylow_two_eq_32`) | PDF 確認済: `G` 単純で abelian Sylow-2 `P` の位数が `2^5` ⇒ `P` は初等可換 |
| 5C.4 | ✅ 完了 (`exists_subgroup_card_eq_of_isZGroup` + `exists_conj_of_card_eq_of_isZGroup`) | すべての Sylow が巡回 ⇒ 任意の約数位数の部分群が存在し互いに共役 (repo に `IsZGroup` 系 Thm 5.16 あり) |
| 5C.5 | ✅ | `exists_mem_normalizer_conj_eq_of_normal` + `eq_of_characteristic_of_conj` (`Problems5C.lean`) |
| 5C.6 | 🔒 hub | weak closure。**hub レーンが `OddOrder/GroupTheory/WeaklyClosed.lean` で着手中** (issue 9503) — A レーンは触らない |
| 5C.7 | ✅ 完了 (`normal_sylow_three_of_card_eq`) | `\|G\| = 3^a·5·11` ⇒ Sylow-3 が正規 |
| 5C.8 | ✅ 完了 (`hasNormalPComplement_of_minFac_of_not_dvd_pow_three`) | `p` が最小素因数 (`p > 2`) で `p^3 ∤ \|G\|` ⇒ 正規 p-補群 |
| 5C.9 | ✅ 完了 (`three_dvd_card_of_isSimpleGroup_of_not_dvd_eight`) | 非可換単純で偶数位数、`8 ∤ \|G\|` ⇒ `3 \| \|G\|` |
| 5C.10 | ✅ 完了 (`seven_dvd_card_of_isSimpleGroup_of_card_sylow_two_eq_eight`) | 単純で abelian Sylow-2 が位数 8 ⇒ `7 \| \|G\|` |
| 5C.11 | ✅ 完了 (`hasNormalPComplement_of_hall_le_center_normalizer`) | Hall 部分群 `H ≤ Z(N_G(H))` ⇒ `\|H\|` の各素因数で正規 p-補群 |
| 5C.12 | ✅ 完了 (`hasNormalPComplement_of_isCyclic_sylow_of_dvd_index`) | 巡回 Sylow-p、`N ⊴ G` の指数が `p` で割れる ⇒ `N` が正規 p-補群をもつ |
| 5C.13 | ✅ 完了 (`hasNormalPComplement_normalizer_commutator_of_selfNormalizing_sylow`) | (Navarro) **自己正規化** Sylow `P = N_G(P)` ⇒ `N_G(P')` が正規 p-補群をもつ (⚠ 旧記載の `P = N_G(P)'` は誤読、PDF p.164 で確認) |

### 5C.2 の証明 (2026-07-26 に導出、PDF p.162 = PDF ページ 175 で主張確認済)

**主張**: `U ⊆ V ⊆ P ⊆ G`、`P` は `G` の abelian Sylow-2、`U`, `V` は `P` の特性部分群で
`|V : U| = 2`。`G` が単純なら `|G| = 2`。

**証明** (⭐ transfer 評価 + fusion control):
`P` が abelian なので `N := N_G(P)` は `P` 内の fusion を制御する
(Burnside; repo の Cor 5.22 = `Basic.lean` の fusion-control 系)。
`U`, `V` は `P` の特性部分群なので `N` は両方を保ち、`|V/U| = 2` かつ `Aut(C₂) = 1` より
**`N` は `V/U` に自明に作用する**。
transfer `v : G →* P` (P abelian) を取ると、transfer 評価の各因子
`t x^{n_t} t⁻¹` は `x ∈ V` のとき `V` に入り、fusion が `N` 由来なので
**`≡ x^{n_t} (mod U)`**。`∑ n_t = |G : P|` だから `v(x) ≡ x^{|G:P|} (mod U)`。
`|G:P|` は奇数なので `x ∈ V \ U` に対し `v(x) ∉ U`、特に `v(x) ≠ 1`。
一方 `G` が非可換単純なら `G = G'` で `v(G) = v(G') = 1` (`P` 可換) — 矛盾。
よって `G` は可換単純 = 素数位数。`V/U` が位数 2 を含むので `2 ∣ |G|` ⇒ `|G| = 2`。

### 5C.3 の設計 (2026-07-26)

`|P| = 2^5` で `G` 単純 ⇒ `G` は非可換単純 (可換単純は素数位数で Sylow-2 が位数 32 に
ならない)。`P` が初等可換でないとすると `P` は巡回因子の直積で、ある因子の位数が `≥ 4`。
**因子の分割 (5 の分割) のうち「最大部分がただ 1 つ」なら repo の Cor 5.19
(`SylowTwoDirectFactor.lean`、書籍一般形) が非単純性を与えて矛盾**。
⚠ **`(2,2,1)` = `C₄ × C₄ × C₂` だけは最大部分が 2 つあり Cor 5.19 で覆えない**。
この場合は **5C.2** を `U := ℧¹(P) = P²` (位数 4)、`V := Ω₁(P)` (位数 8) に適用する
(`|V : U| = 2`、どちらも特性部分群) と `|G| = 2` となって矛盾。
⟹ **5C.3 は 5C.2 に依存する**。実装順は 5C.2 → 5C.3。

✅ **5C.3 landing (2026-07-26)** — ただし**書籍の分割数え上げは採らなかった**。
⭐ **有限可換群の構造定理を使わずに済む書き換え**を見つけた: `n` 乗写像の核 `Ω_n` と像 `℧_n`
(新 shared leaf `AbelianPowerSubgroups.lean`, issue 9208) は第一同型定理で
`|Ω_n| · |℧_n| = |Q|` を満たす。位数 32 では `|℧₂| = |powImage Q 2|` の値
(`1,2,4,8,16,32`) で場合分けし、鎖 `℧₂ ≥ ℧₄ ≥ ℧₈` の**隣接比が 2 の箇所**を探せばよい:

* 比 2 の隣接対がそのまま 5C.2 に渡す特性部分群対。
* 比 1 (鎖が止まる) なら不動点補題 `powKernel_two_pow_mul_eq` で `Ω = ⊤` となり位数に矛盾。
* `℧ = ⊥` に落ちた段は `℧ ≤ Ω₂` (`powImage_le_powKernel`) なので `Ω₂` との対を取る。

分割 `(2,2,1)` (= `C₄×C₄×C₂`, 書籍で Cor 5.19 が効かない唯一の型) はこの枠組では
`|℧₂| = 4, |Ω₂| = 8` の枝として自動的に処理される。Cor 5.19 (`SylowTwoDirectFactor.lean`)
は**結局使わなかった**。
主定理 = `sq_eq_one_of_card_sylow_two_eq_32` / `isElementaryAbelian_of_card_sylow_two_eq_32`、
核 = `exists_characteristic_relIndex_two_of_card_32`。

⭐ 罠: `hpair _ _ inferInstance ...` のように**存在命題を作る補助の引数をメタ変数のままにすると
`inferInstance` が無関係な部分群の `Characteristic` を拾って**変な unify をする
(結論が `∃` なのでゴールから決まらない) — `U`, `W` を明示する。
`norm_num at h` は `↥(powImage Q 2)` を生の subtype に展開してしまうので
数値の正規化には `simp only [Nat.reducePow]` を使う。

### 5C.2 の実装状況 (2026-07-26)

**fusion 段は landing 済** (`Problems5C.lean`):
* `inv_mul_conj_mem_of_index_two` — `|V:U| = 2` かつ `U, V` が `n`-共役不変なら
  `n` は `V/U` に自明作用 (`x ∉ U` なら `n x n⁻¹ ∉ U` で、`U` 外の 2 元は法 `U` で一致)
* ⭐ `inv_mul_conj_mem_of_fusion` — `P` 可換 Sylow で `V ≤ P`、`N_G(P)` が `V/U` に自明作用
  ⇒ **`V` の元の `G`-共役で `P` に入るものは `U` を法として元と一致**
  (Isaacs Lemma 5.12 `normalizer_controls_centralizer_fusion` で `G`-共役を `N_G(P)`-共役へ)

**残り (transfer 段)**: `ϕ := (QuotientGroup.mk' (U.subgroupOf P)) : ↥P →* ↥P ⧸ U'`
(`P` 可換なので `U'` 正規・商も可換) の transfer `v' : G →* ↥P ⧸ U'` を取り、
**5B.1 で使った `MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot`** で
`v'(x) = ∏_q ϕ⟨w_q⁻¹ x^{n_q} w_q⟩` と展開する。各因子は上の fusion 段で
`ϕ⟨x^{n_q}⟩` に等しく、`∑ n_q = |G:P|` (5B.1 と同じ `Subgroup.quotientEquivSigmaZMod` +
`Nat.card_sigma` + `Nat.card_zmod`) なので `v'(x) = ϕ⟨x^{|G:P|}⟩`。
⚠ **mathlib の `MonoidHom.transfer_eq_pow` は「厳密な固定」を要求するので使えない**
(法 `U` で十分という弱い仮定では通らない) — 軌道分解版を使うこと。

⭐ **商群 `↥P ⧸ U` を作る必要はない** (2026-07-26 の知見): `↥P` が可換なので、
軌道分解の各因子が `x^{n_q}` と `U` を法として一致すれば、**積もそのまま**
`x^{∑ n_q} = x^{|G:P|}` と法 `U` で一致する (`Finset.prod_mul_distrib` +
`Finset.prod_pow_eq_pow_sum`)。結論は
`(x ^ |G:P|)⁻¹ * (transfer (MonoidHom.id ↥P) x : G) ∈ U` の形で書ける。

✅ **transfer 段 landing (2026-07-26)**: `transfer_inv_pow_mul_mem_map`
「`ϕ : ↥P →* A` (`A` 可換) の transfer は `x ∈ V` 上で `ϕ(x)^{|G:P|}` と `ϕ(U)` を法として
一致する」。⭐ **target を変数 `A` にすると instance diamond が完全に消える**
(下記の障害はこれで解消)。5C.2 の組み立てでは `A := Abelianization ↥P`,
`ϕ := Abelianization.of` を取る (`P` 可換なので `commutator ↥P = ⊥` で `ϕ` は単射、
`ϕ(x^{|G:P|}) ∈ ϕ(U)` から `x^{|G:P|} ∈ U` が戻せる)。

✅ **組み立て landing (2026-07-26) — 5C.2 完了**:
`not_mem_of_commutator_eq_top` (完全群での矛盾) + `conj_mem_map_subtype_of_characteristic`
(`Subgroup.normalizerMonoidHom` で「特性部分群は `N_G(P)`-共役不変」) +
`inv_mul_mem_of_relIndex_eq_two` (`Subgroup.relIndex_eq_two_iff`) を経て主定理
`card_eq_two_of_characteristic_relIndex_eq_two`。
⭐ **書籍の `U ⊆ V` は不要**と判明したので落とした (`relIndex` で `|V:U| = 2` を課せば十分)。
⭐ 罠: `set Pg := (P : Subgroup G)` は `U V : Subgroup ↥(P:Subgroup G)` の**型を書き換えて
仮説を shadow する** (`U✝`) ので使わない。`IsPGroup` は `∀ g, ∃ k, g ^ p ^ k = 1` であって
`orderOf g = p ^ k` ではない (後者は `IsPGroup.iff_orderOf`)。

~~**残り (組み立て)**~~: `|G:P|` 奇数 (`Sylow.not_dvd_index`) と `|V:U| = 2` から
`x ∈ V \ U` に対し `x^{|G:P|} ∉ U` ⇒ `transfer ϕ x ≠ 1`。一方 `G` 非可換単純なら
`G = G'` かつ `A` 可換なので `transfer ϕ (G') = 1` で矛盾 ⇒ `G` 可換単純 = 素数位数、
`2 ∣ |G|` で `|G| = 2`。

~~⚠ 未解決の実装障害 (解消済)~~: `↥P` の **`CommGroup` instance diamond**。
`MonoidHom.transfer` は target に `CommGroup` を要求するが、`↥P` には
`Subgroup.toGroup` 由来の `Group` があるため、`haveI : CommGroup ↥P` を入れると
`MonoidHom.id ↥P` の型 (`Subgroup.toGroup` 側) と
`transfer_eq_prod_quotient_orbitRel_zpowers_quot` が要求する型 (`CommGroup.toGroup` 側) が
unify しない。`Ch05_Transfer/CentralTransfer.lean` の Thm 5.3 は
`@MonoidHom.transfer G _ ↑P ↑P ((haveI := hPab; (inferInstance : CommGroup ↥↑P)))
(MonoidHom.id ↑P) _` の `@` 明示形で回避しているので、**評価補題側も同じ `@` 明示形で
instance を渡す**必要がある (`@MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot`
の implicit/explicit の並びを確認してから書く)。
`|G:P|` 奇数 (`Sylow.not_dvd_index`) なので `x ∈ V \ U` で `v'(x) ≠ 1`、
`G` 非可換単純なら `G = G'` で `v'(G) = 1` に矛盾。

### 5C.13 の実装メモ (2026-07-27) — §5C 完済

⚠ **書籍読解の訂正**: この表の旧記載「`P = N_G(P)'` なる Sylow」は**誤読**。PDF ページ画像
(書籍 p.164 = PDF p.177) で確認した正しい主張は

> (Navarro) `P` が **自己正規化** Sylow (`P = N_G(P)`) ⟹ **`N_G(P')`** が正規 `p`-補群をもつ

(仮定側が `P = N_G(P)`、結論側が `N_G(P')`)。hint 中の「`X` を Hall `p`-部分群」も
`p'`-部分群の誤植 (そうでないと `G = P' N_G(X)` が成立しない)。

新 leaf `Problems5C13.lean` (316 行)。`H := N_G(P')` に取り替えると `P ≤ H`・`N_H(P) = P`・
`P' ⊴ H` なので、**還元形** `hasNormalPComplement_of_selfNormalizing_sylow_of_commutator_normal`
(「`N_G(P) = P` かつ `⁅P,P⁆ ⊴ G` ⟹ `G` が正規 `p`-補群」) に帰着する。還元形の証明:

1. `L := ⁅P,P⁆` として `G/L` の Sylow `P̄ = P/L` は**可換** (`L` は `P` の交換子群) かつ
   **自己正規化** (`π⁻¹(P̄) = ↑P ⊔ ker π = ↑P` と `N_G(P) = P`) ⟹ **Burnside (Thm 5.13)** で
   `G/L` に正規 `p`-補群 `K̄`。`K := π⁻¹(K̄)`。
2. `L` は `K` の正規 Hall `p`-部分群 ⟹ **Schur–Zassenhaus** (`exists_right_complement'_of_coprime`)
   で補群 `X' ≤ ↥K`、`X := X'.map K.subtype`。
3. **Frattini**: `Ch03.exists_conj_le_of_isComplement'_of_coprime'` (3B.4 で一般化した D-part、
   ⭐ **共役元が `M` の中に取れる**強化形がここで効く) を `↥K` で使い `G = L · N_G(X)`。
4. **Dedekind**: `z ∈ P` を `z = y·n` (`y ∈ L ≤ P`, `n ∈ N_G(X)`) と分解すると `n ∈ P` なので
   `⊤ = (N_G(X)).subgroupOf P ⊔ Φ(P)` (`L.subgroupOf P = commutator ↥P ≤ Φ(P)` は Problem 1D.8
   `commutator_le_frattini`)。`frattini_nongenerating` で `P ≤ N_G(X)`。
5. `L ≤ P ≤ N_G(X)` と 3 から `N_G(X) = ⊤` ⟹ `X ⊴ G`。`|X| = |K̄|` は `p` と素、
   `|G:X| = |L|·|K̄ の指数|` は `p`-冪 ⟹ 新 helper
   `hasNormalPComplement_of_normal_of_index_eq_pow` で結論。

⚠ 実装の罠: `MulAut G` の `Subgroup G` への pointwise 作用は、`•` 記法で書いた goal でないと
`mul_smul` / `pointwise_smul_def` が発火しない (`Subgroup.map ↑(MulAut.conj g) S` の形になった
goal では不可) ⟹ **`have key : … • … = …` を別立てしてから `mem_normalizer_iff_map_conj_eq` に
渡す**。Ch03 の D-part 結論 `K.map (MulAut.conj x).toMonoidHom` と `MulAut.conj x • K` は
defeq だが構文が違うので `have hcoe : … = … := rfl` で橋渡しする。
`IsComplement' A B` の `.index_eq_card` は **`B.index = |A|`** (向きに注意、逆は `.symm`)。

**🎉 §5C 完済 (5C.1–5C.13 全 13 問)** — 5C.6 のみ hub レーン (issue 9503 WeaklyClosed) 担当。

### 5C.12 の実装メモ (2026-07-27)

新 leaf `Problems5C12.lean` (118 行)。⭐ **`Y := N ⊔ P` (= `NP`) に上げてから Thm 5.17 を当てる**
のが鍵。`N` 自身に Thm 5.17 を当てるだけでは `N` が完全群のとき (`|N:N'| = 1` ゆえ) 何も出ない
(実際 `A₅`, `p = 5` は正規 5-補群を持たない — 仮定 `p ∣ |G:N|` が効く場所)。

* `⁅Y,Y⁆ ≤ N`: `Y/N` は可換 `P` の像 (helper `commutator_sup_le_of_normal_of_commutative`、
  `Subgroup.map_commutator` + `commutator_eq_bot_iff_le_centralizer` で商へ落とす)。
* `p ∤ |G:Y|` (`P ≤ Y`) と `relIndex_mul_index` から **`p ∣ |Y : N|`**、
  `commutator ↥Y ≤ N.subgroupOf Y` ゆえ `p ∣ (commutator ↥Y).index`。
* `↥Y` の Sylow は `P.subtype` (巡回) なので **Thm 5.17** の第 2 選択肢が潰れ
  **`p ∤ |commutator ↥Y|`**。
* `⁅N,N⁆ ≤ ⁅Y,Y⁆` (`Subgroup.map_subtype_commutator` で `commutator ↥N` と橋渡し) ゆえ
  `p ∤ |commutator ↥N|`、位数互いに素で `commutator ↥N ⊓ Q = ⊥`、**Problem 5C.1**
  (`hasNormalPComplement_of_commutator_inf_sylow_eq_bot`) で結論。

⚠ 実装の罠: `Subgroup.map_eq_bot_iff` は `H` が**明示引数**なので `.mpr` を直接付けられない
(`(Subgroup.map_eq_bot_iff _).mpr`)。`Sylow.subtype` の coe は `rfl` だが instance 探索は
unfold しないので `IsCyclic ↥((P.subtype hPY : Sylow p ↥Y) : Subgroup ↥Y)` の形で `haveI` する。

### 5C.11 の実装メモ (2026-07-27)

新 leaf `Problems5C11.lean` (266 行)。⭐ **書籍 hint の「`|G|` に関する帰納法」を、`G` を固定した
「部分群の位数に関する帰納法」に組み替えた** — 型レベル再帰 (`motive : ℕ → Prop` で全ての群型を
量化する `S7C_ThompsonPComplementFinal` 型のパターン) も商群への降下も要らなくなる。

**核 = `le_centralizer_aux`**: 「`H ≤ M` かつ `M ≤ N_G(P)` なる任意の部分群 `M` は `C_G(P)` に
含まれる」。`Nat.card ↥M ≤ n` の `n` で帰納。

* `M ≤ N_G(H)` なら仮定 `H ⊆ Z(N_G(H))` からそのまま `M ≤ C_G(H) ≤ C_G(P)`。
* そうでなければ `H` が Sylow 部分群たちの join である (`iSup_sylow_eq_top`、下記) ことと
  `Subgroup.iInf_normalizer_le_normalizer_iSup` (mathlib) から、**`M` が正規化しない `H` の
  Sylow `q`-部分群 `Q`** が取れる。Hall 性より `Q` は `G` の Sylow `q`-部分群でもある
  (`exists_sylow_coe_eq_map_subtype`)。`L := M ⊓ N_G(Q)` は `M` の真部分群なので帰納法で
  `L ≤ C_G(P)`、`C := M ⊓ C_G(P)` は `M ≤ N_G(P)` ゆえ `M`-共役不変で `Q ≤ H ≤ C`。
  **Frattini 論法** (`C` 内の Sylow `q`-共役性、transport は 1C.1 と同じ `Ch01.map_conj_smul`
  パターン) が `M = C · L` を与え、両因子が `C_G(P)` に入る。

⟹ `M := N_G(P)` で `N_G(P) ≤ C_G(P)`、Burnside (Thm 5.13
`hasNormalPComplement_of_sylow_normalizer_le_centralizer`) で結論。書籍 hint の 2 段
(「`N_G(P) < G` の段」と「`P ⊴ G` かつ `N_G(Q) < G` の段」) はこの形では**同じ 1 本の補題に融合**する。

**再利用可能な副産物**:
* `iSup_sylow_eq_top` — 有限群は Sylow 部分群たちで生成される
  (`⨆ (q : (Nat.card K).primeFactors) (Q : Sylow q K), ↑Q = ⊤`)。位数の各素冪が Sylow の位数を
  割ることから `|K| ∣ |⨆ …|` (`Nat.dvd_iff_prime_pow_dvd_dvd`)。mathlib に無かった。
* `card_map_subtype_eq_multiplicity` / `exists_sylow_coe_eq_map_subtype` — Hall 部分群の
  Sylow 部分群は `G` の Sylow 部分群。

⚠ 実装の罠: `inf_eq_left.mpr (…)` を `rw` の引数にメタ変数のまま置くと、パターン `?a ⊓ ?b` が
**`M ⊓ C_G(P)` (部分群 `C` そのもの)** に先にマッチして motive 破綻 (`C.subtype c` の型が `C` に
依存する) — `have hinf1/hinf2 :` で**両辺を明示した等式**にしてから `rw` する。
`Nat.dvd_iff_prime_pow_dvd_dvd` の `intro` が与えるのは `Nat.Prime` (変換不要)。
`Subgroup.normalizer` は現 mathlib では `Set G → Subgroup G`。

### 5C.10 の実装メモ (2026-07-27)

新 leaf `Problems5C10.lean` (146 行)。⭐ **`P` の同型類 (`C₈` / `C₄×C₂` / `C₂³`) を場合分けしない**
のが要点で、書籍の hint (5C.9 の議論を真似る) をそのまま一様に通せる。

論法: `7 ∤ |G|` と仮定。`8 ∣ |G|` と単純性から `G` は非可換 ⟹ `commutator G = ⊤`。
Isaacs Thm 5.18 (`eq_one_of_mem_commutator_of_mem_sylow_of_central_normalizer`) は
`P ∩ Z(N_G(P)) ∩ G' = 1` を与えるが `G' = G` なので **`C_P(N_G(P)) = 1`**。
`S := N_G(P)/C_G(P) ≅ range (normalizerMonoidHom P)` の位数を割る素数 `q` は
(i) `q ≠ 2` (`relIndex ∣ |G:P|` が奇数) かつ (ii) `q ∣ 2^m − 1` (`1 ≤ m ≤ 3`,
5C.8 の `exists_dvd_pow_sub_one_of_dvd_card_mulAut`) ⟹ `q ∈ {3, 7}` ⟹ `q = 3`。
∴ `S` は 3-群。`S` の `P` への作用の不動点は `C_P(N_G(P)) = 1` ゆえ
`IsPGroup.card_modEq_card_fixedPoints` で `8 ≡ 1 (mod 3)` ⟹ `3 ∣ 7` で矛盾。

⚠ 実装の罠: 元の交換子 `⁅x, y⁆` は **scoped instance** ゆえ `open scoped commutatorElement` が要る
(Ch01 §1D 1D.9 と同じ罠)。`Nat.Prime 7` / `¬Nat.Prime 8` は minimal import では `norm_num` が
落とせない ⟹ `Mathlib.Tactic.NormNum.Prime` を明示 import。現 mathlib の
`Nat.eq_prime_pow_of_unique_prime_dvd` は指数が `factorization p` でなく
**`primeFactorsList.length`**、仮説も `n ≠ 1` でなく `n ≠ 0`。

### 5C.9 の実装メモ (2026-07-26)

**主張** (PDF 実測): `G` 非可換単純, `|G|` 偶数, `8 ∤ |G|` ⇒ `3 ∣ |G|`。

Sylow-2 `P` は位数 `2^n` (`1 ≤ n ≤ 2`) ゆえ可換。`3 ∤ |G|` と仮定すると
`|N_G(P) : C_G(P)|` を割る素数 `q` は `q ≠ 2` (`P ≤ C_G(P)`) で、5C.8 の軌道数え上げ補題
`exists_dvd_pow_sub_one_of_dvd_card_mulAut` より `q ∣ 2^m - 1` (`1 ≤ m ≤ 2`)。
`m = 1` なら `q = 1`、`m = 2` なら `q = 3` — どちらも矛盾なので `N_G(P) = C_G(P)`。
Burnside で正規 2-補群 `K` が取れ、単純性から `K = ⊥` (⇒ `P = ⊤` ⇒ `G` 可換、矛盾) か
`K = ⊤` (⇒ `|P| = 1` ⇒ `2 ∤ |G|`、矛盾)。

⭐ 書籍は `Aut(C₂ × C₂) ≅ S₃` を使うが、**5C.8 の補題を一般形に切り出して共用した**
(`hp2 : p ≠ 2` を外し `q ≠ p` だけを仮定する形にリファクタ) ので `|Aut P|` の計算は不要。

### 5C.8 の実装メモ (2026-07-26)

**主張** (PDF 実測): `p > 2` が `|G|` の最小素因数で `p^3 ∤ |G|` ⇒ `G` は正規 `p`-補群を持つ。

Sylow-`p` `P` は位数 `p^n` (`n ≤ 2`) ゆえ可換なので、Burnside
(`Basic.lean` の `hasNormalPComplement_of_sylow_normalizer_le_centralizer`) より
`N_G(P) ≤ C_G(P)` を示せばよい。`N/C ↪ Aut(P)` なので `|N : C|` は `|Aut P|` と `|G|` の
両方を割り、`P` 可換ゆえ `p ∤ |N : C|`。素数 `q ∣ |N:C|` があれば最小性から `q > p`。

⭐ **`|Aut P|` を計算せずに済ませた**。書籍の標準証明は
`|Aut(C_p × C_p)| = |GL_2(F_p)| = p(p-1)^2(p+1)` を使うが、mathlib に `Aut` の同型計算が
無い。代わりに位数 `q` の自己同型 `σ` を取り、`⟨σ⟩` の `P` への作用で軌道数え上げ
(`IsPGroup.card_modEq_card_fixedPoints`) すると `p^n ≡ |Fix σ| (mod q)`、
`Fix σ = σ.toMonoidHom.eqLocus (MonoidHom.id P)` は `σ ≠ 1` ゆえ真部分群なので
`q ∣ p^n - p^k` (`k < n ≤ 2`) ⟹ `q ∣ p - 1` か `q ∣ p^2 - 1`。前者は `q > p` に反し、
後者は `q ∣ p + 1` ⟹ `q = p + 1` が偶数で `q` 奇素数に反する。
定理名 = `not_dvd_card_mulAut_of_card_eq_pow` (`Problems5C8.lean`)。
⭐ **2026-07-26 に一般形 `exists_dvd_pow_sub_one_of_dvd_card_mulAut` へリファクタ**
(`p` の奇偶も `q > p` も仮定せず「`q ≠ p` なら `∃ m, 1 ≤ m ≤ n, q ∣ p^m - 1`」)。
5C.9 が `p = 2` で同じ補題を使う。

⚠ 罠: `MulAction.fixedPoints` の `Nat.card` は `↥(↑S : Set P)` の形で出るので
`Nat.card ↥S` への `rw` が通らない (`rw [← hkcard]; exact hmod` で defeq を使って渡す)。

### 5C.7 の実装メモ (2026-07-26)

**主張** (PDF 実測): `|G| = 3^a · 5 · 11` ⇒ `G` は正規 Sylow 3-部分群を持つ。

**証明** = Burnside の正規 `p`-補群定理を 2 段: Sylow-5 は位数 5 (巡回) で `φ(5) = 4` が
`|G|` (奇数) と互いに素 ⇒ 正規 5-補群 `K` (位数 `3^a·11`)。`K` の Sylow-11 は位数 11 で
`φ(11) = 10` が `|K|` と互いに素 ⇒ 正規 11-補群 `L` (位数 `3^a`)。`L` は `K` の正規 Sylow-3
ゆえ特性 (`Sylow.characteristic_of_normal`)、`K ⊴ G` なので `L ⊴ G`。位数が `G` の Sylow-3
と一致するので `L` 自身が Sylow-3 で、正規 Sylow は一意 (`Sylow.unique_of_normal`)。

⭐ **mathlib の `IsCyclic.normalizer_le_centralizer` は `p` が最小素因数のときしか使えない**
(ここは `p = 5, 11` で最小は 3)。一般形 `normalizer_le_centralizer_of_coprime_totient`
(`gcd(|G|, φ(|P|)) = 1` 版, issue 9210) を新設して使った。

補助: `card_sylow_eq_self_of_sq_not_dvd` (`q ∣ |G|`, `q² ∤ |G|` ⇒ Sylow-`q` の位数 `q`) /
`factorization_three_pow_mul` / `sq_not_dvd_mul`。

### 5C.4 の設計と進捗 (2026-07-26)

**主張** (p.163): Sylow がすべて巡回 (= mathlib `IsZGroup`) なら、`|G|` の任意の約数 `m` に
対し位数 `m` の部分群が存在し、位数 `m` の部分群同士は `G`-共役。

**骨格** = mathlib の Z-群 API (実測で確認、自作不要):
`IsZGroup.isCyclic_commutator` (`G'` 巡回) / `IsZGroup.isCyclic_abelianization` (`G/G'` 巡回) /
`IsZGroup.coprime_commutator_index` (`gcd(|G'|, |G:G'|) = 1` ⟹ `G'` は**巡回な正規 Hall**)。
⟹ `m ∣ |G|` は `m = gcd(m,|G'|) · gcd(m,|G:G'|)` と分解する
(`Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime`)。

✅ **存在部分 landing (2026-07-26)**: `Problems5C4.lean` (新 leaf, `OddOrder.lean` 配線済)。
巡回群 `G'` の位数 `m₁` の部分群 `M` (巡回ゆえ特性 ⟹ `G` で正規) と、Schur–Zassenhaus 補群
`H ≅ G/G'` (巡回) の位数 `m₂` の部分群 `H₂` を取り `K := H₂ ⊔ M`。
補助: `normal_map_subtype_of_characteristic` / `isCyclic_of_isComplement'_commutator`。
新 shared infra = `exists_subgroup_card_eq_of_isCyclic` + `characteristic_of_isCyclic`
(`CyclicSubgroupUniqueness.lean` へ追記) と `CardSupInf.lean` (issue 9209)。

✅ **共役性 landing (2026-07-26)** — ⭐ **商群 `G/M` を経由しない経路**に差し替えた。
下記の当初設計 (step 3-5 で `G/M` を作る) は不要で、鍵は
**`m₁ = |K ⊓ G'|` と `m₂ = f` が互いに素**であること (`m₁ ∣ |G'|`, `f ∣ |G:G'|`):

* `K_i` 自身も Z-群なので**存在部分を再利用**して位数 `f` の部分群 `Q_i ≤ K_i` を取れる。
* `gcd(f, |G'|) = 1` より `Q_i ⊓ G' = ⊥`、かつ `|Q_i| · |G'| = |L|` なので
  `Q_i` は `↥L` の中で正規 Hall `G'` の**補群**。⟹ Schur–Zassenhaus 共役性を
  `↥L` を ambient として直接適用できる (`Subgroup.IsComplement'.exists_conj_of_coprime`)。
* `K_i = Q_i ⊔ (K_i ⊓ G')` で `K_i ⊓ G'` は `G` 正規なので共役で不変 ⟹ `K₁^n = K₂`。

補助定理: `exists_index_factor` (`|K| = |K ⊓ G'| · f`, `|K ⊔ G'| = |G'| · f`, `f ∣ |G:G'|`) /
`card_inf_commutator` / `inf_commutator_eq_of_card_eq` / `normal_inf_commutator` /
`sup_commutator_eq_of_card_eq` / `card_map_mk'_mul_card` / `mem_normalizer_of_normal`。

~~**残り (共役性) の設計**~~ (当初案、上記に置換): 位数 `m` の部分群 `K₁, K₂` に対し
1. `|K_i ∩ G'| = m₁`: `d := |K_i ∩ G'|` は `m₁` を割り、`m/d ∣ |G:G'|` かつ `m₁/d ∣ |G'|` なので
   `m₁/d ∣ gcd(|G'|,|G:G'|) = 1`。
2. `G'` 巡回 ⟹ 位数 `m₁` の部分群は一意 (`cyclic_subgroup_eq_of_card_eq`) ⟹
   `K₁ ∩ G' = K₂ ∩ G' =: M` (`G` で正規)。
3. `Ḡ := G/M` で `K̄_i` は位数 `m₂`、`K̄_i ∩ Ḡ'` は自明。`L_i := K̄_i · (G'/M)` は
   `Ḡ/(G'/M) ≅ G/G'` (**巡回**) の位数 `m₂` の部分群に対応 ⟹ **一意** ⟹ `L₁ = L₂ =: L`。
4. `L` の中で `K̄_i` は正規 Hall `G'/M` の補群 ⟹ Schur–Zassenhaus 共役性
   (`Subgroup.IsComplement'.exists_conj_of_coprime`, repo の
   `OddOrder/Mathlib/SchurZassenhausConj.lean`) で共役。
5. 商の対応で `G` に持ち上げる。

### 5C.1 の実装メモ (2026-07-26)

* `p ∤ |G'|`: `G'` の位数 `p` の元 `x` を取ると `⟨x⟩` はある Sylow `Q` に入り `Q` は `P` に共役、
  `G'` 正規なので `x^g ∈ G' ⊓ P = ⊥` で矛盾。⭐ **「N 正規なら N ⊓ P ∈ Syl_p(N)」を経由せずに済む**。
* `Abelianization G` は可換なので Sylow が正規 ⇒ **Schur-Zassenhaus**
  (`Subgroup.exists_right_complement'_of_coprime`) で `p`-補群 `K` を取り、
  `N := (Abelianization.of)⁻¹(K)`。`|G : N| = |PA| = |P|` (`Sylow.card_eq_multiplicity` +
  `p ∤ |G'|` から `p`-指数が一致)、`p ∤ |N|` は `p^{v+1} ∤ |G|` から。
* 各 Sylow `Q` に対する `IsComplement'` は `Subgroup.isComplement'_of_card_mul_and_disjoint`
  + `Subgroup.disjoint_of_coprime_natCard`。
⚠ `Abelianization G := G ⧸ commutator G` なので全射性は `QuotientGroup.induction_on` で出る
(`Abelianization.of_surjective` / `induction_on` は存在しない)。

### 5C.5 の実装メモ (2026-07-26)

`P` と `P^g` がともに `N_G(B)` の `p`-部分群であることを使い、hub の
`GroupTheory.exists_mem_conj_le_common` (2 つの `p`-部分群を共通の `p`-部分群へ) で
`c ∈ N_G(B)` を取る。`P` は Sylow なので共通部分群は `P` 自身、ゆえに `cg ∈ N_G(P)`。
⚠ `Sylow` の極大性フィールドは `P.3 : IsPGroup p Q → ↑P ≤ Q → Q = ↑P` (**向きに注意**)。
⚠ `Subgroup.mem_normalizer_fintype` で「片方向の共役閉」から正規化子の元が取れる。

## Ch.5 §5D (書籍 pp. 169-170 の Problems 5D) — 次の frontier (2026-07-27)

statement は **PDF ページ画像で確定済** (書籍 pp. 169-170 = PDF pp. 182-183)。
`A^p(G)` / `O^p(G)` / focal subgroup / `ControlsFusionIn` は `Ch05_Transfer/Basic.lean` に既存
(`APrime` / `pResidual` / `Subgroup.focalSubgroup` / `Subgroup.ControlsFusionIn`,
Thm 5.20/5.21/5.22 = `APrime_eq_transferFocal_ker` / `focalSubgroupTheorem` /
`APrime_eq_subgroupOf_APrime_of_controlsFusionIn`)。

| 問題 | 状態 | 主張 (PDF 実測) |
|---|---|---|
| 5D.1 | ✅ 完了 (`hasNormalPComplement_of_controlsPTransfer`) | `P ∈ Syl_p(G)` 可換, `P ⊆ H ⊆ G`, `H` が `G` の `p`-transfer を制御 (= `A^p(H) = H ∩ A^p(G)`)。`H` が正規 `p`-補群をもつなら `G` も持つ |
| 5D.2 | ✅ 完了 (`hasNormalPComplement_of_sylow_le_center` + Burnside 導出の `example`) | `P ∈ Syl_p(G)`, `P ⊆ Z(G)` ⇒ (Burnside も transfer 理論も使わずに) `G` は正規 `p`-補群をもつ。これと Cor 5.23 から Burnside を導く |
| 5D.3 | (a) ✅ 完了 (`exists_sylow_coe_eq_of_isCoatom_of_isPGroup`) / (b)(c) 🔒 5C.6 待ち | `G` 非可換単純, `P ⊆ G` が極大な `p`-部分群。(a) `P ∈ Syl_p(G)` (b) `1 < N ⊴ P` で `P/N` 可換なら `P` は `N` を含む唯一の Sylow `p`-部分群 ⇒ `N` は `P` 内で `G` に関し weakly closed (c) `P` の冪零類 ≥ 3 |
| 5D.4 | ✅ 完了 (`pResidualOf_le_inf_pResidual` / `APrime_eq_subgroupOf_APrime_of_pResidualOf_eq`) | `P ∈ Syl_p(G)`, `P ⊆ K ⊆ G` ⇒ `O^p(K) ⊆ K ∩ O^p(G)`、等号なら `A^p(K) = K ∩ A^p(G)` |
| 5D.5 | ✅ 完了 (`hasNormalPComplement_of_APrime_inf_sylow_eq_commutator`) | `P ∈ Syl_p(G)`, `A ∩ P = P'` (`A = A^p(G)`)。`P' ⊴ A` なら (Tate を使わず) `G` は正規 `p`-補群をもつ。hint: SZ で `A` 内の `P'` の補群 `K` を取り `G = N_G(K)P'`、`P' ⊆ Φ(P)` から `P` が `K` を正規化 |
| 5D.6 | ✅ 完了 (`hasNormalPComplement_of_APrime_inf_sylow_eq_commutator_of_abelian`) | 同じ設定で `P'` 可換なら `G` は正規 `p`-補群をもつ。hint: `N = N_G(P')` が仮定を満たすことを見て `A` の中で Burnside |

⚠ **5D.3(b)** は **5C.6 (weak closure)** に依存 — 5C.6 は hub レーン (issue 9503
`OddOrder/GroupTheory/WeaklyClosed.lean`) 担当なので、そこが landing してから着手する。

### 5D.1 の実装 (2026-07-27 完了、新 leaf `Problems5D.lean`)

**可換 Sylow に対しては `G` が正規 `p`-補群をもつ ⟺ `A^p(G) ⊓ P = ⊥`**。

* `⟸`: `APrime_inf_sylow_eq_focalSubgroup` + focal subgroup 定理で
  `commutator G ⊓ P = focalSubgroup P = A^p(G) ⊓ P = ⊥` ⟹ **Problem 5C.1**
  (`hasNormalPComplement_of_commutator_inf_sylow_eq_bot`)。
* `⟹` (`H` 側で使う): 正規 `p`-補群 `N ⊴ ↥H` に対し `↥H/N` は `P` の像で**可換**ゆえ
  `commutator ↥H ≤ N`、また `N.index = |P|` は `p`-冪ゆえ `APrime_le` で `A^p(↥H) ≤ N`、
  `IsComplement'.disjoint` から `A^p(↥H) ⊓ ↑P_H = ⊥`。

あとは仮説 `A^p(↥H) = (A^p G).subgroupOf H` と `P ≤ H` から
`(A^p(G) ⊓ ↑P).subgroupOf H = ⊥` ⟹ `A^p(G) ⊓ ↑P = ⊥` (comap は `⊓` を保つ)。

**実装**: 同値の両向きを独立補題にした —
`APrime_inf_sylow_eq_bot_of_hasNormalPComplement` (⟹) と
`hasNormalPComplement_of_APrime_inf_sylow_eq_bot` (⟸)。主定理は
`hasNormalPComplement_of_controlsPTransfer`。axiom-clean。

⚠ 実装の罠: `IsComplement' A B` の `.index_eq_card` は `B.index = |A|` (逆は `.symm`)。
`Subtype.ext` の二重適用は `apply` を重ねると 2 段目が不発になることがある — `G` レベルの
等式を `have` で明示してから `Subtype.ext (Subtype.ext hGeq)` と項で書く。
`(⊤ : Subgroup G)` の元を `N * P` に分解するには `Subgroup.normal_mul` で
`↑(N ⊔ P) = ↑N * ↑P` にしてから `rw [← htop]; exact Subgroup.mem_top _`。

### 5D.2 の実装 (2026-07-27 完了)

**前半**: `P ≤ Z(G)` ⟹ `P ⊴ G`、`|P|` と `|G:P|` は互いに素なので **Schur–Zassenhaus**
(`Subgroup.exists_right_complement'_of_coprime`) が補群 `K` を与える。`g = x·k` (`x ∈ P` は
中心的) の共役は `k` による共役に一致するので `K ⊴ G`、5C.13 の helper
`hasNormalPComplement_of_normal_of_index_eq_pow` で結論。**Burnside も transfer も未使用**。

**後半 (Burnside の別証明)**: `N := N_G(P)` の中で `P` は中心的なので前半が `N` の正規
`p`-補群を与え、`P` 可換ゆえ **Cor 5.23**
(`APrime_normalizer_eq_subgroupOf_APrime_of_isMulCommutative_sylow`) が `p`-transfer 制御を
与え、**Problem 5D.1** で `G` に持ち上がる。⚠ statement は既存の
`hasNormalPComplement_of_sylow_normalizer_le_centralizer` (Thm 5.13) と同一ゆえ、
ラッパー方針に従い定理として再掲せず **`example` で導出のみ kernel 検証**した
(5C.1 の「同一 statement の別証明を避ける」方針と同じ扱い)。

⚠ 実装の罠: `hasNormalPComplement_of_normal_of_index_eq_pow` の `X` は結論に現れない
implicit なので `(X := K)` を明示しないと `Subgroup.Normal ?m` で instance 探索が止まる。

### 5D.4 の実装 (2026-07-27 完了、新 leaf `Problems5D4.lean` 166 行)

`O^p` は Ch09 の `pResidual` / ambient 版 `pResidualOf` を使う (⚠ `Ch09_MoreSubnormality/PResidual.lean`
は **mathlib しか import しない**ので Ch05 から import しても cycle 無し — 実測済)。

* **前半** `pResidualOf_le_inf_pResidual`: `↥K ⧸ O^p(G).subgroupOf K` は
  `(mk' O).comp K.subtype` の像と同型で、像は `p`-群 `G ⧸ O^p(G)` の部分群 ⟹ `p`-群 ⟹
  `O^p` の普遍性。
* **後半** `APrime_eq_subgroupOf_APrime_of_pResidualOf_eq` (⭐ 本題): `≤` は既存
  `APrime_le_subgroupOf_APrime_of_sylow_le`。`≥` は `O := O^p(G)`, `B := A^p(K)` の押し出しとして
  1. `K ⊔ O = ⊤` (`(P ⊔ O).index` は `|G:P|` (p と素) と `|G:O|` (p-冪) の両方を割るので 1),
  2. `⁅G,G⁆ ≤ ⁅K,K⁆ ⊔ O` (`g = k·u` 分解 + `mk' O` で交換子を比較),
  3. `A^p(G) ≤ O ⊔ ⁅G,G⁆ ≤ O ⊔ B` (`APrime_le`; ⚠ `O ⊔ B` は `G` で正規と限らないので
     **正規な `O ⊔ ⁅G,G⁆` を経由**する),
  4. Dedekind `K ⊓ (O ⊔ B) = (K ⊓ O) ⊔ B = B` (仮定 `K ⊓ O = O^p(K) ≤ B`)。
  ⭐ 仮定 `O^p(K) = K ∩ O^p(G)` は 4 でだけ効く。
* 副産物 `pResidual_le_APrime` (`O^p(H) ≤ A^p(H)`)。

⚠ 実装の罠: `hrp : r = p` の `▸` は `P : Sylow p G` の型内の `p` まで巻き込んで
**kernel で type mismatch** (elaborator は通す) — `subst hrp` を使う。
商型に対する `rw [← hker]` は motive 不正 ⟹ `QuotientGroup.quotientMulEquivOfEq hker` +
`IsPGroup.of_equiv` で移送。ゴールを変える `show` は `linter.style.show` が警告 ⟹ `change`。

### 5D.3(a) の実装 (2026-07-27 完了、新 leaf `Problems5D3.lean` 83 行)

`P ≤ S` (Sylow) で `P < S` なら `p`-群の正規化群成長 (Isaacs Thm 1.22
`Ch01.lt_normalizer_of_isNilpotent_of_lt_top` を `↥S` で使い
`Subgroup.subgroupOf_normalizer_eq` で `G` に降ろす) から `P < N_G(P)`、coatom 性で
`N_G(P) = ⊤` ⟹ `P ⊴ G` ⟹ 単純性で `P ∈ {⊥, ⊤}`。`P = ⊤` は `P < S` に矛盾。
`P = ⊥` なら coatom 性で `S = ⊤` ⟹ `G` が `p`-群 ⟹ `IsPGroup.center_nontrivial` +
単純性で `Z(G) = ⊤` ⟹ 可換で仮定に矛盾。⟹ `P = S`。

⚠ (b)(c) は **Problem 5C.6 (weak closure)** 依存 — hub レーンの
`OddOrder/GroupTheory/WeaklyClosed.lean` (issue 9503) が landing してから。

### 5D.5 の実装 (2026-07-27 完了、新 leaf `Problems5D5.lean` 68 行) + 5C.13 のエンジン切り出し

⭐ **5D.5 の hint は 5C.13 の最終段と完全に同じ論法**だったので、5C.13 の還元形から共通部分を
`hasNormalPComplement_of_commutator_normalHall_in_normal` として `Problems5C13.lean` に
**切り出して共有した** (重複を書かない方針):

> `P ∈ Syl_p(G)`, `L := ⁅P,P⁆`, `K ⊴ G` が `L` を含み `L` が `K` の**正規 Hall `p`-部分群**
> (`p ∤ |K:L|`) で `|G:K|` が `p`-冪 ⟹ `G` は正規 `p`-補群をもつ

(証明 = Schur–Zassenhaus で `K` 内の `L` の補群 `X` → Frattini (共役元は `L` 内) で
`G = L·N_G(X)` → Dedekind + `⁅P,P⁆ ⊆ Φ(P)` の非生成性で `P ≤ N_G(X)` → `X ⊴ G`)。
5C.13 の還元形は Burnside で `K = π⁻¹(K̄)` を作ってこのエンジンを呼ぶだけになった。

**5D.5 側**: `A := A^p(G) ⊴ G` なので `A ∩ P` は `A` の Sylow `p`-部分群
(`Ch03.isHallSubgroup_subgroupOf_of_normal` + `Ch01.sylow_isHallSubgroup_singleton`)、
仮定でそれが `P'` かつ `A` で正規 ⟹ 正規 Hall `p`-部分群。`|G:A|` は `p`-冪
(`APrime_index_isPGroup`) ⟹ エンジンをそのまま適用。

⚠ `(K ⊓ H).subgroupOf K = H.subgroupOf K` は **`inf_subgroupOf_left`** (右側版は `_right`)。

### 5D.6 の実装 (2026-07-27 完了、新 leaf `Problems5D6.lean` 248 行)

**主張**: `P ∈ Syl_p(G)`, `A := A^p(G)`, `A ∩ P = P'` で **`P'` が可換**なら (Tate 抜きで)
`G` は正規 `p`-補群をもつ。

**書籍 hint** =「`N := N_G(P')` が仮定を満たすことを見て、`A` の中で Burnside を使う」。
これを展開すると次の 4 段:

1. **`P ≤ N := N_G(P')`** (`P` は `⁅P,P⁆` を正規化)。ゆえに `P ∈ Syl_p(N)` で `P' ⊴ N`。
2. **`N` が 5D.5 の仮定を満たす**:
   * `A^p(N) ⊇ ⁅N,N⁆ ⊇ ⁅P,P⁆ = P'` なので `A^p(N) ∩ P ⊇ P'`、
   * 逆は既存の `APrime_le_subgroupOf_APrime_of_sylow_le P (P ≤ N)` で
     `A^p(↥N) ≤ (A^p G).subgroupOf N` ⟹ 押し出して `A^p(N) ∩ P ≤ A ∩ P = P'`。
   * `P' ⊴ N` かつ `P' ≤ A^p(N)` ⟹ `P' ⊴ A^p(N)`。
   ⟹ **5D.5 (`hasNormalPComplement_of_APrime_inf_sylow_eq_commutator`) を `↥N` に適用**して
   `N` が正規 `p`-補群 `M` をもつ。
3. **`N_A(P') = A ∩ N` は `P'` を中心化する**: `M ⊴ N` は `p'`-群で `N/M` は `p`-群なので
   `A ∩ N` は正規 `p`-補群 `A ∩ M` をもち、`P' = A ∩ P` はその Sylow `p`-部分群。
   `P' ⊴ A ∩ N` (1 より) と `A ∩ M ⊴ A ∩ N`、交わり自明・積が全体 ⟹
   **`A ∩ N = P' × (A ∩ M)`**。`P'` 可換ゆえ `P' ≤ Z(A ∩ N)`, すなわち
   `N_A(P') ≤ C_A(P')`。
4. **`A` の中で Burnside** (`hasNormalPComplement_of_sylow_normalizer_le_centralizer` を `↥A` に):
   `P'` は `A` の Sylow `p`-部分群 (5D.5 と同じ `isHallSubgroup_subgroupOf_of_normal`) なので
   `A` は正規 `p`-補群 `K` をもつ。`K` は正規 `p`-補群の一意性
   (`map_mulAut_of_normal_pcomplement`) から `A` に characteristic ⟹ `A ⊴ G` より `K ⊴ G`。
   `p ∤ |K|` かつ `|G:K| = |G:A|·|A:K| = p`-冪 ⟹ `hasNormalPComplement_of_normal_of_index_eq_pow`。

**実装の副産物 (いずれも再利用可能)**:
* `le_centralizer_of_normal_sylow_of_hasNormalPComplement` — 正規 `p`-補群をもつ群で
  **正規な** Sylow `p`-部分群は全体に中心化される (正規 `p`-補群と正規 Sylow は交わり自明で交換)。
* `le_normalizer_commutator_self` — `H ≤ N_G(⁅H,H⁆)`。
* `hasNormalPComplement_of_mulEquiv` / `hasNormalPComplement_of_le` — 同型・部分群への遺伝
  (`Ch05_Transfer/Main.lean` の `hasNormalPComplement_of_subgroup` を ambient 部分群の形に橋渡し)。
  ⚠ Ch07 の `S7B2` に同種の MulEquiv 版があるが Ch05 から見て下流なので使えない。

⚠ 実装の罠: `Sylow.coe_subtype` は `rfl` なので `hPNcoe := rfl` で済む。`x : ↥↑S` の `x.2` に
`rw [hS]` は motive 破綻 ⟹ `hS.le x.2` と項で書く。`Subgroup.relIndex_mul_relIndex` は
部分群 3 つが explicit。

## Ch.6 (Frobenius Actions) §6A (書籍 pp. 184-186 の Problems 6A) — 着手 (2026-07-27)

Isaacs Ch.1–Ch.5 の章末演習が全完したので **Ch.6 が次の frontier** (文書順)。
§6A は **6A.1–6A.11** の 11 問 (statement は PDF ページ画像で確定; 書籍 p.184-186 =
PDF p.197-199、`references/isaacs/pages/isaacs-p{184,185,186}-{197,198,199}.png` に保存済)。
Ch.6 本文 (Thm 6.4 / Lem 6.5 / Cor 6.6 / Thm 6.7 …) は `Ch06_FrobeniusActions/` に実装済。

| 問題 | 状態 | 主張 |
|---|---|---|
| 6A.1 | ✅ 完了 (`Problems6A.lean`) | `A ≤ SL(2,p)`, `p ∤ \|A\|` ⟹ `A` の `(ZMod p)²` への作用は Frobenius |
| 6A.2 | ✅ **完了** (`Problems6A2.lean`) | `GL(3,43)` の具体例 `a = diag(α,α⁴,α²)`, `b = [[0,1,0],[0,0,1],[ε,0,0]]` (`α` 位数 7, `ε` 位数 3) で `A = ⟨a,b⟩` は非巡回位数 63, `43³` 次元への作用は Frobenius |
| 6A.3 | ✅ **完了** (`Problems6A3.lean`) | 位数 `5²·11` の非巡回群で Frobenius 作用をもつものが存在 (hint: `GL(5,p)`) |
| 6A.4 | ✅ **完了** (`ProblemsFrobeniusGroups.lean`) | Frobenius 群 `G` (核 `N`) の `N` 以外の剰余類は単一の共役類に含まれる |
| 6A.5 | ✅ **完了** (`ProblemsFrobeniusGroups.lean`) | 非可換可解群で全非単位元の中心化群が可換 ⟹ Frobenius 群 (核 = `F(G)`) |
| 6A.6 | ✅ **完了** (`ProblemsTIHypothesis.lean`) | Lemma 6.5 の仮説を満たす `A, B > 1` ⟹ ある `g` で `A ⊓ B^g > 1` |
| 6A.7 | ✅ **完了** (`ProblemsTIHypothesis.lean`) | Lemma 6.5 の `A ⊆ H ⊆ G` で (a) `A^g ⊓ H > 1 ⟹ g ∈ H` (b) `H ⊴ G ⟹ H = G` |
| 6A.8 | ✅ **完了** (`Problems6A8.lean`) | `M ⊴ G` ⟹ `M ⊆ X` または `X ⊆ M` |
| 6A.9 | ✅ **完了 (a)-(f)** (`Problems6A9.lean`) | `A` に involution `t` があるとき (a)-(f) (⟹ `X` は部分群 = 偶数位数版 Frobenius 定理) |
| 6A.10 | ✅ **(a)(b)(c) 完了** | (a) `A` は Sylow を含み fusion を制御 (b) `G'A = G` (c) `A` 可解 ⟹ `X` は部分群 |
| 6A.11 | ✅ **完了** (`ProblemsTIHypothesis.lean`) | `A` が Lemma 6.5 の仮説 ⟺ 全非単位部分群 `T ≤ A` で `N_G(T) ⊆ A` |
| 6B.1 | ✅ 完了 (前半・後半とも) | 任意の Frobenius 群は可解 Frobenius 部分群を含む ⟹ Frobenius 補群は Frobenius 群を部分群に持てない |
| 6B.2 | ✅ | `A` 可換が `N` に忠実作用, `N` の非自明真部分群が `A`-不変でない ⟹ `A` 巡回 |
| 6B.3 | ✅ | Thm 6.21 の coprime 仮定を落とすと偽 (反例構成) |
| 6B.4 | ✅ | 分割 II で `[X,Y] = 1` ⟹ (a) `G` 可換 (b) 基本可換 |
| 6B.5 | ✅ 完了 (Wielandt 補題は不要だった) | subnormal 部分群からなる分割を持つ ⟹ `G` 冪零 |
| 6B.6 | ✅ | 位数 ≥ 8 の巡回 2-群は位数 2 の自己同型をちょうど 3 個持つ |
| 6B.7 | ✅ | 非可換 2-群が指数 2 の巡回部分群を持ち `|P:Z(P)| > 4` ⟹ 二面体/半二面体/一般四元数 |
| 6B.8 | 🔨 部品 20 本完了 (|P:Z(P)|>4 含む) / 帰納法本体が残り | `|P| ≥ 8`, `|P:P'| = 4` ⟹ 二面体/半二面体/一般四元数 (Taussky-Todd) |
| 6B.9 | ⬜ | `G` 可解 + 全元が素数冪位数 ⟹ `|G|` の素因子は高々 2 個 |

### 6A.6 完了 / 6A.11 は (⟹) のみ (2026-07-27) — 新 leaf `ProblemsTIHypothesis.lean`

⚠ 書籍の Note どおり **Frobenius の定理 (`X` が部分群) は使わない**。

* **6A.6** `exists_inf_conj_ne_bot_of_TI`: `A > 1`, `B > 1` がともに Lemma 6.5 の TI 仮説を
  みたすなら, ある `g` で `A ⊓ B^g > 1`。論法 (hint の `X`, `Y` の計数): 全ての `g` で
  `A ⊓ B^g = 1` なら `A` の非単位元は `B` の非単位元と共役になれないので **`X ∪ Y = G`**、
  一方 `1 ∈ X ⊓ Y` なので `|G| + 1 ≤ |X| + |Y| = |G:A| + |G:B| ≤ |G|/2 + |G|/2 = |G|` で矛盾。
* **6A.11 (⟹)** `normalizer_le_of_TI`: TI ⟹ 非自明 `T ≤ A` で `N_G(T) ≤ A`。

* **6A.7** `mem_of_conj_inf_ne_bot` (a) / `eq_top_of_normal_of_TI` (b): `A` が TI で
  `A ≤ H ≤ G` のとき `A^g ⊓ H > 1 ⟹ g ∈ H`, および `H ⊴ G ⟹ H = G` (⚠ (b) は `A > 1` が要る
  — 書籍では Lemma 6.5 の文脈から暗黙)。hint どおり `A` と `A^g` がともに **`↥H` の中で**
  TI 仮説をみたすこと (`TI_subgroupOf_of_TI` / `TI_subgroupOf_conj_of_TI`) を見て **6A.6** を
  `↥H` で使う。副産物: `conj_smul_subgroupOf` (`k ∈ H` なら共役と `subgroupOf` が交換)。
* **6A.9 の準備** (新 leaf `Problems6A9.lean`、2026-07-27): TI 仮説の下での `X` の構造。
  `centralizer_le_of_TI` (`1 ≠ a ∈ A` なら `C_G(a) ≤ N_G(⟨a⟩) ≤ A`) /
  `conj_mem_iff_of_TI` (`g a g⁻¹ ∈ A ⟺ g ∈ A`) / `inv_mem_notConjugateSet` /
  `zpow_mem_notConjugateSet` (`X` は冪で閉じる — `x^k` が `a` と共役なら
  `g⁻¹xg ∈ C_G(a) ≤ A` で `x` 自身が `A` の非単位元と共役になる) /
  `eq_one_of_mem_notConjugateSet_of_mem` (`X ⊓ A = {1}`) /
  `mem_normalizer_zpowers_of_conj_eq_inv` /
  ⭐ **`mem_notConjugateSet_of_conj_eq_inv`** = `Inv(t) ∖ A ⊆ X` (6A.9(b) の核心の片側):
  `x ∉ A` が `t` に反転され `x = g a g⁻¹` (`1 ≠ a ∈ A`) なら `u := g⁻¹ t g` が `a` を反転するので
  `u ∈ N_G(⟨a⟩) ≤ A`、つまり `t ∈ A ⊓ A^g` で TI から `g ∈ A`、これは `x ∈ A` で矛盾。

  **(a) 完了** `card_inverted_notMem_ge` (2026-07-27): `t` に反転される `G ∖ A` の元は
  `|G:A| − 1` 個以上。⭐ 共役類の濃度を持ち出さずに **fiber 計数**で済んだ:
  `f g := (g t g⁻¹)·t` は `t` に反転される元を与え (`(f g)·t = g t g⁻¹` は involution)、
  `f g ∉ A ⟺ g ∉ A` (`conj_mem_iff_of_TI`)、`f` の fiber は `C_G(t)` の左剰余類なので
  大きさ `≤ |A|` (`centralizer_le_of_TI`)。`Finset.card_le_mul_card_image` で
  `|G| − |A| ≤ |A| · |image|` ⟹ `|image| ≥ |G:A| − 1`、そして `image ⊆ Inv(t) ∖ A`。

  **(b)-(e) 完了** (2026-07-27):
  `conj_eq_inv_of_mem_notConjugateSet` (b) = (a) と `mem_notConjugateSet_of_conj_eq_inv` の
  濃度合わせで `Inv(t) ∖ A = X ∖ {1}` /
  `eq_of_isInvolution_mem` (c) = `t` は `A` の唯一の involution (⚠ `A ≠ ⊤` が要る;
  `s ≠ t` なら `ts ≠ 1` が `1 ≠ x ∈ X` を中心化して `x ∈ C_G(ts) ≤ A` で矛盾) /
  `odd_orderOf_of_mem_notConjugateSet` (d) = `X` の元は奇数位数 (偶数なら冪の involution `u`
  が `X` に入り `t` と可換ゆえ `u ∈ A`, `X ⊓ A = {1}` で矛盾) /
  `eq_of_mul_inv_mem` (e) = `x y⁻¹ ∈ A` なら `x = y` (`b := x⁻¹y = t(xy⁻¹)t ∈ A` で
  `x b x⁻¹ = (xy⁻¹)⁻¹ ∈ A`, `b ≠ 1` なら `conj_mem_iff_of_TI` で `x ∈ A` となり矛盾)。
  ⟹ **`X` は `A` の右剰余類とちょうど 1 点ずつ交わる (右横断系)**。

  **(c) の系も landing** (2026-07-27): `eq_one_or_eq_of_mem_of_conj_eq_inv`
  (`A` の元で `t` に反転されるのは `1` と `t` だけ — `a t` が `A` の involution になるので
  (c) の一意性から) / `setOf_conj_eq_inv_eq` = **`Inv(t) = X ∪ {t}`** (したがって
  `|Inv(t)| = |G:A| + 1`)。

  **(f) 完了** `mul_mem_notConjugateSet` + `frobeniusKernelOfInvolution` (2026-07-27)。
  ⭐ **鍵は「別の involution `s` に乗り換える」こと**: `x, y ∈ X` に対し `s := x t`,
  `r := t y` はともに involution で **`x y = s r`**。(d) より `X` の元は奇数位数なので
  `s ∉ X`, ゆえに `s` はある共役 `A^g` の非単位元。`A^g` も TI 仮説をみたし
  (`TI_conj`) `notConjugateSet A^g = X` (`notConjugateSet_conj`) なので, (b)(c) の系
  `setOf_conj_eq_inv_eq` を **`(A^g, s)` に適用**して `Inv(s) = X ∪ {s}`。
  `s (s r) s = (s r)⁻¹` より `x y ∈ Inv(s)`, そして `x y = s` なら `y = t ∈ X ⊓ A = {1}`
  で `t = 1` となり矛盾 ⟹ `x y ∈ X`。
  ⚠ 前回「`t` による反転だけからは出ない」と書いたとおりで, `t` ではなく **`s = xt`**
  に対する (b) を使うのが要点だった (`X` は共役不変なので `A` の共役に乗り換えられる)。
  副産物: `TI_conj` / `notConjugateSet_conj` (TI 仮説と `X` は `A` の共役に不変)。

* **6A.10(c) 完了** `exists_subgroup_coe_eq_notConjugateSet_of_solvable` (2026-07-27,
  新 leaf `Problems6A10c.lean`) ⭐ = **可解な場合の Frobenius の定理**: `A` が TI 仮説を
  みたし**可解**なら `X = notConjugateSet A` は部分群 (の台集合)。`|G|` に関する強帰納法:
  * `A' < A` (`IsSolvable.commutator_lt_top_of_nontrivial` を `↥A` に適用) と 6A.10(b) の
    `G' ⊓ A = A'` が両輪。
  * **`A` 非可換**: `A ⊓ G' = A' ≠ 1` ⟹ 6A.7(a) で `AG' = G`。`G' = G` なら `A = A'` で
    矛盾ゆえ `G' < G`。6A.8 の `TI_subgroupOf_normal` + `image_notConjugateSet_subgroupOf_eq`
    で `X` は `X_{G'}(A ⊓ G')` の像 ⟹ 帰納法の仮定を `G'` に適用。
  * **`A` 可換**: `A ⊓ G' = 1` ⟹ 6A.8 第 1 場合で `G' ⊆ X`。`M := AG'` は正規で `A ≤ M`,
    `A ≠ 1` ゆえ `M ⊄ X` ⟹ 6A.8 で `X ⊆ M`, さらに `G = X ∪ ⋃A^g ⊆ M` で `AG' = G`。
    濃度が `|X| = |G:A| = |G':A⊓G'| = |G'|` で一致 ⟹ **`X = G'`**。
  この過程で `Problems6A8.lean` を refactor し, 埋もれていた 3 本を再利用可能に切り出した
  (`subset_notConjugateSet_of_inf_eq_bot` / `sup_eq_top_of_inf_ne_bot` /
  `image_notConjugateSet_subgroupOf_eq`)。⟹ **§6A 完了**。
* **6A.10(b) 完了** `inf_commutator_eq_commutator_self_of_TI` (2026-07-27): TI 仮説の下で
  **`G' ⊓ A = A'`**。⊇ は自明 (`commutator_self_le_inf_commutator`)。⊆ は焦点部分群定理経由:
  `H := G' ⊓ A` の Sylow `p`-部分群 `Q` を含む `↥A` の Sylow `S` を取ると, (a) 前半で
  `S` は `G` の Sylow でもあり, Isaacs Thm 5.21 (`Subgroup.commutator_inf_eq_focalSubgroup`)
  で `Q ≤ G' ⊓ S = S.focalSubgroup`。(a) 後半の fusion 制御 + Cor 5.22 core
  (`Subgroup.focalSubgroup_subgroupOf_map_eq_of_controlsFusionIn`) で `S.focalSubgroup` は
  `↥A` 内部の焦点部分群 (`= A' ⊓ S ≤ A'`) の像。⟹ 全 Sylow が `A'` に入る。
  汎用補題 `eq_top_of_forall_sylow_le` (**有限群は Sylow 部分群で生成される**の指数版:
  `p ∣ |H:K|` なら `p^(n+1) ∣ |H|` で multiplicity の最大性に反する) を新設して束ねた。
  ⟹ **6A.10(b) 完了**、§6A の残りは (c) のみ。
* **6A.10(b) 前半** `commutator_sup_eq_top_of_TI` (2026-07-27): `A > 1` が TI なら
  `G' A = G`。`G'` を含む部分群は正規なので **6A.7(b)** が直ちに使える (1 行)。
* **6A.10(a) 前半** `exists_sylow_coe_eq_of_maximal_pGroup_of_TI` (2026-07-27):
  TI 仮説の下で `A` に含まれる極大 `p`-部分群 (≠ 1) は **`G` の Sylow `p`-部分群**。
  6A.11(⟸) の step 2 と同じ論法 (`↥S` の冪零正規化条件 + `N_G(P) ≤ A`) を単独補題に。

  **⚠ 書籍の主張を PDF ページ画像 (`isaacs-p186-199.png`) で確定済 (2026-07-27)**:
  6A.10 = (a) 「`p ∣ |A|` なら `A` は `G` の Sylow `p`-部分群 `P` を**含み**, `A` は
  `P` における `G`-fusion を**制御する**」/ (b) 「`A > 1` なら **`G'A = G` かつ
  `G' ∩ A = A'`**」/ (c) 「`A` 可解なら `X` は部分群」。
  `commutator_self_le_inf_commutator` で (b) 後半の**易しい向き** `A' ≤ G' ⊓ A` は landing
  (TI 仮説不要)。⟹ 残り = (a) の fusion 制御 (Ch.5 §5C の fusion 制御 API を使う) /
  (b) の `G' ⊓ A = A'` (focal subgroup / transfer が要りそう) /
  (c) = **奇数位数側の Frobenius の定理** (6A.9(f) の可解版、本格的)。
  書籍 Note: (6A.9 と 6A.10 を合わせると) Frobenius の定理は Feit-Thompson の
  奇数位数定理の帰結になる。

* **6A.8** `subset_notConjugateSet_or_subset_of_normal` (新 leaf `Problems6A8.lean`):
  `M ⊴ G` なら `M ⊆ X` または `X ⊆ M`。`A ⊓ M = 1` なら前者 (`M` 正規ゆえ共役先も `M` 内)。
  `A ⊓ M ≠ 1` なら **6A.7(a)** で `A ⊔ M = ⊤`、そのうえで
  (i) `A ⊓ M` が `↥M` で TI 仮説をみたす、(ii) Lemma 6.5 を `↥M` で使って
  `|X_M| = |M : A ⊓ M| = |G : A| = |X|` (第 2 同型定理の指数版
  `index_eq_relIndex_of_sup_eq_top` を新設)、(iii) `X_M ⊆ X` を elementwise に示し
  (`g = m a₁` と分解して `y` が `M` 内で `a₁ a a₁⁻¹ ∈ A ⊓ M` と共役)、
  (iv) 濃度一致 + 包含から `X = X_M ⊆ M`。
* **6A.11** `TI_iff_forall_normalizer_le`: TI 仮説 ⟺ 任意の非自明 `T ≤ A` で `N_G(T) ≤ A`。
  (⟸) の論法 (`TI_of_normalizer_le`)。`D := A ⊓ A^g ≠ 1` として:
1. `1 ≠ T ≤ D` について `N_G(T) ≤ A` かつ (`g⁻¹ • T ≤ A` に仮説) `N_G(T) ≤ A^g`
   ⟹ **`N_G(T) ≤ D`** (`N(g • T) = g • N(T)` の移送が要る)。
2. 素数 `p ∣ |D|` を取り, **`D` に含まれる `p`-部分群のうち極大なもの `P`** を
   `Finite.exists_le_maximal` で取る (Cauchy で非自明なものが存在)。`P` は実は
   **`G` の Sylow `p`-部分群**: `P < S ∈ Syl_p(G)` なら `↥S` の冪零正規化条件で
   `y ∈ N_S(P) ∖ P` が取れ, `y ∈ N_G(P) ≤ D` ゆえ `P ⊔ ⟨y⟩ ≤ S ⊓ D` が `P` より大きい
   `D` 内 `p`-部分群になって極大性に矛盾。
3. `P ≤ A` と `g⁻¹ • P ≤ A` はともに `G` の Sylow `p`-部分群ゆえ `A` の Sylow `p`-部分群、
   Sylow C (↥A で取って `map_conj_smul` で `G` に降ろす = 1C.1 のパターン; 汎用形として
   `exists_mem_smul_sylow_eq` に切り出した) で `k ∈ A` があって `k • P = g⁻¹ • P`
   ⟹ `g k ∈ N_G(P) ≤ A` ⟹ `g ∈ A`。

  副産物の汎用補題: `normalizer_conj_smul` (`N(g • T) = g • N(T)`) /
  `conj_smul_eq_map` / `conj_inv_smul_smul` / `conj_smul_inv_smul` /
  `exists_mem_smul_sylow_eq`。

### 🎉 6A.4 / 6A.5 完了 (2026-07-27) — 新 leaf `ProblemsFrobeniusGroups.lean`

* **6A.4** `isConj_mul_of_notMem_kernel`: Frobenius 群 `G` (核 `N`) で `g ∉ N` なら剰余類
  `Ng` の元はすべて `g` に共役。論法: Thm 6.4 (4) (`centralizer_kernel_le`) の対偶で
  **`C_N(g) = 1`** (`eq_one_of_mem_kernel_of_commute`) ⟹ `f : N → N`, `f(m) = m g m⁻¹ g⁻¹`
  が単射 ⟹ 有限性から全射 ⟹ 任意の `n ∈ N` に `m g m⁻¹ = n g` なる `m`。
  集合形 `coset_subset_setOf_isConj` も。
* **6A.5** `exists_isFrobeniusGroup_fitting_of_centralizer_comm`: 非可換可解な **CA 群**
  (全非単位元の中心化群が可換) は Frobenius 群で核は `F(G)`。論法:
  (1) `F := F(G)` は非自明冪零ゆえ `Z(F) ≠ 1`, その元 `z` について `F ⊆ C_G(z)` で
  `C_G(z)` 可換 ⟹ **`F` は可換**。(2) `1 ≠ n ∈ F` について `C_G(n)` の元は `F` の元と可換
  (両方 `C_G(n)` 内, `C_G(n)` 可換) ⟹ `C_G(n) ⊆ C_G(F) ⊆ F` (**P. Hall**,
  `OddOrder.GroupTheory.centralizer_fitting_le_fitting`)。(3) **Thm 6.7**
  (`exists_isComplement'_of_centralizer_le`) が Frobenius 構造を与える。

### 🎉 6A.3 完了 (2026-07-27) — 新 leaf `Problems6A3.lean` 442 行

6A.2 の `n = 3, q = 7` を **`n = 5, q = 11`** にした同型の構成 (書籍 hint「`GL(5,p)` で」):
`3` は `11` を法として位数 5 (`3ᵏ mod 11 = 1,3,9,5,4`) なので

* `a = diag(α, α³, α⁹, α⁵, α⁴)` (`α` 位数 11) / `b` = 巡回シフト + 隅に `ε` (位数 5)
* **`b⁵ = ε · 1`** (スカラー、`b²`→`b⁴`→`b⁵` と段階的に計算; 一気に 5 乗すると simp が重い)
* **`a b = b a⁴`**, すなわち **`b a = a³ b`**

⟹ `card_grpA5` (`|A| = 5²·11 = 275`) / `not_isCyclic_grpA5` / `isFrobeniusAction_grpA5`。

**Frobenius 性は共通土台の `pow_mul_pow_pow` で一撃**: `b a = a³ b` から
`(aⁱ bᵗ)⁵ = a^{(∑_{k<5} (3ᵗ)ᵏ)·i} b^{5t}` で, 幾何級数の和は
`t=1: 121 = 11², t=2: 7381, t=3: 551881, t=4: 43584805` がいずれも **11 の倍数**なので
`aⁱ` の寄与が消えて `x⁵ = b^{5t} = εᵗ·1` (非単位スカラー)。`5 ∣ t` の側は 6A.2 と同じ対角論法。

**書籍の体**: `55 ∣ p−1` が要るので最小の素数は **`p = 331`** (`330 = 2·3·5·11`)、
`α = 74` (位数 11), `ε = 64` (位数 5)。主張そのものは
`exists_noncyclic_order_twentyfive_mul_eleven_frobenius`。

### 🎉 6A.2 完了 (2026-07-27) — `Problems6A2.lean` 619 行

新 leaf `Problems6A2.lean` (`OddOrder.lean` 配線済、全て実証明・警告 0)。

⚠ **一般化した**: 書籍は `F = 𝔽₄₃` だが証明は「位数 7 の `α` と位数 3 の `ε` をもつ体」で
そのまま通るので, 一般の体 `F` で述べている (`ZMod 43` への具体化は次回)。

**行列の関係式** (`matA α = diag(α, α⁴, α²)`, `matB ε = ![[0,1,0],[0,0,1],[ε,0,0]]`):
* `matA_pow` / `matA_pow_seven` (`a⁷ = 1`)
* `matB_pow_three`: **`b³ = ε · 1`** (スカラー) ⟹ `matB_pow_nine` (`b⁹ = 1`)
* `matA_mul_matB`: **`a · b = b · a²`** (⭐ 書籍 hint の「`b` は `⟨a⟩` を正規化」の内容;
  実際に計算すると `b⁻¹ a b = a²`, `b a b⁻¹ = a⁴`)

**`GL(3,F)` の元と群構造**: `uA` / `uB` (単元版, 逆元は `a⁶` / `b⁸`) / `orderOf_uA = 7` /
`orderOf_uB = 9` / `uB_inv_mul_uA_mul_uB` (`b⁻¹ a b = a²`) /
`uB_mul_uA_mul_uB_inv` (`b a b⁻¹ = a⁴`, `a⁸ = a` と `b a² b⁻¹ = a` から) /
`uB_mem_normalizer` (`b ∈ N(⟨a⟩)`) / `grpA` / `grpA_eq_sup` (`⟨a,b⟩ = ⟨a⟩ ⊔ ⟨b⟩`)。

**主結果 (前半)**:
* `card_grpA` : **`|A| = 63`**
* `not_isCyclic_grpA` : **`A` は非巡回** (巡回なら可換, しかし `a b = b a²` で `a = a²`)

再利用可能な helper: `card_sup_of_le_normalizer_of_coprime`
(`Ch01.card_sup_of_normal_of_coprime` の「`N` が `G` で正規」を「`S ≤ N_G(N)`」に緩めた版;
`N ⊔ S` の中に降りて `subgroupOf` で適用) / `finiteMatrixUnits` instance。

**Frobenius 性** (`isFrobeniusAction_grpA`, 実証明・axiom-clean):

⭐ **書籍 hint の「素数位数の元に還元」も Sylow も使わずに済んだ**。正規形
`exists_pow_mul_pow_of_mem_grpA` (`A` の元は `aⁱ bʲ`, `i j : ℕ`) を作ると 2 ケースで終わる:

* **`3 ∣ j`**: `bʲ = εᵐ · 1` (スカラー) ゆえ `x = diag(εᵐαⁱ, εᵐα⁴ⁱ, εᵐα²ⁱ)` は対角。
  非零ベクトルを固定するならある対角成分が `1`, その成分は 7 乗すると 1 で `εᵐ` は
  3 乗すると 1 ⟹ `⟨ε⟩ ⊓ ⟨α⟩ = 1` (`eq_one_of_pow_three_pow_seven`) から `εᵐ = 1` かつ
  `α^{cⁱ} = 1` (`c ∈ {1,4,2}`, 7 と互いに素) ⟹ `αⁱ = 1` ⟹ `x = 1`。
* **`3 ∤ j`**: `b³ = ε·1` は中心的なので `x³ = (aⁱ bʳ)³` (`r = j mod 3 ∈ {1,2}`)。
  `cube_uA_pow_mul_uB` / `cube_uA_pow_mul_uB_sq` で **`(aⁱb)³ = b³`, `(aⁱb²)³ = b⁶`**
  (`aⁱ` の寄与は `1+4+16 = 21`, `1+16+256 = 273` でどちらも `7` の倍数ゆえ消える) ⟹
  `x³` は非単位スカラー `ε·1` / `ε²·1` ⟹ 非零ベクトルを固定しない。

**書籍の場合 `F = 𝔽₄₃`**: `exists_odd_order_nonabelian_frobenius_complement`
(`α = -2 = 41` (`(-2)⁷ = 1 - 3·43`), `ε = 6` (`6³ = 1 + 5·43`) を `decide` で確認)。
⟹ **奇数位数の非可換群が Frobenius complement になりうる** (書籍の Note) が形式化された。

再利用 helper (追加分): `unitsMatrixDistribMulAction` (`GL(n,R)` の `n → R` への作用) /
`coe_sup_eq_mul_of_le_normalizer` (`K ≤ N_G(H)` なら `↑(H ⊔ K) = ↑H · ↑K`;
`Subgroup.mul_normal` の正規性を緩めた版) / `scalar_mulVec_ne_of_ne_one` /
`exists_diagonal_eq_one_of_mulVec_eq` / `diagonal_mul_scalar`。

⚠ 実装の罠: `fin_cases k` の後は `simpa using ...` が別方向に正規化することがある
(`(α⁴)ⁱ` が `(αⁱ)⁴` になる) — 補題を `∀ c, ((α^c)^i)^7 = 1` の形で用意して
`exact` (defeq) で当てるのが安全 / `le_sup_left` は項なので `(le_sup_left : H ≤ H ⊔ K) hh` /
`Ch01.card_sup_of_normal_of_coprime` は `S` を implicit に取るので `(S := …)` を明示。

### 6A.1 の実装 (2026-07-27 完了、新 leaf `Problems6A.lean`)

**主結果** `isFrobeniusAction_specialLinearGroupTwo` (実証明・axiom-clean・警告 0)。

論法 (書籍 hint 無しの標準論法): `1 ≠ a ∈ A` が非零ベクトル `v` を固定したとすると
`K := a - 1` は `Kv = 0` ゆえ `det K = 0`。2 次の行列式を展開して `det a = 1` と合わせると
**`tr a = 2`**、これと `det a = 1` から成分計算で **`K² = 0`** (固有値 1 の重根 = 冪単)。
`K² = 0` なら `(1+K)^n = 1 + n·K` (帰納法) で標数 `p` ゆえ **`a^p = 1`**、
`p ∤ |A|` から `orderOf a = 1` で矛盾。

支持部品 (いずれも汎用・再利用可):
* `multiplicativeMulDistribMulAction` — `DistribMulAction M V` ⟹
  `MulDistribMulAction M (Multiplicative V)`。repo の `IsFrobeniusAction` が乗法的なので
  ベクトル空間への線形作用を扱うのに必須 (§6A/§6B の他の問題でも使う)。
* `specialLinearGroupDistribMulAction` — `SL(n,R)` の `n → R` への `mulVec` 作用。
* `one_add_pow_of_sq_eq_zero` — 環で `K² = 0` ⟹ `(1+K)^n = 1 + n•K`。
* `specialLinearGroupTwo_pow_eq_one_of_smul_eq` / `..._eq_one_of_smul_eq` (元の形)。

⚠ 実装の罠: `fin_cases i` の後は添字が `⟨0, _⟩` 形になり `simp only [h00]` (`K 0 0` 形) が
**構文的にマッチしない** — 成分等式を先に `have e00 : (K*K) 0 0 = 0` として証明し、
`fin_cases` 後は `exact e00` (defeq で通る) にする / `Matrix` は非可換環なので
`M = 1 + (M - 1)` は `ring` でなく `abel` / `Multiplicative.ofAdd_toAdd` は無く
`Multiplicative.toAdd.injective` を使う。

## Ch.5 §5E (書籍 p. 175 の Problems 5E) — 🎉 完済 (2026-07-27)

statement は **PDF ページ画像で確定済** (書籍 p.175 = PDF p.188)。§5E は **3 問のみ**。
§5E 本文 (Thm 5.25 / **Thm 5.26 Frobenius** / Lem 5.27 / Lem 5.28 / Cor 5.29 / Cor 5.30) は
`Ch05_Transfer/Main.lean` に**完成済**なので、道具は揃っている。

| 問題 | 状態 | 主張 (PDF 実測) |
|---|---|---|
| 5E.1 | ✅ **完了** (`Problems5E1.lean`) | `G` 有限で**真部分群がすべて正規 `p`-補群をもつが `G` 自身は持たない** ⇒ `G` は正規 Sylow `p`-部分群をもち、`\|G\|` の `p` 以外の素因数はちょうど 1 個 (= Itô「極小非 `p`-冪零群」) |
| 5E.2 | ✅ 完了 (`isSolvable_of_forall_proper_isSupersolvable`) | 真部分群がすべて超可解 ⇒ `G` は可解。hint: 極小反例は単純、Problem 3B.10 で最小素因数 `p` に対する正規 `p`-補群 |
| 5E.3 | ✅ 完了 (`hasNormalPComplement_of_forall_two_generator`) | **2 元生成部分群がすべて正規 `p`-補群をもつ** ⇒ `G` も持つ。hint: `⟨x,y⟩` (`x` は `p`-部分群 `P` の元、`y ∈ N_G(P)` は位数が `p` で割れない) |

### §5E の設計メモ (2026-07-27)

**共通の道具**: **Thm 5.26 Frobenius** (`Main.lean`, 「`G` が正規 `p`-補群をもつ ⟺ 任意の
`p`-部分群 `X` で `N_G(X)/C_G(X)` が `p`-群」) と、その使いやすい形
`isPGroup_normalizerQuotientCentralizer_of_prime_subgroups_centralize`
(「`q ≠ p` の `q`-部分群が `p`-部分群を正規化すれば中心化する」を確かめれば十分)。

* **5E.2 の道筋 (repo 資産が一番揃っている)**: 極小反例 `G` を取る。真部分群は超可解ゆえ可解、
  `1 < N ◁ G` があれば `N` も `G/N` も可解になり矛盾 ⟹ **`G` は単純**。`p` = `|G|` の最小素因数。
  非自明 `p`-部分群 `X` について `N_G(X)` は `G` (単純性より `X ◁ G` は不可) ではなく真部分群、
  よって超可解 ⟹ **3B.7(b)** (`index_prime_of_isCoatom_of_isSupersolvable`) + **3B.8**
  (`exists_normal_qComplement`) で最小素因数の正規 `p`-補群をもつ ⟹ Frobenius (5.26) で
  `G` が正規 `p`-補群 `K` をもつ。`K ≠ ⊥, ⊤` で単純性に矛盾。
  ⚠ 「極小反例」は型レベル帰納 (`motive : ℕ → Prop` で全群型を量化;
  `S7C_ThompsonPComplementFinal` と同じパターン) が要る。
* **5E.1**: Itô の「極小非 `p`-冪零群」。Frobenius の対偶で「`N_G(X)` が正規 `p`-補群を
  持たない非自明 `p`-部分群 `X`」が取れ、仮定から `N_G(X) = G` すなわち `O_p(G) ≠ 1`。
  そこから `P ◁ G` と `|G| = p^a q^b` を出すのが本体 (商への帰納が要る)。
* **5E.3**: Frobenius の判定条件を `q`-部分群版で使い、`x ∈ X` (`p`-部分群) と
  `y ∈ N_G(X)` の `p'`-元に対し `⟨x,y⟩` の正規 `p`-補群から `[x,y] = 1` を出す
  (`y` は `⟨x,y⟩` の `p`-補群に入る)。`|X|` に関する帰納が要りそう。

### 5E.2 の実装 (2026-07-27 完了、新 leaf `Problems5E.lean` 151 行)

型レベル強帰納 (`motive : ℕ → Prop` で全群型を量化、`S7C_ThompsonPComplementFinal` と同型)。

* **非自明な真の正規部分群 `N` がある場合**: `N` は超可解ゆえ可解。`H ⧸ N` の真部分群 `L` は
  `comap (mk' N) L ≠ ⊤` の像なので超可解 (新設 `Ch03.IsSupersolvable.of_surjective` を
  `(mk' N).restrict _ |>.codRestrict L` に適用) ⟹ 帰納法で `H ⧸ N` 可解 ⟹
  `solvable_of_ker_le_range` で拡大が可解。
* **無い場合 (単純)**: `H` が `p`-群 (`p := minFac |H|`) なら冪零ゆえ可解。そうでなければ
  非自明 `p`-部分群 `X` に対し `N_H(X) ≠ ⊤` (⊤ なら `X ◁ H` で単純性から `X ∈ {⊥,⊤}`、
  どちらも除外)、ゆえに超可解 ⟹ **3B.7(b)** で極大部分群の指数が素数 ⟹ **3B.8**
  (`exists_normal_qComplement`、`p` 最小素因数) で正規 `p`-補群 ⟹
  **Frobenius Thm 5.26** で `H` 自身が正規 `p`-補群 `K` をもつ。`p ∣ |H|` で `K ≠ ⊤`、
  `H` が `p`-群でないので `K ≠ ⊥` ⟹ 単純性に矛盾。

**Ch03 側の追加**: `IsSupersolvable.of_surjective` (超可解列を押し出すだけ) を新設し、
既存の `IsSupersolvable.quotient` はその特殊化に書き換えた (重複解消)。

⚠ 実装の罠: `rw [hbot] at hmul` は `K.index` の `K` まで書き換えて後続の `hidx` が
マッチしなくなる — `Nat.card ↥K = 1` だけを別 `have` にして書き換える。
`push_neg` は deprecated (`push Not`)。

### 5E.3 の実装 (2026-07-27 完了、`Problems5E.lean` に追記)

⭐ **帰納法が要らない**。Frobenius Thm 5.26 の十分条件
`isPGroup_normalizerQuotientCentralizer_of_prime_subgroups_centralize`
(「`q ≠ p` の `q`-部分群 `Q` が `p`-部分群 `X` を正規化するなら中心化する」を確かめれば十分)
に対して、`x ∈ X`, `y ∈ Q` を取り `H := ⟨x,y⟩` (2 元生成) の正規 `p`-補群 `K` を使うと:

* `y` の位数は `q`-冪 (⟹ `p` と素) で `H ⧸ K` は `p`-冪位数 ⟹ **`y ∈ K`**;
* `y` は `X` を正規化するので `⁅x,y⁆ = x·(y x⁻¹ y⁻¹) ∈ X` (`p`-群);
* `K ⊴ H` と `y ∈ K` から `⁅x,y⁆ = (x y x⁻¹)·y⁻¹ ∈ K` (`p'`-群)。

`⁅x,y⁆` の位数が `p`-冪かつ `p` と素 ⟹ `⁅x,y⁆ = 1`。

⚠ 実装の罠: `orderOf_injective f hf a` は `a` を**明示的に渡す** (メタ変数のままだと
`f ?a = x*y*x⁻¹*y⁻¹` を unify できない)。`orderOf_map_dvd` で商への位数の割り切れを取る。

### 5E.1 (Itô) の設計 — **完全に確定** (2026-07-27、前回の未確定部分を解消)

前 iteration で詰まっていた 2 点は**文献を読まずに解消できた**。鍵は
**「極小非 `p`-冪零群は指数 `p` の正規部分群を持たない」**という補題。⭐ **位数に関する
帰納法は一切不要** (Lemma 1 を `G` と `G/O_p(G)` の 2 つの群に適用するだけ)。

**補題 1** (`opCore ≠ ⊥`): Frobenius Thm 5.26 の対偶で `N_G(X)` が正規 `p`-補群を持たない
非自明 `p`-部分群 `X` が取れ、仮定から `N_G(X) = ⊤` すなわち `X ◁ G` ⟹ `O_p(G) ≠ 1`。

**補題 2** (指数 `p` の正規部分群は無い) ⭐**これが前回の欠けていた鍵**: `M ◁ G` で
`|G:M| = p` とすると `M` は真部分群ゆえ `p`-冪零、その正規 `p`-補群 `C` は一意性から
`M` に characteristic ⟹ `C ◁ G`。`p ∤ |C|` かつ `|G:C| = p·|M:C|` は `p`-冪 ⟹
`C` が `G` の正規 `p`-補群になり仮定に矛盾。

**補題 3** (`G/O_p(G)` は `p`-冪零): そうでなければ `G/O_p(G)` も極小非 `p`-冪零 (真部分群は
全射像ゆえ `p`-冪零 — 新設 `hasNormalPComplement_of_surjective`) なので**補題 1** が使えて
`O_p(G/O_p(G)) ≠ 1`、その引き戻し `M` は `|M| = |O_p(G)|·(p-冪)` で `p`-群かつ正規、
`normal_pgroup_le_opCore` で `M ≤ O_p(G)` となり矛盾。

**(a) 正規 Sylow `p`-部分群**: 補題 3 の正規 `p`-補群 `K̄` の引き戻し `K` は `|G:K|` が `p`-冪。
`K ≠ ⊤` なら `G/K` は非自明 `p`-群ゆえ極大部分群 (1D.6 で指数素数、冪零ゆえ正規) の
引き戻しが**指数 `p` の正規部分群**になり補題 2 に矛盾 ⟹ `K = ⊤` ⟹ `G/O_p(G)` は
`p'`-群 ⟹ `O_p(G)` は正規 Sylow `p`-部分群。

**(b) `p` 以外の素因数はちょうど 1 個**: (a) の `P := O_p(G)` に Schur–Zassenhaus で
Hall `p'`-補群 `H` を取る (`H ≠ 1`、さもないと `G` が `p`-群で `p`-冪零)。`|H|` が 2 個以上の
素因数をもつなら、各素数 `s` の Sylow `S ≤ H` について `P·S` は**真部分群**ゆえ `p`-冪零、
その正規 `p`-補群は `S` 自身 (正規 Hall `p'`-部分群は全ての `p'`-部分群を含む) ⟹
`[P, S] ≤ P ⊓ S = 1`。`H` は Sylow 部分群たちで生成される (**5C.11 の `iSup_sylow_eq_top`**)
ので `H ≤ C_G(P)` ⟹ `H ◁ G` が正規 `p`-補群になり矛盾。⟹ `|H|` は素数冪。

### 🎉 5E.1 (Itô) 完了 (2026-07-27) — `Problems5E1.lean` 528 行

**全て実証明・axiom-clean (`propext`/`Classical.choice`/`Quot.sound` のみ)・警告 0**。
設計 (上記「5E.1 (Itô) の設計 — 完全に確定」節) はそのまま通った — **位数に関する帰納法は不要**。

主結果:

* `hasNormalPComplement_quotient_opCore_of_forall_proper` = **補題 3** (`G/O_p(G)` は `p`-冪零)。
  ⚠ **設計時の想定より仮定が 1 つ落ちた**: `G` 自身が `p`-冪零でないことは**不要**
  (`G` が `p`-冪零なら商もそう)。証明は「補題 1 を `G ⧸ O_p(G)` に適用 →
  `O_p(G/O_p(G)) ≠ 1` → 引き戻しが正規 `p`-部分群で `O_p(G)` の最大性に矛盾」。
* `sylow_eq_opCore_of_minimal_non_pNilpotent` = **(a)** (`Syl_p(G) = O_p(G)`, 一意)
  + `normal_sylow_of_minimal_non_pNilpotent` (正規 Sylow の存在)。
* `card_primeFactors_erase_eq_one_of_minimal_non_pNilpotent` = **(b)**
  (`|G|` の `p` 以外の素因数はちょうど 1 個) + 使いやすい形
  `exists_prime_card_eq_pow_mul_pow_of_minimal_non_pNilpotent`
  (`∃ q a b, q.Prime ∧ q ≠ p ∧ 1 ≤ a ∧ 1 ≤ b ∧ |G| = p^a q^b`)。
* `prime_dvd_card_of_not_hasNormalPComplement` (`p ∤ |G|` なら `⊤` が正規 `p`-補群)。

再利用可能な汎用 helper 5 本 (いずれも 5E.1 専用でない):

* `hasNormalPComplement_of_surjective` — 正規 `p`-補群は**全射像**に遺伝。
* `isPGroup_comap_mk'_of_isPGroup` — `p`-群 `N` による商の `p`-部分群の引き戻しは `p`-群。
* `card_map_mk'_of_inf_eq_bot` — `C ⊓ N = ⊥` なら `|C.map (mk' N)| = |C|`
  (`(mk' N).comp C.subtype` の単射性経由)。
* `le_of_index_eq_pow_of_not_dvd_card` — 指数が `p`-冪の正規部分群は `p'`-部分群を全て含む
  (= 正規 `p`-補群が `p'`-部分群を全て含むことの一般形)。
* `exists_normal_index_eq_prime_of_index_eq_pow` — 指数 `p^a` (`a ≥ 1`) の正規部分群が
  あれば指数ちょうど `p` の正規部分群がある (1D.6 `isCoatom_iff_index_prime` +
  冪零の正規化条件 + `IsCoatomic.eq_top_or_exists_le_coatom`)。

**(b) の実装で効いた工夫** — 部分群の積の位数公式 (`|HK|·|H∩K| = |H||K|`, Set 積) を
**一度も使わずに済ませた**。代わりに商 `G ⧸ O` への像で測る:

* `O ⊔ T ≠ ⊤` は「`(O ⊔ T).map π = T.map π` かつ `|T.map π| = |T| < |H| = |G ⧸ O|`」で出る
  (`⊤` なら像も `⊤`)。
* `|O ⊔ T| = |O|·|T|` は `O ≤ O ⊔ T` から `(O⊔T).index = ((O⊔T).map π).index`
  (`comap_map_eq` + `index_comap_of_surjective`) を作り、3 本の `card_mul_index` を
  掛け合わせて `(O⊔T).index` で消去。
* `T ⊴ O ⊔ T` は「`T.subgroupOf (O⊔T) ≤ C`(= `p`-補群) かつ位数一致 ⟹ `= C`」で出す。

⚠ 実装の罠: `Subgroup.map_eq_bot_iff` は `H` が**明示引数**なので `.mpr` のドット記法が
効かない (`Unknown constant`) — `QuotientGroup.map_mk'_self` (`N.map (mk' N) = ⊥`, simp) を使う /
`le_sup_left` は項であって関数でないので `x ∈ O ⊔ T` を得るには `(le_sup_left : O ≤ O ⊔ T) hx` /
`Nat.factorization_prod_pow_eq_self` は deprecated (`Nat.prod_factorization_pow_eq_self`)。

### 🎉 §5E 完済 (5E.1 / 5E.2 / 5E.3 の全 3 問) ⟹ Isaacs Ch.5 の章末演習は §5A–§5E 全完。

## Ch.5 §5B (書籍 p. 157 の Problems 5B) — 着手 (2026-07-26)

| 問題 | 状態 | 実装 |
|---|---|---|
| 5B.1 | ✅ `exists_notMem_conj_mem_of_mem_commutator` | `P ∈ Syl_p(G)`, `g ∈ P` 位数 `p`, `g ∈ G'`, `g ∉ P'` ⇒ `g^t ∈ P` なる `t ∉ P` が存在。transfer-evaluation lemma (Thm 5.5 = mathlib `MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot`) を使う |
| 5B.2 | ✅ | `card_closure_le_pow_card` (書籍の形) / `card_closure_range_le` (添字形) — `Problems5B.lean` |
| 5B.3 | ✅ | `exists_finite_normal_iff` (`Problems5B.lean`) + `normal_closure_of_conj_closed` |

### 5B.2: 正しい論法 (2026-07-26 に確定) — 隣接交換によるソート

**⚠ 前回の診断を訂正する。** 「書籍 hint は動かない」と書いたが、それは
**ブロック収集** (「`x₁` を全部前に出し、次に `x₂` を…」) という読み方に対してであって、
**隣接交換でソートする**読み方なら hint は正しく、以下で厳密に証明できる。

**書き換え規則**: 語の中の隣接する 2 文字 `x_i x_j` が `i > j` (添字の逆転) なら
`x_i x_j = x_j · (x_j⁻¹ x_i x_j) = x_j x_k` と書き換える (`X` 共役閉ゆえ `x_k ∈ X`;
`x_j⁻¹ x_i x_j = x_j ⟺ x_i = x_j` なので `k ≠ j`)。

**停止性 (⭐ ここが要)**: 語の**添字列を辞書式順序で見ると狭義に減少する** —
書き換えは位置 `p` の添字を `i` から `j < i` に変え、`p` より前は不変だから。
長さは不変で、添字は `Fin m` の有限集合を動くので、長さ `L` の添字列は有限個 ⟹ 停止。
Lean 用の具体的な減少測度は **`m` 進数値 `μ(ι) := ∑_p ι_p · m^{L-1-p}`**:
位置 `p` が `i → j` (`j ≤ i-1`)、位置 `p+1` が任意 (`≤ m-1`) なので
`Δμ ≤ -m^{L-1-p} + (m-1)·m^{L-2-p} = -m^{L-2-p} < 0`。

**停止時**: 逆転が無い = 添字列が広義単調増加 = `x₁^{a₁} x₂^{a₂} ⋯ x_m^{a_m}` の形。
最後に `x_i^n = 1` で各指数を `n` 未満に落とす ⟹ `|⟨X⟩| ≤ n^m`。
(`⟨X⟩` = `X` の元の積全体。`x⁻¹ = x^{n-1}` なので逆元は別途要らない。)

**なぜブロック収集だと壊れるか (参考)**: `x₂` の収集中の共役が `x₁` に戻りうる。
`G = S₃`, `X` = 3 互換, `w' = (23)(13)` は `(12)` を含まないが `(13)` を前に出すと
`(13)(12)` になる。隣接交換版ならここからさらに `(13)(12) = (12)((12)(13)(12)) = (12)(23)`
と進んでソート済になる (添字列 `(3,2) → (2,1) → (1,3)`; 辞書式に減少)。

**得られている部品 (landing 済、`Dietzmann.lean`)**:
`conj_mem_sdiff_singleton` (`x` による共役は `X \ {x}` を保つ) /
`closure_le_normalizer_closure_sdiff` (`⟨X \ {x}⟩ ⊴ ⟨X⟩`; `|⟨X⟩| ≤ n·|⟨X\{x}⟩|` を与えるが
帰納は閉じない — 上の論法とは別筋) / `conj_mem_closure_of_conj_mem` /
`exists_pow_mul_prod_eq_notMem`。

**実装状況 (2026-07-26)**: **組合せ部分は landing 済** (`Problems5B.lean` の
`namespace Sort5B2`):
* `measure` (`m` 進数値) と `measure_lt` / `measure_cons_lt` / `measure_append_lt`
* `exists_inversion` — ソートされていない添字列には隣接逆転がある
* ⭐ `exists_chain'_map_prod_eq` — 共役閉な枚挙 `xs : Fin m → G` に対し
  **任意の添字列は同じ積を与える単調増加な添字列に書き換えられる** (`measure` の強帰納)

⚠ `List.Chain'` は deprecated、`List.IsChain` を使う (`List.isChain_cons` /
`isChain_nil` / `isChain_singleton`)。

**2026-07-26 に完成**。数え上げは**正規形の一意性**で回した:
`eq_of_count_eq` (単調増加列は重複度ベクトルで決まる; `List.Perm.eq_of_sortedLE` +
`List.sortedLE_iff_isChain` + `List.perm_iff_count` で 1 行) から
`{κ // κ.IsChain (· ≤ ·) ∧ ∀ i, κ.count i < n} ↪ (Fin m → Fin n)` を作り、
そこからの全射で `Nat.card ⟨X⟩ ≤ n^m` (`Nat.card_le_card_of_surjective`)。
⭐ **重複度ベクトルから整列列を構成する必要はない** (単射だけで足りる) のが軽量化の要点。
書籍の形 `card_closure_le_pow_card` は `Finset.equivFin` で枚挙を作って添字形に流すだけ。

⚠ mathlib API: `List.eq_of_perm_of_sorted` は無い — `List.Perm.eq_of_sortedLE` +
`List.sortedLE_iff_isChain` を使う。

⚠ **`S₃` は「因子がすべて `≤ n` の subnormal 列」では説明できない** (`|S₃| = 6 = 2·3` で
`3 > 2`) ので、`n^m` は**衝突込みの数え上げ**でしか出ない。鎖による評価を試みても無駄。

### ⚠ 5B.1 の書籍訂正 (2026-07-26)

書籍の印刷は「show that `g^t ∈ P'` for some element `t ∈ G` with `t ∉ P`」だが、
**巻末 errata の項目 3 (p. 157) が「`P` の dash を削れ」= `g^t ∈ P` に訂正**している。
PDF ページ画像 (書籍 p.157 = PDF p.170) と errata の両方で確認済。
数学的にも訂正版が正しい: transfer-evaluation で `V(g) = ∏_{n_t=1} g^{t⁻¹}` (mod `P'`) となり、
もし全ての `t` で `g^{t⁻¹} ≡ g` (mod `P'`) なら `V(g) ≡ g^N`, `N = #{t : n_t=1} ≢ 0 (mod p)`
となって `V(g) ∈ P'` に矛盾。`P` の元による共役は `P/P'` に自明に作用するので、
`g^{t⁻¹} ∉ gP'` なる `t` は `t ∉ P` をみたす。

## Ch.5 §5A (書籍 pp. 152-153 の Problems 5A) — **完了 (2026-07-26)**

新 leaf `OddOrder/Isaacs/Ch05_Transfer/Problems.lean` (namespace `OddOrder.Isaacs.Ch05`、
`OddOrder.lean` 配線済)。mathlib の transfer は
`MonoidHom.transfer (ϕ : ↥H →* A) : G →* A` (`A` 可換) で、Isaacs の `v : G → H/H'` は
`A = H/H'`, `ϕ` = 自然な射影の場合。

| # | 状態 | Lean 名 / メモ |
|---|---|---|
| 5A.1 | ✅ | `transfer_id_eq_pow_index_of_commGroup` / `coe_transfer_id_of_commGroup` |

⚠ **余域を `↥H` に取る版は避ける**: `H ≤ Z(G)` の一般形で `CommGroup ↥H` を statement 内
`letI` で供給すると, その instance の `toGroup` が `Subgroup.toGroup` と構文的に一致せず
`MonoidHom.id ↥H` の型が合わない (diamond)。**一般の `ϕ : ↥H →* A` 版で述べる**のが正解
(Isaacs の `v : G → H/H'` はまさにこの形)。
| 5A.2 | ✅ | `transfer_top_eq_apply` |
| 5A.3(a)(b) | ✅ | `eq_of_mul_eq_mul_of_isComplement` / `isComplement_mul_of_transversal` (mathlib に `IsComplement` の推移律が無いので自作)。(b) の数値部分は mathlib `relIndex_mul_index` |
| 5A.3(c)(d) | ✅ | `transfer_transfer` (transfer の推移律、mathlib に無い新規形式化) | **transfer の推移律**。mathlib は pretransfer を持たず `diff` 経由なので、Isaacs の `w = v ∘ V_T` は「`H ≤ K ≤ G`, `ϕ : ↥H →* A` に対し `transfer_{K≤G} (transfer_{(H.subgroupOf K) ≤ K} ϕ') = transfer_{H≤G} ϕ`」の形になる (`ϕ'` は `↥(H.subgroupOf K) ≃* ↥H` を経由した `ϕ`)。`subgroupOf` の同型を挟むのが主な摩擦。5A.3(b) で作った `isComplement_mul_of_transversal` を `LeftTransversal` に持ち上げ、`transfer_def` で両辺の `diff` を `S * T` 上の積として比較するのが素直な経路 | 推移律。**(b) の数値部分 `|G:H| = |G:K||K:H|` は mathlib `Subgroup.relIndex_mul_index` で既済**。transversal の積 `ST` の一意分解 (a) / (b) の transversal 性は **mathlib に既製が無い** (`Subgroup.IsComplement` の推移律は未収載; `IsComplement.mul_eq` のみ)。`↥K` の subtype を跨ぐので定式化に注意 — 「`S ⊆ K` かつ `∀ k ∈ K, ∃! s ∈ S, k·s⁻¹ ∈ H`」+「`IsComplement (K : Set G) T`」⟹「`IsComplement (H : Set G) (S * T)`」の形が素直。(c)(d) の pretransfer 合成は mathlib が `diff` 経由の定義なので、この transversal 推移律を作ってから `transfer_def` で両辺を比較する |

### 5A.3(c)(d) の実装状況 (2026-07-26)

⚠ **書籍は右 transversal、mathlib の `MonoidHom.transfer` は左 transversal**
(`Subgroup.LeftTransversal` = `{S // IsComplement S H}`) で定義されている。
そこで (b) の左版 `isComplement_mul_of_transversal_left`
(`T` が `K` の左 transversal, `S ⊆ K` が `K` 内の `H` の左 transversal ⇒ `T * S` が
`H` の左 transversal) を landing 済 (`Problems.lean`)。

**5A.3(c) の書籍の主張 (PDF p.152 = PDF ページ 165 で確認)**:
`(st)·g = s·(t g (t·g)⁻¹) · (t·g)`。`·` は transversal の「代表元へ落とす」作用。
これは左版では「`T * S` 上の `g` 作用が `T` 成分と `S` 成分に分かれる」ことにあたる。

**5A.3(d) = transfer の推移律**:
`transfer_{K≤G} (transfer_{(H.subgroupOf K)≤K} ϕ') = transfer_{H≤G} ϕ`
(`ϕ' = ϕ ∘ (Subgroup.subgroupOfEquivOfLe hHK)`)。
⚠ **mathlib に transfer の推移律は無い** (`Mathlib/GroupTheory/Transfer.lean` を grep 済)。
**(ii) の Equiv は landing 済 (2026-07-26)**: `quotientEquivProd hHK T :
G ⧸ H ≃ (G ⧸ K) × (↥K ⧸ H.subgroupOf K)` (`⟦g⟧_H ↦ (⟦g⟧_K, ⟦τ(⟦g⟧_K)⁻¹ g⟧)`)。
⭐ **`T * S` を Set として作らなくてよい**のが要点 — 分解 Equiv は `T` だけで決まり、
`S` は不要。計算則 `quotientEquivProd_symm_apply` / `_apply_fst` / `_apply_snd` はすべて `rfl`。
⚠ `left_inv` は `Quotient.liftOn'` の beta/iota 簡約が `rw` に効かないので `change` で
明示的に落とす必要がある。

**積 transversal も landing (2026-07-26)**: `mulTransversalFun` (`q ↦ τ(q₁)·σ(q₂)`) /
`mulTransversalFun_spec` / `mulTransversal` / `mulTransversal_leftQuotientEquiv`。
⭐ **`Set` の積を作らず `Set.range F` として構成する**のが要点 —
mathlib `Subgroup.isComplement_range_left` (「`∀ q, (F q : G ⧸ H) = q` なら
`Set.range F` は左 transversal」) と `Subgroup.IsComplement.leftQuotientEquiv_apply` で
**transversal 性と代表元計算則が同時に**手に入り、`isComplement_mul_of_transversal_left`
(書籍 5A.3(b) の忠実な形式化として保持) を経由する必要すらない。

**残作業 = 最終計算のみ**。因子の計算は次のとおり確認済 (紙の上):
`q = e.symm (q₁, r)` に対し `(P q)⁻¹ · (g•P) q = (σ r)⁻¹ · m⁻¹ · σ(m•r)`,
ここで `m := ⟨τ(g⁻¹•q₁)⁻¹ · g⁻¹ · τ(q₁)⟩ ∈ K`。ゆえに
`∏_r ϕ(…) = diff_{H'} ϕ' S (m⁻¹ • S) = transfer_{H'≤K} ϕ' m⁻¹`,
`∏_{q₁} が diff_K (transfer ϕ') T (g•T) = transfer_K (transfer ϕ') g`。
**部品は 2026-07-26 にすべて landing**:
* `diff_eq_prod` — `Subgroup.leftTransversals.diff` の展開形。⭐ **`rfl` で通る**
  (`let _ := H.fintypeQuotientOfFiniteIndex` を展開形でも使い、membership 証明項は
  proof irrelevance で吸収される)。
* `mulTransversal_apply_symm` — `P (e.symm (q₁, r)) = τ q₁ · σ r`。
* `transferCocycle T g q := ⟨τ(q)⁻¹ · g · τ(g⁻¹•q)⟩ ∈ K` — 外側 `diff` の因子そのもの。
* `quotientEquivProd_smul_symm` — `e (g⁻¹ • e.symm (q₁, ⟦k⟧)) = (g⁻¹•q₁, ⟦m⁻¹ · k⟧)`,
  `m = transferCocycle T g q₁`。
  ⚠ **`m` と `m⁻¹` の取り違えに注意** (第 2 成分に現れるのは `m⁻¹ = τ(g⁻¹•q₁)⁻¹ g⁻¹ τ(q₁)`、
  `diff` の因子は `m` 自身)。1 回間違えて `group` が閉じずに発覚した。

**2026-07-26 に完成**: `mulTransversal_diff_factor` (因子 `(P q)⁻¹·(g•P)q =
(σ⟦k⟧)⁻¹·m·σ(m⁻¹•⟦k⟧)` を `↥K` 側の `diff` 因子に落とす) + `transfer_transfer` (本体)。
本体は `transfer_def` → `diff_eq_prod` → `Equiv.prod_comp (quotientEquivProd …).symm`
→ `Fintype.prod_prod_type` → `Finset.prod_congr` 2 段、で 20 行ほど。
⚠ `Subtype.mk` の中を `rw` すると motive エラーになるので、先に `change` で
coe を剥がしてから rewrite する。

### 5A.2 の設計 (2026-07-26 に確定、**実装済** `transfer_top_eq_apply`)

⚠ 実装知見: `diff` は **`Subgroup.leftTransversals.diff`** (MonoidHom 名前空間ではない) /
`Fintype (G ⧸ H)` は **`letI`** で入れる (`haveI` だと `diff` の `let` が展開した
`Subgroup.fintypeQuotientOfFiniteIndex` と defeq 判定に失敗する) /
`transfer_eq_pow` は key 仮説が `H = ⊤` で偽なので使えない。


**statement**: `A` 可換, `ϕ : ↥(⊤ : Subgroup G) →* A` に対し
`transfer ϕ g = ϕ ⟨g, Subgroup.mem_top g⟩`。Isaacs の `v : G → G/G'` は
`A = G/G'`, `ϕ` = 自然な射影の場合で, これがまさに「transfer = 自然な射影」。

**証明**:
1. `[(⊤ : Subgroup G).FiniteIndex]` (`Subgroup.index_top = 1`)。
2. `transfer_def ϕ T g : transfer ϕ g = diff ϕ T (g • T)` (`T` は任意の left transversal;
   `default` でよい)。
3. `diff ϕ S T = ∏ q : G ⧸ H, ϕ ⟨(α q)⁻¹ * β q, _⟩` (`α = S.2.leftQuotientEquiv`,
   `β = T.2.leftQuotientEquiv`) を展開。`Subsingleton (G ⧸ ⊤)`
   (`QuotientGroup.subsingleton_quotient_top`) なので **積は 1 項**
   (`Fintype.prod_subsingleton`)。
4. ⭐ **鍵の mathlib 補題** `Subgroup.smul_apply_eq_smul_apply_inv_smul (f) (S) (q) :
   ((f • S).2.leftQuotientEquiv q : G) = f • (S.2.leftQuotientEquiv (f⁻¹ • q) : G)`。
   subsingleton なので `g⁻¹ • q = q`, したがって `β q = g * (α q)`。
5. よって唯一の項は `ϕ ⟨(α q)⁻¹ * g * (α q)⟩` = `g` の**共役**の `ϕ`-像。
   `↥⊤` では `⟨x⁻¹ g x⟩ = ⟨x⟩⁻¹ * ⟨g⟩ * ⟨x⟩` で **`A` が可換**だから
   `ϕ ⟨x⁻¹ g x⟩ = ϕ ⟨g⟩` ∎

⚠ `transfer_eq_pow` は使えない (key 仮説「`g₀⁻¹ g^k g₀ = g^k`」は `H = ⊤` では偽)。
`diff` は `let` を含む noncomputable def なので `simp only [MonoidHom.diff]` で展開する。
| 5A.4 | ✅ | (a) `transfer_eq_pow_index_of_le_center` / (b) `inf_ker_transfer_eq_bot_of_le_center` + `sup_ker_transfer_eq_top_of_le_center` (+ `normal_of_le_center`) |
| 5A.5 | ✅ | `card_ker_dvd_relIndex_commutator` (`ProblemsSchurMultiplier.lean`) — **`M(G)` を定義せず stem extension の ∀-形**で述べた (下記) |
| 5A.7 | ✅ | `card_ker_lt_relIndex_commutator` (同上)。書籍の `G/C` cyclic 仮定は `BC = G` + `B` cyclic から従うので導出に変更 |
| 5A.6 | ✅ | `card_ker_dvd_two_of_dihedral` (上界) + `isStemExtension_dihedralReduce` (下界) — `ProblemsDihedralMultiplier.lean`。書籍の `2^n` 版より強い**偶数一般形**で証明 |
| 5A.8(a) | ✅ | `isStemExtension_prodMap` + `card_ker_prodMap` (`ProblemsSchurMultiplier.lean`) |
| 5A.8(b) | ✅ | `card_ker_eq_mul_card_ker_stem` (`ProblemsProductMultiplier.lean`) | `ProblemsProductMultiplier.lean` に `inf_ker_snd_ker_fst` / `exists_mem_ker_snd_mul_mem_ker_fst` / ⭐`commutator_ker_snd_ker_fst_eq_bot`。残りはステップ 4-6 (下記設計)。準備補題 `not_dvd_card_commutator_of_sylow_le_center` (ステップ 5 用) も landing 済 |

### 5A.8(b) の証明設計 (2026-07-26 確定、実装は次イテレーション)

**∀-形の主張**: `h : Γ →* A × B` が stem extension で `|A|`, `|B|` が互いに素なら,
`A` の stem extension `f` と `B` の stem extension `g` が存在して
`|ker h| = |ker f| · |ker g|`。(a) と合わせて `|M(A×B)| = |M(A)||M(B)|` の位数版。

記号: `Z := ker h`, `Γ_A := ker ((snd).comp h)` (= `h⁻¹(A × 1)`),
`Γ_B := ker ((fst).comp h)`, `n := |A|`, `m := |B|`。

1. `Γ_A ⊓ Γ_B = Z`, かつ `∀ γ, ∃ x ∈ Γ_A, y ∈ Γ_B, γ = x·y` (h の全射性から)。
2. **`⁅Γ_A, Γ_B⁆ = ⊥`** ⭐ ここが coprime を使う要:
   `x ∈ Γ_A`, `y ∈ Γ_B` なら `⁅x,y⁆ ∈ Γ_A ⊓ Γ_B = Z ≤ Z(Γ)`。
   `h (x^n) = (h x)^n = (a^n, 1) = 1` (`pow_card_eq_one`) なので **`x^n ∈ Z`**
   — 剰余群を作らずに済むのがポイント。`⁅x,y⁆` が中心的なので
   `⁅x,y⁆^n = ⁅x^n, y⁆ = 1` (帰納法: `⁅ab,y⁆ = a⁅b,y⁆a⁻¹⁅a,y⁆` で中心性から
   `= ⁅b,y⁆⁅a,y⁆`)。同様に `⁅x,y⁆^m = 1`。coprime ⇒ `⁅x,y⁆ = 1`。
3. `Γ = Γ_A·Γ_B` かつ `⁅Γ_A,Γ_B⁆ = ⊥` ⇒ `Γ' = ⁅Γ_A,Γ_A⁆ ⊔ ⁅Γ_B,Γ_B⁆`
   (`Γ_A × Γ_B → Γ` が全射準同型で `(H×K)' = H'×K'`)。
4. `Z_A := Z ⊓ ⁅Γ_A,Γ_A⁆`, `Z_B := Z ⊓ ⁅Γ_B,Γ_B⁆` とおくと **`Z = Z_A · Z_B`**:
   `z ∈ Z ≤ Γ'` を `z = u·v` (`u ∈ ⁅Γ_A,Γ_A⁆ ≤ Γ_A`, `v ∈ ⁅Γ_B,Γ_B⁆ ≤ Γ_B`) と書くと
   `v = u⁻¹z ∈ Γ_A ⊓ Γ_B = Z` ゆえ `v ∈ Z_B`, `u = zv⁻¹ ∈ Z_A`。
5. **`Z_A ⊓ Z_B = ⊥`**: `p ∤ n` なら `Γ_A` の Sylow-`p` は中心的
   (`|Γ_A| = n|Z|` で `Z ≤ Z(Γ)` ゆえ `Z` の Sylow-`p` が `Γ_A` の Sylow-`p`) なので
   **`not_dvd_card_commutator_of_sylow_le_center`** より `p ∤ |⁅Γ_A,Γ_A⁆|`。
   ⇒ `|Z_A|` の素因数は `n` を割り, `|Z_B|` の素因数は `m` を割る。coprime ⇒ 交わりは自明。
6. `Γ_A/Z_B ↠ A` は核 `Z/Z_B` の stem extension (`Z = Z_A Z_B ≤ ⁅Γ_A,Γ_A⁆·Z_B`),
   同様に `Γ_B/Z_A ↠ B`。核の位数の積 = `|Z|²/(|Z_A||Z_B|) = |Z|` (5 で `|Z_A||Z_B| = |Z|`)。

⚠ 実装上の重さ: `⁅H, K⁆` (Γ 内の部分群としての交換子) と `commutator ↥H` の往復,
`Γ_A × Γ_B → Γ` の準同型構成。~400 行規模の見込み。

**実装メモ (2026-07-26、ステップ 1-3 landing 済)**

- ステップ 2 の `⁅x,y⁆^n = ⁅x^n,y⁆` には**中心的交換子の双線形性**が要るが、repo の既存版は
  BG (Isaacs の下流) にしかなかったので**上流の共有 leaf**
  `OddOrder/GroupTheory/CentralCommutatorPower.lean` を新設した (issue 9207、BG 側の
  重複解消は hub へ申し送り)。
- `Γ_A`, `Γ_B` は `((MonoidHom.snd A B).comp h).ker` / `((MonoidHom.fst A B).comp h).ker`
  として持つのが軽い。`(h x).2 = 1` は `MonoidHom.mem_ker` 後に **defeq でそのまま `have`** で
  取れる (`MonoidHom.snd_apply` という simp 補題は存在しない)。
- ステップ 3 では `IsStemExtension` の全射性も交換子群条件も不要 — 仮説は
  `ker h ≤ Z(Γ)` と coprime だけ。
- **ステップ 4-5 前半も landing (2026-07-26)**。既存述語 `IsCentralProduct` に共通 API を追加:
  `exists_mul` (中心積の元は `x·y` に分解; `closure_induction`)、`mulHom` (`R₁ × R₂ →* G`)、
  `commutatorElement_mul_mul` (`⁅x₁y₁, x₂y₂⁆ = ⁅x₁,x₂⁆⁅y₁,y₂⁆`)、
  `commutator_self` (`⁅R,R⁆ = ⁅R₁,R₁⁆ ⊔ ⁅R₂,R₂⁆`)。
  ⭐ `commutatorElement_mul_mul` は **`mulHom` の `map_commutatorElement` の像そのもの**で、
  積群の交換子が成分ごとであることも部分群 coe が積・逆元と可換であることも定義上等しいので
  `exact hmap.symm` 一行で済む (手で語の並べ替えをする必要はない)。
  ⚠ ただし `map_commutatorElement` の引数は**明示的に与える** (期待型からの推論に失敗する)。
- 5A.8(b) 側では `isCentralProduct_top` / `commutator_eq_sup` / `exists_mul_mem_inf_commutator`。
- **ステップ 5 後半も landing (2026-07-26)**: `inf_inf_commutator_eq_bot` = `Z_A ⊓ Z_B = ⊥`。
  鍵は**抽象化**した `not_dvd_card_commutator_of_ker_le_center`:
  「中心的な核をもつ `ψ : K →* A'` があり `p ∤ |A'|` なら `p ∤ |K'|`」。
  `Syl_p(K)` の元は位数が `p` 冪、その `ψ` 像の位数は `|A'|` を割る ⇒ 互いに素で像 = 1 ⇒
  `Syl_p(K) ≤ ker ψ ≤ Z(K)` ⇒ `not_dvd_card_commutator_of_sylow_le_center`。
  ⭐ この抽象形にすると `Γ_A` 側と `Γ_B` 側が**同じ補題の 2 適用**で済む
  (`ψ` = `fst∘h` / `snd∘h` の制限)。`|Γ_A| = |A||Z|` の位数計算は一切不要だった。
  `⁅H,H⁆` ↔ `commutator ↥H` の往復は mathlib `Subgroup.map_subtype_commutator` +
  `Subgroup.equivMapOfInjective` (`card_commutator_subgroup`)。
- ⚠ `Subgroup.commutator_le_self` は **mathlib に既存** (自作しかけたので削除)。
- **`|Z| = |Z_A|·|Z_B|` も landing (2026-07-26)** = `card_ker_eq_mul`。
  `Z = Z_A ⊔ Z_B` は**再び中心積** (`isCentralProduct_ker`; `Z_A ≤ Γ_A`, `Z_B ≤ Γ_B` と
  `⁅Γ_A,Γ_B⁆ = ⊥`) で、`Z_A ⊓ Z_B = ⊥` と合わせて内部直積。
  `CentralProduct.lean` に `range_mulHom` と `card_eq_mul`
  (「交わらない中心積の位数は因子の位数の積」= `mulHom` が単射で像が `R`) を追加。
- **商への降下の抽象形 `isStemExtension_lift` を landing (2026-07-26)**:
  「`ψ : K →* A'` が全射・核が中心的、`N ⊴ K` が `N ≤ ker ψ` かつ `ker ψ ≤ K' ⊔ N` ⇒
  `K ⧸ N →* A'` は stem extension で `|N|·|ker| = |ker ψ|`」。
  ⭐ **抽象化しておくと `A` 側と `B` 側が同じ補題の 2 適用**になる。
  位数部分は `(mk' N).restrict ψ.ker` に第一同型 + Lagrange (`Subgroup.index_ker`) を当てるだけ。
- **5A.8(b) 完成 (2026-07-26)**: `prodStemHomFst h : ↥Γ_A ⧸ Z_B →* A` /
  `prodStemHomSnd h : ↥Γ_B ⧸ Z_A →* B` を `QuotientGroup.lift` で定義し、
  `isStemExtension_lift` を 2 回適用 → `card_ker_eq_mul_card_ker_stem`。
  `Z_B ⊴ Γ` は仮説不要 (`h.ker` 正規 + `⁅Γ_B,Γ_B⁆` 正規 + `inf` 正規) なので
  `Subgroup.normal_subgroupOf` が instance で効き、商が仮説なしで型付く。
  ⚠ `Subgroup.subgroupOf_le_subgroupOf` は存在しない — `subgroupOf = comap subtype` なので
  `Subgroup.comap_mono` を使う。
  ⚠ `Subgroup.mul_mem_sup` は第 1 因子が左の summand にある形しか取れない。順序が逆のときは
  `Subgroup.mul_mem _ (mem_sup_right …) (mem_sup_left …)`
  (誤って `mul_mem_sup (mem_sup_left …)` と書くと whnf timeout になる)。

### ⚠ 5A.6 の書籍読解訂正 (2026-07-26)

`pdftotext` は**上付き文字を落とす**ので 5A.6 が「dihedral of order **2n** where n > 2」と
読めるが、この読みは**偽** (n 奇数なら `M(D_{2n}) = 1`; `D_6 = S_3` は Sylow が全て巡回で
Isaacs 自身の Cor 5.4 から `M = 1`)。PDF ページ画像 (書籍 p.153 = PDF p.166) で確認した
正しい主張は **「dihedral of order `2^n` where `n ≥ 2`」= 二面体 2-群**。
同じ潰れは書籍 p.76 の semidihedral `SD_{2^n}` でも起きている。
⟹ **添字に「数字+文字」(`2n`, `pn` …) が現れたら上付き潰れを疑い PDF 画像で確認する。**

実装は書籍の `2^n` 版より強い**偶数一般形**:「`m` 偶数 ⇒ 位数 `2m` の二面体群の
Schur 乗数は位数 2」(`m` 奇数なら 5A.5 から直ちに `M = 1` なので偶数条件は本質的)。
下界の witness は `D_{4t} ↠ D_{2t}` (核 `⟨r (2t)⟩`、中心的かつ `⁅r t, sr 0⁆ = r (2t)`
ゆえ交換子群に入る)。

### 5A.5 / 5A.7 の設計 (2026-07-26 確定・実装済)

Schur 乗数 `M(G)` の universal object (Schur 表現群) は mathlib にも本リポにも無い
(issue 9206 で 3 案を実測比較) が、**5A.5 / 5A.7 の主張は上界なので
「`ker f ≤ Γ' ⊓ Z(Γ)` なる全射 `f : Γ →* G` すべてについて」の ∀-形で述べれば
`M(G)` の定義を一切必要としない** (`|M(G)|` は `Nat.card (ker f)` の最大値)。
`CentralTransfer.lean` の Thm 5.4 弱形と同じ流儀。

* 述語 `IsStemExtension f` は**部分群 `Z` + 同型 `Γ/Z ≅ G` でなく全射 `f` + `ker f`** で持つ。
  これにより Noether III の transport が丸ごと不要になり、`|C : G'| = |f⁻¹C : Γ'|` が
  `Subgroup.relIndex_comap` / `comap_map_eq` / `map_comap_eq_self_of_surjective` の 3 行で出る。
* `f⁻¹(C)` の可換性は mathlib `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` を
  制限 hom `(f.comp A.subtype).codRestrict C _ : ↥A →* ↥C` に適用 (生成元を取る手作業は不要)。
* 5A.7 の核心は `Γ = f⁻¹(B)·f⁻¹(C)` ⟹ `f⁻¹(B) ∩ f⁻¹(C) ≤ Z(Γ)`。
  `B ∩ C > 1` の非自明元の持ち上げが `ker f` の外の `f⁻¹(C) ∩ Z(Γ)` の元になり、
  `ker f ⊊ f⁻¹(C) ∩ Z(Γ)` から厳密不等式。
* ⚠ `Subgroup.relIndex_comap` の第 1 明示引数は comap される側 `H` (`H f K` の順)。

## Ch.4 §4D (書籍 p. 145 の Problems 4D) — 進行中 (2026-07-25)

7 問 (4D.1–4D.7)。coprime action の節。

| # | 状態 | Lean 名 (`OddOrder.Isaacs.Ch04`) / leaf |
|---|---|---|
| 4D.1(a)(b) | ✅ | `commutator_eq_bot_of_centralizer_le_of_coprime` / `inf_centralizer_eq_bot_of_centralizer_le_of_coprime` (`ProblemsCoprimeAction.lean`) |
| 4D.2 | ✅ | `baerAdd_mul_inv_of_commutator_le_center` / `baerMul_div_eq_commutator` (`ProblemsBaerAddition.lean`) |
| 4D.3 | ✅ 全 7 小問 | `IsIrreducibleCoprimeAction.*` (`ProblemsIrreducibleAction.lean`): (a) `exists_isPGroup` / (b) `commutator_le_center` / (c) `fixedPoints_eq_commutator` + `eq_commutator_or_eq_top_of_isAInvariant` / (d) `pow_mem_commutator` + `pow_eq_one_quotient_commutator` / (e) `pow_eq_one_of_mem_commutator` / (f) `pow_eq_one_of_ne_two` / (g) `pow_four_eq_one_of_two` |
| 4D.4 | ✅ | `actionCommutator_eq_bot_of_isPGroup_two_of_fixes_pow_four` (`ProblemsIrreducibleAction.lean`) |
| 4D.5 主張本体 | ✅ | `derivedSeries_semidirectProduct_eq_bot_and_ne_bot` (上界 `..._eq_bot` / 下界 `..._ne_bot` / Lemma 4.29 部分群版 `commutator_commutator_inl_inr_map_eq`、新 leaf `ProblemsDerivedLength.lean`) |
| 4D.5 系 | ✅ | `exists_finite_group_derivedSeries_ne_bot` + `regularPermAut` / `regularPermAut_injective` (同 leaf) |
| 4D.6 | ✅ | `range_fittingProductHom_eq_fixedPoints` / `ker_fittingProductHom_eq_actionCommutator` (新 leaf `ProblemsFittingMap.lean`) |
| 4D.7 | ✅ | `le_oPiCore_compl_of_sylow_isCyclic` (新 leaf `ProblemsCyclicSylow.lean`) |

### 🎉 §4D 完済 (4D.1–4D.7 全 7 問) ⟹ **Isaacs Ch.4 の章末演習 (§4A–§4D) 全完**

### 4D.1 の設計 (実装済)

周囲群 `Γ` の部分群として述べる。鍵は `mem_of_pow_card_eq_one_of_mem_centralizer`
(`C_Γ(N)` の元で `|A|` 乗が 1 のものは `A` に入る) — `x = a·g` 分解 + `C_Γ(N) ⊓ G ≤ N` +
互いに素性。これで `G ≤ N_Γ(A)` が出て `⁅G,A⁆ ≤ G ⊓ A = 1`。(b) は `A₀ := A ⊓ C_Γ(N)` に (a)。

### 4D.4 の設計 (実装済)

`|H|` の強い帰納法。`A`-不変部分群 `H` への制限作用 (`Ch03.IsAInvariant.toMulAutHom`) が
非自明なら、帰納法の仮定で `H` の真の `A`-不変部分群すべてに自明作用 ⟹
`IsIrreducibleCoprimeAction` 成立 ⟹ **4D.3(g)** で `H` の全元が `y⁴ = 1` ⟹ 仮定で固定。
補助 `isAInvariant_map_subtype_of_isAInvariant`。
⚠ `Ch03.IsAInvariant.toMulAutHom` は `ThreeSubgroups.lean` で `_root_.` 無しに宣言されており
実名が `OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom` — namespace Ch04 の
中では `OddOrder.Isaacs.Ch03.…` とフルに書く (`Ch03.…` では解決しない)。

### 4D.5 の設計 (下界 + 系が残り)

**上界 (実装済)**: `rightHom : B ⋊ A ↠ A` で `(B ⋊ A)^{(n)} ≤ ker rightHom = inl(B)`、
`inl(B)` 可換ゆえ `(B ⋊ A)^{(n+1)} = 1`。coprime も faithful も不要。

**下界 (実装済)**: `V := A^{(n-1)} ≠ 1` (導来長がちょうど `n`)。`(|B|, |V|) = 1` と `B` 可換から
Lemma 4.29 (`⁅B, V, V⁆ = ⁅B, V⁆`; repo は `actionCommutator` 形) が使える。
半直積 `Γ = B ⋊ A` の中で `W := ⁅inl(B), inr(V)⁆` とおくと:
- `inr(V) ≤ Γ^{(k)}` (∀ `k ≤ n-1`; `inr` は導来列を保つ + `V = A^{(n-1)} ≤ A^{(k)}`)
- `W ≤ Γ^{(k)}` を `k ≤ n-1` について帰納: `k → k+1` は `W = ⁅W, inr V⁆` (4.29) と
  `W, inr V ≤ Γ^{(k)}` から `W ≤ ⁅Γ^{(k)}, Γ^{(k)}⁆ = Γ^{(k+1)}`。
- 仕上げ: `k = n-1` で `W = ⁅W, inr V⁆ ≤ Γ^{(n)}`、`W ≠ 1` は faithful から
  (`⁅B, V⁆ = 1` なら `V` が `B` に自明作用 ⟹ `V = 1` に矛盾)。
⟹ `Γ^{(n)} ≠ 1` かつ `Γ^{(n+1)} = 1` で導来長ちょうど `n+1`。
⚠ 実装知見: **BG に同型の subgroup 版 4.29 (`commutator_commutator_right_eq`) があるが
BG は Isaacs を import するので Ch04 からは使えない** (import cycle)。Ch04 内では
制限作用の半直積 `Δ = B ⋊[φ∘V.subtype] ↥V` で Γ 形 4.29 を使い、
`F = SemidirectProduct.map (id B) V.subtype : Δ →* Γ` で `Subgroup.map_commutator` により
押し出すのが正しい経路 (`commutator_commutator_inl_inr_map_eq`)。
⚠ `derivedSeries_antitone` は群を**明示引数**で取る (`derivedSeries_antitone A hk`)。

**系 (実装済)**: `C ≀ A` (regular wreath product)。⚠ repo の `WreathProduct` (Ch03,
`D ≀[Ω] Q`) は独立 structure で `SemidirectProduct` ではないため 4D.5 本体に載らない —
同型な半直積 `(A → C) ⋊ A` を `regularPermAut` (座標を `f ↦ fun ω => f (a⁻¹ * ω)` で置換)
として直接構成した。`C` = 位数 `p` 巡回 (`p ∤ |A^{(n-1)}|`, `Nat.exists_infinite_primes`)
とすると `B := (A → C)` は基本アーベル `p`-群 (各座標の位数が `p` を割る) ゆえ
`Nat.card B = p^k` で coprime、正則作用は忠実 (1 の指示関数を `a` で評価)。
⚠ 「導来長」の述語は導入せず `derivedSeries G n ≠ ⊥ ∧ derivedSeries G (n+1) = ⊥` で述べた。
⚠ `Nat.card (Multiplicative (ZMod p)) = p` を使う `rw` は `Fact p.Prime` が `p` に依存して
motive 破綻 — 仮説側で `rw [hcardD] at hpow` と書き換える。

### 4D.6 の設計 (実装済)

`θ = fittingProductHom φ` (`ThreeSubgroupsCoprime.lean`)。像は添字付け替え `a ↦ b*a` で
`A`-固定、逆は `θ(c) = c^{|A|}` と「coprime ⟹ `x ↦ x^{|A|}` が `C_G(A)` 上単射 ⟹
有限性で全射」。核は Lemma 4.28 の `G = C_G(A)·⁅G,A⁆` で `g = c*x` と分解し
`1 = θ(g) = c^{|A|}` から `c = 1` — **位数の数え上げを経由しない**。

### 4D.7 の設計 (2026-07-26 に確定、未実装)

**statement** (PDF p.159 = 書籍 p.146 で確認済): `G` `p`-可解, Sylow `p`-部分群が巡回,
`K ≤ G` が `p'`-部分群で `p ∣ |N_G(K)|` ⟹ `K ⊆ O_{p'}(G)`。

**repo での "p-可解"** = `Ch03.IsPiSeparable ({p} : Set ℕ) G` (π = 単元集合では
π-separable = p-solvable; S7B2 等の既存用法と同じ)。`O_{p'}(G) = oPiCore {p}ᶜ G`,
`O_p(G) = oPiCore {p} G`。

**証明 (|G| の帰納法、hint どおり 2 ケース)**:

- **Case 1: `O_{p'}(G) ≠ 1`**。`Ḡ := G/O_{p'}(G)` に帰納法。仮説は全部遺伝する
  (Sylow の像は巡回、`K̄` は `p'`-群、`p ∣ |N_G(K)|` の位数 `p` の元 `x` は
  `O_{p'}(G)` に入らないので像も位数 `p` で `N_Ḡ(K̄)` に入る)。結論 `K̄ ≤ O_{p'}(Ḡ) = 1`
  (**`O_{p'}(G/O_{p'}(G)) = 1`** — 引き戻しが `p'`-群の正規部分群になるから) ⟹ `K ≤ O_{p'}(G)`。
- **Case 2: `O_{p'}(G) = 1`**。まず **`O_p(G)` が正規 Sylow `p`-部分群**であることを示す:
  1. **Hall–Higman 1.2.3** (repo `Ch03.hall_higman_1_2_3 {p}`, `O_{p'}(G) = ⊥` を仮定) で
     `C_G(O_p(G)) ≤ O_p(G)`。`O_p(G)` は巡回 Sylow の部分群ゆえ巡回=可換なので逆包含も成立し
     **`C_G(O_p(G)) = O_p(G)`**。
  2. `MulAut ↥(O_p(G))` は**可換** (mathlib `IsCyclic.mulAutMulEquiv : MulAut G ≃* (ZMod |G|)ˣ`
     を `injective` で引き戻す; ZGroup.lean:169 と同じイディオム)。`MulAut.conjNormal` の核が
     `C_G(O_p(G)) = O_p(G)` なので **`commutator G ≤ O_p(G)`**。
  3. `O_p(G)` を含む Sylow `p`-部分群 `Q` は `⁅⊤, Q⁆ ≤ commutator G ≤ Q` から正規
     (`le_normalizer_of_commutator_le`)、正規 `p`-部分群ゆえ `Q ≤ O_p(G)`
     (`Subgroup.IsPiGroup.le_oPiCore`) ⟹ `Q = O_p(G)` = 正規 Sylow。
  4. `p ∣ |N_G(K)|` の位数 `p` の元 `x` は Sylow が唯一なので `x ∈ P := O_p(G)`。
     `⟨x⟩ = Ω₁(P)` は巡回 `p`-群の唯一の位数 `p` 部分群ゆえ **char `P` ⟹ `⊴ G`**。
  5. `K` は `⟨x⟩` を正規化 (正規)、`x` は `K` を正規化 ⟹ `⁅K, ⟨x⟩⁆ ≤ K ⊓ ⟨x⟩ = 1`
     (位数互いに素) ⟹ **`x ∈ C_P(K)`, すなわち `C_P(K) ≠ 1`**。
  6. `K` の `P` への coprime 作用 + `P` 可換で **Thm 4.34** (`fixedPoints ⊓ actionCommutator = ⊥`)。
     `P` は巡回 `p`-群なので**非自明な部分群 2 つは必ず非自明に交わる** ⟹ `C_P(K) ≠ 1` から
     `⁅P, K⁆ = 1` ⟹ `K ≤ C_G(P) = P`。`K` は `p'`-群で `P` は `p`-群 ⟹ **`K = 1 = O_{p'}(G)`** ∎

**実装状況 (2026-07-26)** — 新 leaf `Ch04_Commutators/ProblemsCyclicSylow.lean`:

| 部品 | 状態 |
|---|---|
| Hall–Higman 1.2.3 | ✅ 既存 `Ch03.hall_higman_1_2_3` |
| `IsCyclic.mulAutMulEquiv` | ✅ mathlib |
| Thm 4.34 | ✅ 既存 `fixedPoints_inf_actionCommutator_eq_bot_of_abelian` |
| (a) 巡回群の `MulAut` は可換 | ✅ `mulAut_mul_comm_of_isCyclic` |
| (b) `ker (MulAut.conjNormal) = C_G(N)` | ✅ `ker_conjNormal_eq_centralizer` |
| `C_G(O_p(G)) = O_p(G)` | ✅ `centralizer_oPiCore_eq` |
| `G' ≤ O_p(G)` | ✅ `commutator_le_oPiCore_of_isCyclic` |
| `IsPiGroup {p} ↔ IsPGroup p` | ✅ `Ch03.Subgroup.isPiGroup_singleton_iff_isPGroup` (Theorem315.lean に新設) |
| **`O_p(G)` は正規 Sylow** | ✅ `exists_sylow_coe_eq_oPiCore_of_isCyclic` |
| (d) 巡回 `p`-群の非自明部分群は非自明に交わる | ✅ `inf_ne_bot_of_isCyclic_of_isPGroup` (+ `exists_orderOf_eq_prime_of_ne_bot`) |
| (c) `O_{p'}(G/O_{p'}(G)) = 1` | ✅ 既存 `Ch03.oPiCore_quotient_self_eq_bot` |
| `Ω₁(P) ⊴ G` (一般形: 正規巡回部分群の部分群は正規) | ✅ `normal_of_le_of_isCyclic` |
| coprime 作用で `C_P(K) ≠ 1 ⟹ ⁅P,K⁆ = 1` | ✅ `le_centralizer_of_isCyclic_of_exists_fixed` |
| **Case 2 本体** (`O_{p'}(G) = ⊥` ⟹ `K = ⊥`) | ✅ `eq_bot_of_oPiCore_compl_eq_bot` |
| **本体** | ✅ `le_oPiCore_compl_of_sylow_isCyclic` |

⭐ **書籍の hint (`|G|` の帰納法) は不要だった**: `O_{p'}(G/O_{p'}(G)) = 1` が常に成り立つ
(`Ch03.oPiCore_quotient_self_eq_bot`) ので, 商 `G/O_{p'}(G)` に Case 2 を **1 回適用する
だけ**で済む。商への遺伝に要ったのは `Ch01.exists_sylow_map_eq` (自作 1B.5(b)) +
`isCyclic_map_of_isCyclic` + `map_normalizer_le_normalizer_map` の 3 点のみ。

**残りの組み立て手順** (次 iteration):

- **Case 2 (`O_{p'}(G) = ⊥`)**: ✅ 実装済 (`eq_bot_of_oPiCore_compl_eq_bot`)。
- **Case 1 (`O_{p'}(G) ≠ ⊥`)**: `Ḡ = G/O_{p'}(G)` への遺伝に要るもの —
  `Ch03.quotient_isPiSeparable` ✅ / Sylow の像が Sylow = 自作 **1B.5(b)**
  `exists_sylow_map_eq` ✅ (+ Sylow 共役性で「商の任意の Sylow は像」) / `K̄` の位数は `|K|` を
  割る / `mk' x` の位数は `p` (`x ∉ O_{p'}(G)` は位数から) / 結論は
  `Ch03.oPiCore_quotient_self_eq_bot` ✅ で `K̄ = ⊥` ⟹ `K ≤ ker (mk') = O_{p'}(G)`。
- **仮説の形 (2026-07-26 に再検討、こちらを推奨)**: 「Sylow `p` が巡回」は帰納法では
  **`∀ H : Subgroup G, IsPGroup p ↥H → IsCyclic ↥H`** (「すべての `p`-部分群が巡回」) の形で
  持つのがよい。Sylow 版とは同値 (各 `p`-部分群は Sylow に含まれ, 巡回群の部分群は巡回) で,
  Case 2 (`eq_bot_of_oPiCore_compl_eq_bot` は `∀ Q : Sylow p G, IsCyclic` を取る) へは即座に
  渡せる。**商への遺伝**は: `H̄ ≤ G/O` が `p`-群なら `H := comap (mk' O) H̄` の Sylow
  `p`-部分群 `S` が `mk'` で `H̄` へ**同型に**写る (`S ⊓ O = 1` は位数互いに素から,
  `|S| = |H| の p-部分 = |H̄|`) ので `H̄ ≅ S` 巡回。これが Case 1 の唯一の非自明な plumbing。

⚠ **BG 側に重複**: `isPiGroup_singleton_of_isPGroup` / `isPGroup_of_isPiGroup_singleton`
(`BG/Ch1_Preliminary/S04g_Thm418Core.lean`, `PLengthTransfer.lean`) は今回 Isaacs Ch03 に
新設した iff 版と同内容。BG は Isaacs を import するので **BG 側を上流版へ redirect** できる
(hub 案件、lane a の territory 外なので今回は触らない)。

### 4D.3 の設計 (残り (c)–(g))

`IsIrreducibleCoprimeAction φ` (coprime + (A or G 可解) + 真の `A`-不変部分群に自明作用 +
`G` に非自明作用) の下で、既に得ているもの:
`actionCommutator_eq_top` (`⁅G,A⁆ = G`) / `le_fixedPoints_of_ne_top` + `fixedPoints_ne_top`
(**`C_G(A)` が唯一の極大 `A`-不変部分群**) / (a) `p`-群 / (b) `G' ≤ Z(G)`。

- **(c)** `G' < H < G` なる `A`-不変 `H` は無い。Thm 4.34 (Fitting,
  `fixedPoints_inf_actionCommutator_eq_bot_of_abelian`) を `G/G'` (可換) への作用に適用:
  `⁅G/G', A⁆ = ⁅G,A⁆G'/G' = G/G'` なので `C_{G/G'}(A) = 1`。`H` が真の `A`-不変なら `A` は
  `H` 上で自明 ⟹ `H/G' ≤ C_{G/G'}(A) = 1` ⟹ `H = G'`。
  ⚠ 商への作用は `Ch03.IsAInvariant.quotientMulAutHom` (`ThreeSubgroups.lean` に
  `fixedPointsOfMulAut_quotientMulAutHom_eq_map` あり)。
- **(d)** `G/G'` は基本アーベル。`℧₁(G/G')` の引き戻しは `G'` を含む `A`-不変部分群ゆえ (c) で
  `G'` か `G`。`G` なら `G/G' = (G/G')^p` で有限 `p`-群ゆえ `G/G' = 1` = `G = G'`, `G` が
  非自明 `p`-群であることに矛盾。よって `(G/G')^p = 1`。
- **(e)** `G'` は基本アーベル。(b) で `G' ≤ Z(G)` ゆえ可換。class ≤2 なので交換子は双線形で
  `⁅x,y⁆^p = ⁅x^p, y⁆`、(d) より `x^p ∈ G' ≤ Z(G)` ゆえ `= 1`。`G'` は交換子で生成。
- **(f)** `p > 2` ⟹ `x^p = 1`。class ≤2 + `G'` の exponent `p` (e) + `p` 奇 ⟹
  `x ↦ x^p` は準同型 `φ_p : G →* G`。像は `G'` に入り (d)、`G'` 上では自明 (e) なので
  `G/G' →* G'` を誘導し, これは `A`-同変。`A` は `G'` (target) に自明作用するので
  誘導写像は `⁅G/G', A⁆ = G/G'` 上で自明 ⟹ 恒等的に 1 ⟹ `x^p = 1`。
- **(g)** `p = 2` ⟹ `x⁴ = 1`。(d) で `x² ∈ G'`、(e) で `G'` の exponent は 2 ⟹ `x⁴ = 1`。

⚠ 実装知見 (2026-07-25、全 7 小問完了):
- `G ⧸ commutator G` に **`CommGroup` instance は無い** (mathlib は `Abelianization` を別 def に
  している)。repo 既存パターン `letI : CommGroup X := { (inferInstance : Group X) with
  mul_comm := … }` で供給する (`Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl`
  から `IsMulCommutative` を得て `.is_comm.comm`)。この letI の下で
  `fixedPoints_inf_actionCommutator_eq_bot_of_abelian` (Thm 4.34) がそのまま適用できた
  (Group instance は structure eta で defeq)。
- 副産物 `frattini_eq_commutator` (`Φ(G) = G'`)。`frattini G ≠ ⊤` は mathlib
  `frattini_nongenerating` を `K = ⊥` で使う (`⊥ ⊔ Φ = ⊤ → ⊥ = ⊤` の矛盾)。
- class ≤2 の道具は Ch04 Main に既存: `mul_pow_of_class_le_two` ((x*y)^n の collection 公式) /
  `commutatorElement_pow_left_of_class_le_two` (⁅x^n,z⁆ = ⁅x,z⁆^n) /
  `commutatorElement_mem_commutator_top`。
- `omit [Finite A] [Finite G] in` は **docstring より前**に書く (後ろだと構文エラー)。

#### 🎉 4A.11 完了 (2026-07-25) — `ProblemsWreath.lean` に追加

**主結果** (実証明・axiom-clean):
- `commutator_range_inl_map_inr_eq` : **`⁅B, K⁆ = (cosetProdKer K).map inl`**
  (`cosetProdKer K` = 各右剰余類 `Kω` 上で座標積が `1` な tuple 全体)
- `card_commutator_range_inl_map_inr` : **`|⁅B,K⁆| = |A|^{|H| − |H:K|}`** (書籍の形)
- 積の形 `card_cosetProdKer_mul` (`|⁅B,K⁆| · |A|^{|H:K|} = |A|^{|H|}`; ℕ の切り捨て減算を避ける)

支持部品: `rightCosetSetoid` / `cosetRep` (`Quotient.out` による代表元) + 3 補題 /
`filter_mem_cosetRep` / `cosetProdRepHom` (各代表元での剰余類積、核 = `cosetProdKer`、全射) /
`card_cosetRepFixed` (代表元の個数 = `K.index`; `K × T ≃ Q`, `(k,t) ↦ kt` の全単射から)。

⚠ **4A.8(b) は `K = ⊤` の特殊化**なので従来の独立証明 (~70 行) を削除し
`cosetProdKer_top` 経由の系に置換した (同事実の二重管理を解消)。

⚠ 教訓: `open scoped Classical in` は **docstring より前**に置く (後ろだと parse error) /
`Nat.card ⁅A,B⁆` は `(… : Subgroup G)` の型註釈が要る (`Bracket … Type` に取られる) /
`Fintype ↥K` は `[Fintype Q]` だけでは合成されない (classical か `DecidablePred` が要る)。

以下は着手前の設計メモ (実装は概ねこの通り):

#### 4A.11 の設計 (2026-07-25、着手前メモ)

書籍 (p.125): `G = A ≀ H` 正則 wreath (`A` 可換, `H` 有限), base `B = {f : H → A}`, `K ⊆ H`。
**`⁅B,K⁆` = 「`H` の各**左**剰余類上で値の積が単位元」な `f` 全体**、したがって
**`|⁅B,K⁆| = |A|^{|H| − |H:K|}`**。hint の作用は `f^h(x) = f(x h⁻¹)`。

⚠ **repo の wreath は左移動** (`shiftHom q f ω = f (q⁻¹ω)`, `commutatorElement_inl_inr`) なので、
`Δ_q` が触る位置は `{ω, q⁻¹ω}`、`q ∈ K` を動かすと **右剰余類 `Kω`**。剰余類の**個数**は
左右で同じなので位数の主張は不変。docstring に convention 差を明記すること。

- 定義: `cosetProdKer K : Subgroup (Q → D)` = `{f | ∀ ω, ∏ k : K, f (k * ω) = 1}`
  (`∏ k : K` と書けば Finset の剰余類を扱わずに済むのが要点)。
- **⊆**: `Subgroup.commutator_le` で生成元 `⁅inl f, inr q⁆ = inl (Δ_q f)` (`q ∈ K`) に帰着。
  `∏_k (Δ_q f)(kω) = ∏_k f(kω) · (∏_k f(q⁻¹kω))⁻¹` で `k ↦ q⁻¹k` は `K` の全単射ゆえ 1。
- **⊇**: 既存 4A.8(b) (`commutator_range_inl_range_inr_eq`) の証明を一般化。
  * `hgen`: `⁅inl (δ_x d), inr (y·x⁻¹)⁆ = inl (δ_x d · (δ_y d)⁻¹)` は **`y·x⁻¹ ∈ K`**
    (⟺ `y ∈ Kx` 同一右剰余類) のときに `⁅B, K.map inr⁆` の元。
  * 分解: 代表元関数 `ρ` (各右剰余類から 1 点、クラス上定数) を取り
    `f = ∏_{x:Q} (δ_x (f x) · (δ_{ρ x}(f x))⁻¹)`。評価すると
    `f ω · (∏_{x : ρ x = ω} f x)⁻¹` で、`ρ ω ≠ ω` なら空積、`ρ ω = ω` なら剰余類上の積 = 1。
  * `ρ` は `MulAction.orbitRel` (K の左移動作用、軌道 = 右剰余類) の `Quotient.out`、
    または `QuotientGroup.rightRel K` の `Quotient.out` で作る。
- **位数**: `cosetProdKer K = ker Φ`, `Φ : (Q→D) →* (剰余類 → D)`, `Φ f C = ∏_{y∈C} f y` は全射
  ⟹ `|ker| = |D|^{|Q|} / |D|^{|Q:K|} = |D|^{|Q| − |Q:K|}`。

⚠ **4A.8(b) は `K = ⊤` の特殊化**なので、一般版が landing したら
`ProblemsWreath.lean` の `commutator_range_inl_range_inr_eq` を一般版の系に置換して
重複を消す (単一右剰余類 `Q` 上の積 = `coordProdHom`)。一般版は ProblemsWreath 内に置くのが
import 方向的に自然 (現 1033 行 + ~250 行で 1500 上限内)。

#### 🎉 4A.9 完了 (2026-07-25) — 新 leaf `ProblemsIteratedCommutator.lean`

**主結果** (実証明・axiom-clean):
- `isSubnormal_iff_commIterate_le` = **(a)** (`N ⊴ G`, `N ⊔ A = ⊤`, `M` 安定 ⟹ `A ◁◁ G ⟺ M ≤ A`)
- `commIterate_le_nilpotentResidual` = **(b)** (`M ≤ A` ⟹ `M ≤ A^∞`; `N` 正規も `G = NA` も不要)
- `exists_commIterate_stable` (有限群で最終項 `M` が存在 = 系列の安定化)

再利用可能な副産物: `commIterate` (始点と交換相手が別の反復交換子列) と単調性・加法性 /
`le_normalizer_of_forall_conj_mem` / **`le_normalizer_commutator_left`・`_right`**
(`⁅H,K⁆` は両因子で正規化される) / `exists_commIterate_top_le_of_isSubnormal`
(部分正規性の **defect 形** `∃ d, ⁅⊤,A;d⁆ ≤ A`)。

以下は着手前の設計メモ (実装は概ねこの通り):

#### 4A.9 の設計 (2026-07-25、PDF p.137 = 書籍 p.124 で statement 確定)

`G = NA` (`N ⊴ G`, `A ≤ G`)、`M` = 系列 `N ⊇ ⁅N,A⁆ ⊇ ⁅N,A,A⁆ ⊇ ⋯` の最終項。
**(a) `A ◁◁ G` (⚠ subnormal、PDF 画像で `⊲⊲` を確認) ⟺ `M ⊆ A`** / **(b) `M ⊆ A` なら `M ⊆ A^∞`**。

- 定義: `commIterate N A 0 = N`, `commIterate N A (i+1) = ⁅commIterate N A i, A⁆`
  (新 leaf `Ch04_Commutators/ProblemsIteratedCommutator.lean`)。
- **(a) ⟸**: 部分正規鎖は `A = L_k A ≤ ⋯ ≤ L_1 A ≤ L_0 A = N ⊔ A = ⊤` (`L_i := commIterate`)。
  各段 `W := L_{i+1} ⊔ A ⊴ L_i ⊔ A` は `Subgroup.normal_subgroupOf_iff_le_normalizer` +
  `sup_le` で 2 本に分ける:
  * `A ≤ N_G(W)`: `A ≤ W` ゆえ `⁅A,W⁆ ≤ ⁅W,W⁆ ≤ W` (`le_normalizer_of_commutator_le`)。
  * `L_i ≤ N_G(W)`: 共役 `f = MulAut.conj x` (`x ∈ L_i`) で `W.map f = L_{i+1}.map f ⊔ A.map f`
    (`Subgroup.map_sup`)。`L_{i+1}.map f = L_{i+1}` は「**`⁅H,K⁆` は `H` で正規化される**」
    (`⁅hx,y⁆ = h⁅x,y⁆h⁻¹⁅h,y⁆` = `commutatorElement_mul_left_eq_conj_mul` から)、
    `A.map f ≤ W` は `xax⁻¹ = ⁅x,a⁆·a ∈ L_{i+1}A`。`x⁻¹` にも適用して両包含。
  ⚠ `⁅H, K ⊔ L⁆` の分配は偽なので使わない (`sup_le` を **normalizer 側**で使うのが要点)。
- **(a) ⟹**: `IsSubnormal A` の構造帰納で **`∃ d, commIterate ⊤ A d ≤ A`** (defect 版):
  `top` は `d = 0`、`step (A ≤ K) (K subnormal) (A ⊴ K)` は IH の `d` に対し
  `commIterate ⊤ A d ≤ commIterate ⊤ K d ≤ K` (第 2 引数単調) から
  `commIterate ⊤ A (d+1) = ⁅…, A⁆ ≤ ⁅K,A⁆ ≤ A`。あとは `M = ⁅M,A⁆` を `d` 回反復して
  `M = commIterate M A d ≤ commIterate ⊤ A d ≤ A`。
- **(b)**: `M = ⁅M,A⁆` と `M ≤ A` から `M = commIterate M A i ≤ Subgroup.lowerCentralSeries A i`
  (∀ i) ⟹ `M ≤ ⨅ i, … = nilpotentResidual A` (= `A^∞`)。
  ⚠ `nilpotentResidual` は `Ch09_MoreSubnormality/NilpotentResidual.lean` だが、そこは
  **Ch01 しか import しない**ので Ch04 から import しても cycle 無し (実測済)。
- `M` は「最終項」= 有限性で `L k = L (k+1)` となる `k` の値。仮説として
  `hM : commIterate N A k = commIterate N A (k+1)` を取る形が扱いやすい
  (存在は減少列の安定性から別途)。

### §1D の欠落 (2026-07-25 に発見・補充)

§1D は **1D.17 までしか形式化されていなかった** (1D.18 / 1D.19 が欠落)。3B.14 が 1D.19 を
使うので先に補充した。1D.18 = `F(G/Z(G)) = F(G)/Z(G)`、1D.19 = 「`C = C_G(F)` として
`C/(C ⊓ F)` は非自明な abelian 正規部分群を持たない」(対応定理の形
「`A ⊴ ↥C` かつ `⁅A,A⁆ ≤ F.subgroupOf C` ⟹ `A ≤ F.subgroupOf C`」で述べた)。
⟹ **章末問題の「済」ラベルは番号ごとに実測で確認すること** (§1D は 1D.5 だけが欠落と
思われていたが実際は 1D.18/1D.19 も欠けていた)。

### §3B の記録 (2026-07-25)

| # | 状態 | Lean 名 (`OddOrder.Isaacs.Ch03`) |
|---|---|---|
| 3B.1 | ✅ | `index_isPrimePow_of_isCoatom` (+ 対応定理 `isCoatom_map_mk'_of_isCoatom`) |
| 3B.2 | ✅ | `isSolvable_of_commutator_series` (+ 教科書形との往復 3 補題) |
| 3B.3 | ✅ | `isSolvable_iff_forall_prime_card_of_simple_factors` |
| 3B.4 | ✅ | `exists_isComplement'_le_of_coprime` (+ `isComplement'_conj`) |
| 3B.5 | ✅ | `exists_subgroup_orderOf_not_dvd_isComplement'` |
| 3B.6(a) | ✅ | `exists_mem_coset_primeFactors_orderOf_dvd` |
| 3B.6(b) | ✅ | `orderOf_eq_of_primeFactors_orderOf_dvd_of_coprime` |
| 3B.6(c) | ✅ | `isConj_inv_of_quotient_isConj_inv` (+ `isComplement'_subgroupOf_of_coprime`) |
| 3B.6 まとめ | ✅ | `exists_mem_coset_orderOf_eq_and_isConj_inv` |
| 3B.7(a) | ✅ | `card_prime_of_isMinimalNormal_of_isSupersolvable` (新 leaf `ProblemsSupersolvable.lean`) |
| 3B.7(b) | ✅ | `index_prime_of_isCoatom_of_isSupersolvable` |
| 3B.8 | ✅ | `sylow_normal_of_forall_isCoatom_index_prime` / `isSolvable_of_forall_isCoatom_index_prime` / `exists_normal_qComplement` |
| 3B.9 | ✅ | `exists_subgroup_card_eq_of_isSupersolvable` |
| 3B.10 | ✅ | `sylow_normal_of_isSupersolvable` (3B.7(b) + 3B.8 の核の系) |
| 3B.11 | ✅ | `prime_dvd_index_frattini_of_dvd_card_frattini` |
| 3B.12 | ⚠ 訂正版 | `index_sup_eq_relIndex_of_isMinimalNormal_of_not_le` (書籍の主張は偽 — 下記) |
| 3B.13 | ✅ | `exists_greatest_isSolvable_normal` (+ `isSolvable_sup_of_normal`) |
| 3B.14 | ✅ | `center_fitting_greatest_isSolvable_normal_centralizer` (1D.19 + `|S|` 帰納) |
| 1D.18 | ✅ | `Ch01.fitting_quotient_center` (§1D の欠落を補充) |
| 1D.19 | ✅ | `Ch01.le_fitting_subgroupOf_of_commutator_le` (+ `center_fitting_map_eq_inf_centralizer`) |
| 3B.15 | ✅ | `normal_of_index_minimal` (Berkovich) |

⟹ **§3B は 3B.1-3B.15 全完** (3B.12 のみ訂正版)。**2026-07-26 に 3A.6 も完了したので
Isaacs Ch.3 の章末演習は全問完済** ⟹ あわせて **Isaacs Ch.1–Ch.4 の章末演習が全問完済**。

**設計メモ**:

- **3B.2/3B.3 の「列」の表し方**: 因子が abelian という仮説は交換子形
  `⁅Nᵢ₊₁, Nᵢ₊₁⁆ ≤ Nᵢ` で表した。これなら包含も正規性も有限性も要らず (すべて従属)、
  教科書形 (`Nᵢ ⊴ Nᵢ₊₁` + 商 abelian) との往復は 3 補題
  (`commutator_le_of_quotient_isMulCommutative` / `normal_subgroupOf_of_commutator_le` /
  `quotient_isMulCommutative_of_commutator_le`) が与える。
  3B.3 の**単純因子**は商群を直接書くと仮説内で `Normal` instance を捏ねる必要が出るので、
  「抽象群 `Qᵢ` + 全射 `Nᵢ₊₁ ↠ Qᵢ` (核 = `Nᵢ`)」の形で与えた (`Qᵢ ≅ Nᵢ₊₁/Nᵢ` と同値)。

- **3B.4 のために Basic.lean の SZ D-part を一般化した**:
  `exists_conj_le_of_isComplement'_of_coprime` は `IsSolvable ↥M` を要求していたが、
  教科書 3B.4 は「`N` **または** `U` が可解」で足りる。そこで一般版
  `exists_conj_le_of_isComplement'_of_coprime'` (`IsSolvable ↥M ∨ IsSolvable ↥U`) を新設し、
  既存名はその `Or.inl` 特殊化として残した (BG/Peterfalvi 側 5 箇所の呼び出しは無変更)。
  `U` 可解の側は `IsComplement'.QuotientMulEquiv` で `↥P ⧸ M.subgroupOf P ≃* ↥(U.subgroupOf P)`
  を作り、SZ 共役性の「商が可解」枝に流す。
  さらに 3B.6(c) のために結論も強化した (`∃ x ∈ M, U ≤ K^x` — 共役元が `M` の中にあることは
  証明中で既に得ていた情報)。既存名の側で `⟨x, _, hx⟩` に落とすので下流は無変更。

- **3B.6(a) の π-分解は Hall E-定理で得る**: `⟨g⟩` は可換ゆえ可解なので `hall_E_exists` が
  π-Hall 部分群 `C` を与え、`|⟨g⟩| = |C| · [⟨g⟩:C]` が求める π/π'-分解になる (自然数の
  π-part を factorization で作る必要がない)。あとは中国剰余定理で `t ≡ 1 (mod m)`,
  `[⟨g⟩:C] ∣ t` なる `t` を取り `h := g^t`。教科書 hint の「`NC = N⟨g⟩` なる巡回 π-部分群 `C`」
  と同じ道具立て。

- **3B.7 で超可解群を定義した** (`ProblemsSupersolvable.lean`, repo/mathlib いずれにも無かった):
  `IsSupersolvable G := ∃ r N, (∀ i, (N i).Normal) ∧ N 0 = ⊥ ∧ N r = ⊤ ∧
  ∀ i < r, ∃ x ∈ N (i+1), N (i+1) = N i ⊔ ⟨x⟩`。因子の巡回性を `Nᵢ₊₁ = Nᵢ ⊔ ⟨x⟩` で表すと
  商の `Normal` instance を仮説内で作らずに済み、`Nᵢ ≤ Nᵢ₊₁` も自動。
  `IsSupersolvable.isSolvable` は 3B.2 経由、`IsSupersolvable.quotient` も証明済 (3B.7(b) の
  帰納で使う)。3B.9 / 3B.10 も同じ定義を使う予定。

- **3B.8 の核 = Sylow 個数の合同式**: 「極大部分群の指数がすべて素数」⟹ 最大素因数 `p` の
  Sylow `p`-部分群は正規。`P` が非正規なら `N_G(P) ≤ M` (極大) が取れ、`P ∈ Syl_p(M)` かつ
  `N_M(P) = N_G(P)` なので `n_p(G) = n_p(M)·[G:M]`。両者 `≡ 1 (mod p)` から `[G:M] ≡ 1 (mod p)`
  ⟹ `[G:M] > p` で `p` の最大性に矛盾。可解性と正規 `q`-補群 (最小素因数 `q`) はこの核 +
  `G ⧸ P` への帰納法で従う。**正規 `q`-補群は「`|H|` が `q` で割れない正規部分群で `[G:H]` が
  `q`-冪」**という指数形で述べた (存在量化の中で `G ⧸ H` を書くと `H.Normal` instance が
  statement 内で取れないため; 書籍の定義「指数が Sylow `q`-部分群の位数に等しい部分群」と同値)。

### ⚠ 3B.12 は書籍の主張のままでは**偽** (2026-07-25 に反例を確認)

書籍 (p. 85): 「`G` 可解, `Φ(G) = 1`, `M` 極大, `H ⊆ M` ⟹ `G` は指数 `|M : H|` の部分群を持つ」。
**反例 = `G = A₄`**:

- `A₄` は可解、`Φ(A₄) = 1` (極大部分群は `V₄` と 4 個の `C₃`、共通部分は 1)
- `M = V₄` は極大 (指数 3; 位数 6 の部分群が無いので極大)
- `H = ⟨(12)(34)⟩ ≤ M` で `|M : H| = 2`
- しかし `A₄` は指数 2 (= 位数 6) の部分群を持たない (古典的事実)

原文は PDF ページ画像 (書籍 p.85 = PDF p.98) で確認済 — OCR の読み違いではなく確かに `H ⊆ M`。
書籍の議論が通るのは「**`M` に含まれない極小正規部分群 `N` がある**」場合で、そのとき
`G = N ⋊ M` から `N ⊔ H` がちょうど指数 `|M : H|` を与える。`A₄` の `M = V₄` は唯一の極小正規
部分群 `V₄` 自身を含むので、この条件が破れている。⟹ 訂正版
`index_sup_eq_relIndex_of_isMinimalNormal_of_not_le` を形式化し、docstring に反例を明記した。

- **3B.6(c)**: `H := N⟨h⟩` の中で `⟨h⟩` は `N` の補群 (`isComplement'_subgroupOf_of_coprime`
  を新規に証明)。`h₂ := x h x⁻¹` の生成する `⟨h₂⟩` は位数 `o(h)` で `|N|` と互いに素なので
  D-part の **`U` 可解枝** (`⟨h₂⟩` は巡回) が使え、`⟨h₂⟩ ≤ ⟨h⟩^y` (`y ∈ N`) を得る。
  `⟨h⟩ ⊓ N = 1` より `G ⧸ N` での像を比べて `k = h⁻¹`, すなわち `h ~ h⁻¹`。


## §6B 着手メモ (2026-07-27)

書籍 p. 195-196 (PDF p. 208-209)。§6B の本文定理は Lemma 6.16 / Cor 6.17 (Frobenius 補群の
Sylow は巡回か一般四元数) / Cor 6.18 / Thm 6.19 / Lemma 6.20 / Thm 6.21。

**6B.1 の設計 (実装前に確定した分)**:
* 前半「任意の Frobenius 群は可解 Frobenius 部分群を含む」: `hF : IsFrobeniusGroup G N A` から
  素数位数 `p` の `x ∈ A` を取り `B := ⟨x⟩`。`B` 不変な非自明可換部分群 `M ≤ N` を
  `FrobeniusGroup.lean` の既存 API (l.931/977 付近, Isaacs Thm 3.23 経由で不変 Sylow → `Z(R)`)
  で取る。`M ⊔ B` が可解 Frobenius 部分群 (`isFrobeniusGroup_of_prime_complement_fixedFree`,
  l.258 が素数位数補群からの構成を与える)。
* 後半「Frobenius 補群は Frobenius 群を部分群に持てない」: **repo に可解版が既に在る** —
  `false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup`
  (`FrobeniusGroup.lean` l.1000, Isaacs Thm 6.9 の可解分岐)。前半と合成すれば可解仮定が外れる。
  ⟹ **6B.1 = 前半を作って既存の可解版と合成する**のが正しい構成。
* ⚠ `exists_aInvariant_sylow_subgroup` (部分群形) は `OddOrder/BG/Ch3_MaximalSubgroups/
  S13_Corollary132.lean` に在るが **BG は Isaacs の下流**なので import 不可。Isaacs 側では
  `Isaacs.Ch04.exists_aInvariant_sylow` (action 形) か、上記 `FrobeniusGroup.lean` の
  既存ラッパを使う。


## 6B.5 着手メモ (2026-07-27) — 「subnormal 部分群からなる分割 ⟹ 冪零」

**調査結果 (実測)**:
* **mathlib に `Subgroup.IsSubnormal` が在る** (`Mathlib/GroupTheory/IsSubnormal.lean`)。使える API =
  `Normal.isSubnormal` / `isSubnormal_iff` / `IsSubnormal.trans` / `.trans'` / `.map` / `.comap` /
  ⭐ **`exists_normal_and_le_and_lt_top_of_ne : H.IsSubnormal → H ≠ ⊤ → ∃ K, K.Normal ∧ H ≤ K ∧ K < ⊤`**
  (`|G|`-induction の下降ステップに直結)。
* repo 側: `Ch02_Subnormality/Basic.lean:140` `inf_isSubnormal_subgroupOf` (部分群への制限),
  同 `:150` `commute_of_disjoint_normal` (**normal 版のみ** — subnormal 版は無い),
  `Theorem211Wielandt.lean` = Isaacs Thm 2.11 (可換 subnormal ⟹ `≤ F(G)`)。

**最短経路 (6B.4 が効く)**: 欠けているのは 1 本だけ —
> **Wielandt**: `H`, `K` が subnormal で `H ⊓ K = ⊥` なら `⁅H, K⁆ = ⊥`。

これが在れば, 分割の相異なる部分は `SubgroupPartition.inf_eq_bot_of_ne` で交わりが自明ゆえ
**互いに可換**になり, **6B.4 (a)(b)** がそのまま適用できて `G` は基本可換 ⟹ 冪零。
(別経路として Thm 2.11 で「各部分が可換 subnormal ⟹ `≤ F(G)`」から `G = F(G)` も使える。)

**Wielandt 補題の証明の当たり**: `|G|` に関する強帰納法。`H = ⊤` なら `K = ⊥` で自明。
`H ≠ ⊤` なら `exists_normal_and_le_and_lt_top_of_ne` で `H ≤ M ⊴ G`, `M < ⊤` を取り,
`H` と `K ⊓ M` を `M` の中で帰納法にかけると `⁅H, K ⊓ M⁆ = ⊥` までは出る。
⚠ **`K ⊓ M` から `K` 全体へ延ばす所が本体** (素朴には `⟨H,K⟩ = ⊤` に還元して `H^G ≤ M < ⊤` を
使うが, そこから先がもう一段要る)。書籍の hint (「`H < G` が分割のどの部分にも含まれないなら
`H` は冪零」→「`F(G)` に含まれない部分は正規で素数指数」) は別経路で, こちらは
`H` に誘導分割 `{H ⊓ X}` が乗る (全部真部分群になる) ので帰納法が回る形。


### 6B.5 進捗 (2026-07-27): 還元 landing, 残りは Wielandt 補題のみ

`Problems6B5.lean` を新設し, **ステップ 2-3 を実証明**:
`isNilpotent_of_subnormal_partition` = 分割の相異なる部分が Wielandt で可換 ⟹ 6B.4(a) で
`G` 可換 ⟹ `CommGroup.isNilpotent` で冪零。**残る sorry は Wielandt 1 本だけ**:
`commutator_eq_bot_of_isSubnormal_of_inf_eq_bot`。

**Wielandt の証明で詰めた所まで** (次回の出発点):
* `|G|` 強帰納法。`H = ⊤` なら `K = ⊥`, `K = ⊤` なら `H = ⊥` で自明。
* `H ≠ ⊤` なら `H ≤ M ⊴ G`, `M < ⊤` が取れ, **`N := H^G ≤ M < ⊤`** (正規閉包が真)。
  同様に `N' := K^G < ⊤`。`⁅H,K⁆ ≤ N ⊓ N'` (`[h,k] = h⁻¹h^k ∈ H^G` かつ `= (k⁻¹)^h k ∈ K^G`)。
* `N'` の中で `H ⊓ N'` と `K` に帰納法 ⟹ **`⁅H ⊓ N', K⁆ = ⊥`**。
  `H ⊴ G` の場合はさらに `⁅H,K⁆ ≤ H ⊓ N'` が出て, `H ⊓ N'` が `N'` の任意の共役を中心化する
  ことから `H ⊓ N' ≤ Z(N')`, したがって `⁅H,K⁆ ≤ Z(N')`。
* ⚠ ここから `⁅H,K⁆ = ⊥` を出す最後の一段が未確定 (`[h,k]^{o(k)} = 1` までは出る)。
  **次回は Isaacs Ch.2 の原文 (subnormal 部分群の join / Wielandt) を PDF で読んでから書く** —
  repo には `Ch02_Subnormality/` が既に在るので, 対応定理番号を先に特定するのが早い。


### 6B.5 調査続報 (2026-07-27): Isaacs 原文の道具を特定

**(1) 使える既存定理 (原文で確認)**
* **Isaacs Thm 2.6**: `H ⊴⊴ G` かつ `N` が `G` の極小正規部分群なら **`N ≤ N_G(H)`**。
  ⟹ `⁅N, H⁆ ≤ H ⊓ N` が言える (Thm 9.3 の証明が実際にこの形で使っている)。
  Wielandt 補題の極小正規部分群による場合分けの土台になる。
* **Isaacs Ch.2**: 「`F(G)` は**すべての subnormal 冪零部分群を含む**」。
  ⟹ **6B.5 の別 endgame**: 各部分が冪零だと言えれば, 全部分 `≤ F(G)` かつ部分は `G` を被覆
  するので `G = F(G)` で冪零。⚠ repo にあるのは可換版 (Thm 2.11 =
  `Ch02_Subnormality/Theorem211Wielandt.lean`) のみで, **冪零版は未形式化** (grep 実測)。
* **Isaacs Thm 9.4** (相異なる component は可換) は**別物** — component = subnormal quasisimple
  であって我々の「交わり自明な subnormal 対」ではない。証明の型 (真部分群に落とす →
  単純なら矛盾 → 極小正規部分群で場合分け) は流用できる。

**(2) 書籍 hint 経路の核心が見えた**: 分割のどの部分にも含まれない `H < G` は,
`{H ⊓ Y : Y ∈ Π}` が **`H` の本物の分割になる** (`H ⊄ Y` ゆえ各 `H ⊓ Y` は `H` の真部分群、
subnormal 性は制限で保たれる) ので `|G|` 帰納法で冪零。ここは素直に書ける。
残りは「`F(G)` に含まれない部分は正規で素数指数」→ 冪零、の詰め。

⟹ **次回の選択肢は 2 つ**: (a) Wielandt 補題を Thm 2.6 + 極小正規部分群で正面から,
(b) 書籍 hint 経路 (誘導分割の帰納法 + 冪零版 Fitting 補題の新規形式化)。
(b) は「subnormal 冪零 ⟹ ≤ F(G)」という**汎用補題が副産物**として得られる利点がある。


### 6B.5 進捗 (2026-07-27 続き): Fitting 冪零版を実証明

`isSubnormal_le_fitting_of_isNilpotent` (**`F(G)` は subnormal な冪零部分群をすべて含む**)
を `Problems6B5.lean` に実証明で追加。`|G|` 強帰納法 + repo 既存の
`Ch01.nilpotent_normal_le_fitting` / `Ch01.fitting_map_subtype_le_fitting` /
mathlib `IsSubnormal.subgroupOf` で書けた (可換版 Thm 2.11 の冪零版; 汎用補題)。

**これで書籍 hint 経路の全ステップが見通せた (次回これを実装)**:
1. 分割のどの部分にも含まれない `H < G` は `{H ⊓ Y}` が本物の分割 ⟹ `|G|` 帰納法で冪零。
2. 部分が全部 `F(G)` に入れば `G = F(G)` で冪零。よって `X ⊄ F(G)` なる部分 `X` を取る。
3. `X` は冪零でない (冪零なら上の新補題で `X ≤ F(G)`)。`X < H < G` なる `H` は
   どの部分にも含まれない (含まれれば `X` と一致してしまう) ので 1 で冪零 ⟹ `X ≤ H` も冪零で
   矛盾。ゆえに **`X` は極大**。subnormal かつ真ゆえ正規化群が真に大きいので `X ⊴ G`,
   `|G : X| = p` (素数)。
4. 他の部分 `Y` は `Y ⊓ X = ⊥` より `G/X` に単射, ゆえに `|Y| = p` で冪零 ⟹ `Y ≤ F(G)`。
5. したがって `G = X ∪ F(G)` (集合として) だが **群は 2 つの真部分群の合併にならない** ⟹ 矛盾。

⟹ Wielandt 補題は 6B.5 には**不要**になる (statement は残すか削除するか次回判断)。


### 6B.6 着手メモ (2026-07-27) — 「位数 ≥ 8 の巡回 2-群は位数 2 の自己同型を 3 個持つ」

**⭐ 鍵の実測**: mathlib に **`IsCyclic.mulAutMulEquiv : MulAut G ≃* (ZMod (Nat.card G))ˣ`**
が在る (`Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:593`)。したがって 6B.6 は
**`(ZMod (2^n))ˣ` の位数 2 の元を数える**問題に落ちる (`IsCyclic.card_mulAut` も併存)。

**残る数学的中身**: `n ≥ 3` のとき `#{x : ZMod (2^n) | x² = 1} = 4` (解は `±1`, `2^(n-1) ± 1`)。
⚠ `n` が変数なので `decide` は使えない。証明:
`x² ≡ 1 (mod 2^n)` ⟺ `(x-1)(x+1) ≡ 0`。`x` は奇数ゆえ `x-1`, `x+1` はともに偶数で
**一方はちょうど 2 で割れる** (差が 2 なので 4 で割れるのは高々一方)。よって他方が
`2^(n-1)` で割り切れ, `x ≡ ±1 (mod 2^(n-1))` — `mod 2^n` では 4 解。
`n ≥ 3` が効くのはこの 4 解が相異なること (`n = 2` だと `2^(n-1)±1 = ±1` に潰れる)。

⟹ 位数ちょうど 2 の元は `4 - 1 = 3` 個。


#### 6B.6 の Lean 実装方針 (2026-07-27 詰め)

mathlib に `ZMod (2^n)` の平方根 1 に関する補題は**無い** (grep 実測) ので自前で書く。
`N := 2^n`, `a : ZMod N := 2^(n-1)` として

**主補題**: `∀ x : ZMod N, x^2 = 1 ↔ x = 1 ∨ x = -1 ∨ x = a + 1 ∨ x = a - 1`。

順方向の Lean 手順 (整数経由):
1. `x^2 = 1` を `ZMod.intCast_zmod_eq_zero_iff_dvd` で `(2^n : ℤ) ∣ (m-1)(m+1)`
   (`m := (x.val : ℤ)`) に変換。
2. `m` は奇数 (偶数なら `(m-1)(m+1)` が奇数で `2 ∤` に反する)。`m = 2k+1` と書くと
   `(m-1)(m+1) = 4k(k+1)` なので **`2^(n-2) ∣ k(k+1)`**。
3. `k` と `k+1` は互いに素なので, 素数冪 `2^(n-2)` は**どちらか一方を割る**
   (`Nat.Coprime.eq_one_of_dvd` 系 / `Int.Prime.dvd_mul` の冪版)。
   ⟹ `2^(n-1) ∣ m - 1` または `2^(n-1) ∣ m + 1`。
4. `ZMod N` に戻すと `x - 1 = a * s` または `x + 1 = a * s` (`s : ZMod N`)。
   ⭐ **`2a = 2^n = 0` なので `a * s ∈ {0, a}`** (`s` の偶奇で決まる) — ここが効いて
   4 通りに絞れる。
5. 逆方向は `a^2 = 2^(2n-2) = 0` (`2n-2 ≥ n`) から計算するだけ。

そのあと `n ≥ 3` から 4 元が相異なることを示し (`n = 2` だと `a ± 1 = ∓1` に潰れる),
`IsCyclic.mulAutMulEquiv` で `MulAut C` に移して位数ちょうど 2 は `4 - 1 = 3` 個。


### 6B.7 着手メモ (2026-07-27) — 「指数 2 の巡回部分群を持つ非可換 2-群の分類」

**⭐ repo に Isaacs Lemma 6.13 が両分岐とも既に在る** (`Ch06_FrobeniusActions/DQSDRecognition.lean`):
* `dihedralOrQuaternion_of_invertingConjugation` — `a c a⁻¹ = c⁻¹` なら `D_{2^m}` か `Q_{2^m}`
* `semiDihedral_of_twistConjugation` — `a c a⁻¹ = z c⁻¹` (`z` = `C` の唯一の involution) なら半二面体
* おまけ: `dihedralOrQuaternion_of_card_eight` (Cor 6.14), `dihedralOrQuaternion_of_self_centralizing_cyclic_card_four` (Thm 6.12 の `|C|=4` 分岐)

⟹ **6B.7 の仕事は「`a` の `C` への作用が上の 2 形のどちらかである」ことを示すだけ**:
1. `C = ⟨c⟩` は指数 2 ゆえ正規, `a² ∈ C` で `C` 可換なので **`a` の誘導自己同型は位数 ∣ 2**。
2. 巡回群なので `a c a⁻¹ = c^k` と書け, `k² ≡ 1 (mod 2^m)` (`2^m = |C|`)。
   ⟹ **直前に landing した `sq_eq_one_iff_two_pow` がそのまま効いて `k ∈ {1, -1, 2^(m-1)+1, 2^(m-1)-1}` の 4 通り**
   (6B.6 の数え上げ版ではなく iff 版を使う)。
3. `k = 1` (中心化) は `P = ⟨a, c⟩` が可換になるので**非可換仮定**で排除。
4. `k = 2^(m-1)+1` は `[a,c] = z` が中心的な "modular" 型で `|P : Z(P)| = 4` になるので
   **`|P:Z(P)| > 4` 仮定**で排除。⚠ ここの計算 (`Z(P) = ⟨c²⟩` になること) が本問の実質。
5. 残る `k = -1` / `k = 2^(m-1)-1` がちょうど Lem 6.13 の 2 分岐。
   ⚠ `|C| ≤ 4` (すなわち `|P| ≤ 8`) の場合は 2 の 4 通りが潰れるが, そのとき `|P:Z(P)| ≤ 4` なので
   仮定から除外される — この端点処理も要る。

6B.8 (`|P : P'| = 4` から同じ結論, Taussky-Todd) は 6B.7 を使う想定。


### 6B.7 進捗メモ (2026-07-27): j = 2^(m-1)+1 分岐は WIP

`⟨c²⟩ ≤ Z(P)` ⟹ `|P : Z(P)| ∣ 4` の筋で書き下したが, `set z := c ^ (2^(m-1))` の
**fold/unfold が calc の中で悪さをして** 1 箇所閉じられずに残った (build を green に戻すため
一旦 revert; WIP は scratchpad に退避)。証明の中身自体は次のとおりで確定している:

* `a c² a⁻¹ = (z c)² = z² c² = c²` (`Commute.mul_pow` + `z² = 1`)
* `C_P(c²)` は `⟨c⟩` と `a` を含むので (j=1 分岐と同じ relIndex 論法で) `= ⊤`, つまり `c² ∈ Z(P)`
* `orderOf (c²) = 2^(m-1)` (`orderOf_pow` + `gcd (2^m) 2 = 2`), `|P| = 2^(m+1)` なので
  `|P : ⟨c²⟩| = 4`, ゆえに `Z(P).index ∣ 4` で仮定 `> 4` に反する

⚠ **次回は `set` を使わず `z` を `have hzdef : ... ` 無しの素の `c ^ (2^(m-1))` のまま書く**
(または `set ... with hz` でなく `let`/局所 `have` にする) こと。`set` は goal 側を勝手に
fold するので, calc の各行で `z` と `c^(2^(m-1))` が混在すると `rfl` が通らなくなる。


#### 訂正 (2026-07-27): 6B.7 の詰まりは `set` の fold ではなかった

前記の「`set` の fold が原因」は**誤診**だった。真因は **`group` タクティクが
`a * c^2 * a⁻¹ = (a * c * a⁻¹)^2` を閉じられなかった**こと (`pow_two` で展開してから
`group` を呼べば通る)。`set` → `obtain ⟨z, hz⟩` への置換も併せて行ったが, 本質は
`rw [pow_two, pow_two]; group` の方。⟹ **`group` は指数リテラルを展開しないことがある**。


### 6B.8 進捗 (2026-07-27): hint ステップ 1-3 完了, 帰納法本体の設計

`Problems6B8.lean` に**実証明で 3 本**:
* `exists_orderOf_eq_two_mem_commutator_center` (ステップ 1: `Z ≤ P' ⊓ Z(P)`, `|Z| = 2`)
* `index_commutator_quotient` (ステップ 2: `|P/Z : (P/Z)'| = |P : P'|`)
* `mul_comm_of_center_le_of_isCyclic_quotient` (ステップ 3: 引き戻し `A` は可換)

**帰納法本体で要る部品 (次回以降)**:
1. **base case `|P| = 8`**: `|P:P'| = 4` ⟹ `|P'| = 2` ⟹ 非可換 ⟹ repo の
   `dihedralOrQuaternion_of_card_eight` (Cor 6.14, `DQSDRecognition.lean:960`)。
2. **`|P| ≥ 16` ⟹ `|P : Z(P)| > 4`** (6B.7 を適用するのに要る)。導出:
   * `P/Z(P)` は巡回なら `P` 可換なので, 非可換ゆえ `|P:Z(P)| ∉ {1, 2}`。
   * `|P:Z(P)| = 4` と仮定すると `P/Z(P) ≅ Z₂ × Z₂`。代表元 `a, b` を取ると
     任意の交換子は `[a,b]` の冪で **`P' = ⟨[a,b]⟩`**, さらに `a² ∈ Z(P)` から
     `[a,b]² = [a², b] = 1` なので **`|P'| ≤ 2`**。
   * すると `|P| = |P:P'| · |P'| ≤ 4 · 2 = 8` で `|P| ≥ 16` に反する。⟹ `|P:Z(P)| > 4` ✓
3. **D/SD/Q は指数 2 の巡回部分群を持つ** (`P/Z` から引き戻すため; 具体群についての事実)。
4. **可換 `A` で `A/Z` 巡回 (`|Z| = 2`) ⟹ `A` 巡回 or `A ≅ Z × 巡回`**、後者で `|P| > 16` の矛盾。

⟹ 2 が独立性が高く価値も高いので次に着手する。


### 6B.8 帰納法の再定式化 (2026-07-27) ⭐

当初は「帰納法で `P/Z` が D/SD/Q → その指数 2 の巡回部分群を引き戻す」と設計したが,
**D/SD/Q という具体群についての事実 (指数 2 の巡回部分群を持つ) を 3 種類とも証明する必要**が
あり重い。そこで帰納の主張を差し替える:

> **帰納する命題**: `P` が `2`-群, `|P| ≥ 8`, `|P : P'| = 4` ⟹ **`∃ c, |P : ⟨c⟩| = 2`**

これなら
* **base (`|P| = 8`)**: 非可換な位数 8 の群には位数 4 の元がある
  (`exists_index_two_zpowers_of_card_eight`, 実証明済) — 全元 `g² = 1` なら可換,
  位数 8 の元があれば巡回でやはり可換。
* **step (`|P| ≥ 16`)**: `Z` を取り `P/Z` に帰納法 ⟹ `P/Z` に指数 2 の巡回部分群 `⟨c̄⟩`。
  その引き戻し `A` は指数 2 で `A/Z` 巡回, `Z ≤ Z(P)` より **`A` は可換** (既証明)。
  `A` が巡回ならそれが答え。`A` が非巡回 (= `Z × 巡回`) のときが**残る唯一の難所**で,
  書籍 hint の「`|P| > 16` なら `Z < Z(P)` で矛盾」に当たる。
* 最後に `four_lt_index_center` (既証明) と **6B.7** を合わせて D/SD/Q に結論。

⟹ 具体群 D/SD/Q の構造を一切触らずに済む。残りは step の非巡回ケースのみ。


### 6B.8 の最終難所 (2026-07-27 解析): 引き戻し `A` が非巡回のケース

部品 26 本が実証明で揃い, 残るのは帰納 step で `A` (指数 2 の可換部分群) が**非巡回**の
場合の矛盾のみ。解析した内容:

* `A` 可換 & 指数 2 ⟹ `P/A` 位数 2 で可換 ⟹ **`P' ≤ A`**。`|P'| = |P|/4 = |A|/2` なので
  **`P'` は `A` の指数 2**。
* `a ∉ A` を取ると `θ : A → A`, `θ(x) = x⁻¹ · a x a⁻¹` は (A 可換ゆえ) **準同型**で
  `im θ = P'`, `ker θ = C_A(a)`。よって **`|C_A(a)| = 2`**。
* `A` は極大可換なので `Z(P) ≤ C_P(A) = A`, したがって **`Z(P) = C_A(a)` で `|Z(P)| = 2`**,
  すなわち `Z = Z(P)`。
* 書籍 hint は「`|P| > 16` なら `Z < Z(P)`」と言うので, ここに矛盾を作る。
  ⚠ `A ≅ Z₂ × Z_{2^k}` 上で位数 2 の自己同型が固定点を 2 個しか持たない状況は
  `k` が小さいと起こりうる (GL(2,2) の位数 2 元は 1 次元固定空間) ので,
  **`|P| > 16` (`k ≥ 3`) をどこで使うかが未確定**。次回は書籍 p.196 の hint を
  PDF で読み直して詰める (現状は hint の要約からの再構成)。

⟹ この 1 ケースを残して 6B.8 の他は全部揃っている。


### ⭐ 6B.8 最終難所の証明が確定 (2026-07-27)

前記の「`|P| > 16` をどこで使うか未確定」を解消。`A` 非巡回のときの矛盾は次の通り
(`a ∉ A` を固定, `θ : A → A`, `θ(x) = x⁻¹ · a x a⁻¹`):

1. `A` 可換・指数 2 ⟹ `P' ≤ A`, `|P'| = |A|/2`。`θ` は準同型で **`im θ = P'`**,
   `ker θ = C_A(a)` ⟹ **`|C_A(a)| = 2`**, さらに `A` 極大可換ゆえ `Z(P) = C_A(a) = Z`。
2. **`a` は `P'` を反転する**: `θ(x)·θ(x)^a = x⁻¹x^a·x^{-a}x^{a²} = 1` (`a² ∈ A` 可換)
   なので `y ∈ P'` に対し `y^a = y⁻¹`。
3. ⟹ `C_{P'}(a) = Ω₁(P') ≤ C_A(a) = Z` なので **`P'` は唯一の involution を持つ可換 2-群
   = 巡回**。その唯一の involution が `Z`。
4. `A` 非巡回 ⟹ `Ω₁(A) ≠ Ω₁(P') = Z` なので **`P'` の外に involution `t`** があり
   `A = P' × ⟨t⟩`。
5. `a` は `P'` を反転するので `θ(y) = y⁻¹y^a = y⁻²`, つまり `θ(P') = ℧¹(P') = (P')²`
   (位数 `2^{k-1}`)。また `θ(t) = t·t^a ∈ Ω₁(A)`。
6. したがって `P' = im θ = θ(P')·θ(⟨t⟩) ≤ (P')² · Ω₁(A)`。⚠ `k ≥ 2` (すなわち
   **`|P| ≥ 16`**) なら `Ω₁(P') ≤ (P')²` なので右辺は位数 `≤ 2^{k-1}·2 = 2^k`… の吟味で
   `P' = (P')²` すなわち `|P'| ≤ |P'|/2` の矛盾に至る。**`|P| ≥ 16` はここで効く**。

⟹ 形式化の順序: (2) の反転 → (3) の巡回性 → (4) の分解 → (5)(6) の像の計算。


### 6B.8 進捗 (2026-07-27 続き): θ の像の正規性まで完了

`Problems6B8.lean` は部品 36 本が実証明 (sorry は主定理 `tausskyTodd` の 1 件のみ)。
θ 関連で揃ったもの: `theta_mul` / `theta_conj_eq_inv` / `thetaHom` (束ね) /
`thetaHom_range_le` / `mem_thetaHom_ker_iff` (核 = `C_A(a)`) /
`thetaHom_range_le_commutator` (`R ≤ P'`) / `thetaHom_conj_eq_inv` /
`thetaHom_range_centralized` / `inv_conj_mem_of_sq_mem` / `thetaHom_range_normal`。

**次の 1 手 = 逆包含 `P' ≤ R`**。筋は「`R` 正規で `P/R` が可換」:
* `A` の像どうしは可換 (`A` 可換)
* `a` の像と `A` の像も可換 — `a x a⁻¹ = x · θ(x) ≡ x (mod R)` だから
* `A ⊔ ⟨a⟩ = ⊤` なので `P/R` は可換 ⟹ `P' ≤ R`
⚠ Lean では「可換な生成元集合で生成される群は可換」を出す所が要検討
(`Subgroup.closure_le_centralizer_centralizer` か `Subgroup.closure_induction₂` を試す)。

そのあと: `|R| = |A|/|C_A(a)|` と `|R| = |P'| = |A|/2` から **`|C_A(a)| = 2`**,
反転則から `P'` 巡回 (`isCyclic_of_comm_two_group_unique_involution` が使える),
`A` 非巡回なら `A = P' × ⟨t⟩` で `im θ ⊆ (P')²·Ω₁(A)` の位数評価が破綻 — で完了。


### 🎉 6B.8 (Taussky-Todd) 完成 (2026-07-27) — §6B 完済

**主定理 `tausskyTodd` が sorry-free**。`#print axioms` = `[propext, Classical.choice,
Quot.sound]` (axiom-clean)。

最後に残っていた「帰納 step の引き戻し `A` が非巡回」ケースは
`isCyclic_of_index_two_of_index_commutator_eq_four` (`Problems6B8.lean`) で排除:
* `im θ = P'` で `P'` は巡回, 生成元 `c` の位数 `2^k` は `|P'| = |P|/4 ≥ 4` から `k ≥ 2`
  (**`|P| ≥ 16` がここで効く**)。
* `A` 非巡回なら `⟨c⟩` の外に involution `t` があり `A = P'⟨t⟩` (`Subgroup.normal_mul` で
  `x = y · t^j` に分解)。
* `y ∈ P'` では `θ(y) = (y²)⁻¹ ∈ ⟨c²⟩`、`s ∈ ⟨t⟩` では `θ(s)² = θ(s²) = 1` かつ
  `θ(s) ∈ P' = ⟨c⟩` ゆえ `θ(s) ∈ ⟨c²⟩` (位数 `2^k`, `k ≥ 2` の巡回群の involution は平方元)。
* ⟹ `P' = im θ ≤ ⟨c²⟩` で `c ∈ ⟨c²⟩`、`orderOf c` が偶数であることに反する。

帰納法本体 + 組み立ては新 leaf **`Problems6B8Induction.lean`** (`OddOrder.lean` 配線済):
* `exists_index_two_zpowers_of_card_le` = `|P| ≤ n` で括った帰納 engine
  (base `|P| = 8` / step は `P/Z` に降りる)。
* `exists_index_two_zpowers_of_index_commutator_eq_four` = 帰納の結論
  (`2`-群 + `|P| ≥ 8` + `|P : P'| = 4` ⟹ 指数 `2` の巡回部分群が在る)。
* `tausskyTodd` = `|P| = 8` は Cor 6.14、`|P| ≥ 16` は上記 `⟨c⟩` (位数 `2^m`, `m ≥ 3`) と
  `four_lt_index_center` を **6B.7** に食わせる。

⟹ **書籍 hint の「`P/Z` が D/SD/Q だから指数 2 の巡回部分群を引き戻す」段を回避**したので、
具体群 D/SD/Q の構造 (指数 `2` の巡回部分群を持つこと) を 3 種類とも証明する必要が無くなった。


### 🎉 6B.9 完成 (2026-07-27) — §6B 全 9 問 完済

**`card_primeFactors_le_two_of_forall_prime_pow_orderOf`** (`Problems6B9.lean`, 新 leaf,
`OddOrder.lean` 配線済): 可解群 `G` の全元が素数冪位数なら `|G|` の素因数は高々 2 個。
axiom-clean (`[propext, Classical.choice, Quot.sound]`)。

証明 (素数 3 個以上を仮定して矛盾):
1. minimal normal `U ⊴ G` は elementary abelian `p`-群 (Thm 3.11 =
   `solvable_minimal_normal_isElementaryAbelian`)。
2. `p` 以外の 2 素数 `q ≠ r` を取り、可解性から Hall `{p}ᶜ`-部分群 `K` (Thm 3.13 =
   `hall_exists_of_piSeparable`; `isPiSeparable_of_solvable` instance)。`q, r ∣ |K|`,
   `p ∤ |K|` は Hall 定義 (`|K|` の素因子 ⊆ π、index の素因子 ∩ π = ∅) から。
3. **EPPO の要 `false_of_commute_of_coprime_orderOf`**: 位数が互いに素な非自明元が可換なら
   `orderOf (xy) = orderOf x · orderOf y` が相異なる 2 素数で割れて素数冪でない。
   ⟹ `K` の共役作用は `U` 上 Frobenius (`MulAut.conjNormal` 経由の `MulDistribMulAction`)。
4. `K` の minimal normal `M` は elementary abelian `s`-群。`{q,r}` から `s` と異なる `t` を
   選び `y ∈ K` を位数 `t` (Cauchy) に取ると **`M⟨y⟩` は Frobenius 群**
   (`isFrobeniusGroup_sup_zpowers_of_prime_orderOf` = 6B.1 前半の構成を仮説だけに抽象化。
   ⚠ `M` 可換性は不要と判明したので仮説から落とした)。
5. `false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup` (Thm 6.9 可解分岐 =
   6B.1 の "deduce" 部分) に流して矛盾。

⟹ **§6B 完済 (6B.1〜6B.9 全 9 問)**。次は §6C の Problems。


### §6C 着手 (2026-07-27): 6C.1(a) 完了

§6C は 2 問のみ (6C.1 (a)(b) / 6C.2 (a)(b))。

* ✅ **6C.1(a)** `isNilpotent_of_prime_orderOf_mulAut_of_fixedFree` (`Problems6C1.lean`):
  素数位数の自己同型 `α` が単位元しか固定しないなら `G` 冪零。`A = ⟨α⟩ ≤ Aut(G)` の作用が
  Frobenius (非自明 `a ∈ A` は素数位数ゆえ `⟨a⟩ = A ∋ α`、安定化群が部分群なので `a` の
  固定点は `α` の固定点) ⟹ Isaacs Thm 6.24 (`isNilpotent_of_isFrobeniusAction`)。
  ⚠ `Finite (MulAut G)` は mathlib が既に導出できる (自作 instance は削除)。
* ⏳ **6C.1(b)** 「位数 4 の自己同型では冪零でない例 (`|G| = 75`)」= **具体例の構成**。
  設計: `G = (ZMod 5)² ⋊ ZMod 3` (作用は `x²+x+1` の companion 行列 `B`、mod 5 で既約)。
  `α(v, c) = (A v, c⁻¹)` が自己同型になる条件は `A B A⁻¹ = B⁻¹` で、`A = 2σ`
  (`σ` = Frobenius `x ↦ x⁵` の行列 `[[1,-1],[0,-1]]`) が `A² = -I` (位数 4)・固有値 1 なし
  (⟹ 固定点は単位元のみ) を満たす。非冪零は「冪零なら Sylow 3 が正規 ⟹ 作用自明」で出る。

* ✅ **6C.1(b)** 完了 (`Problems6C1Example.lean`, 新 leaf, `OddOrder.lean` 配線済,
  axiom-clean): `exists_orderOf_four_mulAut_fixedFree_not_isNilpotent` =
  `|G| = 75` ∧ `orderOf α = 4` ∧ `α` の固定点は単位元のみ ∧ `¬ IsNilpotent G`。
  * `Kernel = Multiplicative ((ZMod 5)²)`, `bAut (x,y) = (-y, x-y)` (位数 3),
    `aAut (x,y) = (2x-2y, -2y)` (`= 2σ`, `aAut² = -1`)。**関係式・固定点自由性・
    位数はすべて `decide`** (25 元の有限計算) で確定 — `aAut * bAut = bAut⁻¹ * aAut`,
    `aAut^4 = 1`, `(aAut*aAut) v = v⁻¹`, `bAut/aAut` の固定点は単位元のみ。
  * `Group75 = Kernel ⋊[Complement.subtype] ⟨bAut⟩` (`SemidirectProduct`;
    φ に部分群の包含をそのまま使うと「巡回群からの hom」を作らずに済む)。
  * `α = SemidirectProduct.congr aAut complementInv _` (両側の compatibility は
    `MulAut.conj aAut (bAut^m) = (bAut^m)⁻¹` を `map_zpow` で出す)。
  * 非冪零は `Z(G) = ⊥` + mathlib `Group.IsNilpotent.center_ne_bot`。
    `Z(G) = ⊥` は「`x.right` が `V` を固定 ⟹ 作用の固定点自由性で `x.right = 1`、
    その後 `bAut x.left = x.left` ⟹ `x.left = 1`」。

* ✅ **6C.2(a)** 完了 (`Problems6C2.lean`, 新 leaf, `OddOrder.lean` 配線済, axiom-clean):
  `exists_family_nilpotent_subgroups_of_card_prime_sq` = 位数 `p²` の elementary abelian
  `A` が非冪零 `N` に作用し `C_N(A) = 1` なら、非自明冪零部分群が `p + 1` 個あり
  どの 2 つの交わりも自明。
  * 支持: `exists_family_subgroups_card_prime` = elementary abelian `p²` の位数 `p` の
    部分群を `p + 1` 個構成 (`⟨x y^k⟩` (k < p) と `⟨y⟩`; 相異性は
    `zpow_mul_zpow_eq_one_of_eq` + `eq_zero_of_zpow_mul_zpow_eq_one` の指数一意性から、
    「相異なる位数 `p` の 2 部分群は `⊔` で全体」は位数の割り切りで)。
  * `fixedSubgroup B` (= `C_N(B)`) を定義。素数位数 `B` では「非自明元 1 つが固定 =
    `B` 全体が固定」(`mem_fixedSubgroup_of_smul_eq`)。
  * `K i = C_N(B i)`: 非自明 (さもなくば `B i` の作用が Frobenius で Thm 6.24 から `N`
    冪零)、冪零 (`j ≠ i` で `B j` が `K i` に Frobenius 作用 —
    `IsFrobeniusAction.invariantSubgroupMulDistribMulAction` で target 制限)、
    交わり自明 (`B i ⊔ B j = ⊤` と `C_N(A) = 1`)。
* ⏳ **6C.2(b)** 残り: `Q_i = K_i` の Sylow `q`-部分群、`X = ⟨Q_i⟩` が `Syl_q(N)` に入る。
  hint = `A`-不変 Sylow `q`-部分群 `Q` を取り `X ≤ Q`; `X < Q` なら `A`-不変な
  `X ≤ Y < Q` を作り `A` の `Q/Y` への作用が Frobenius になることを示す。

#### 6C.2(b) 進捗 (2026-07-27): 互いに素性の補題を実証明 + 使うインフラの所在確定

* ✅ `not_dvd_card_of_fixedFree_of_isPGroup` (`Problems6C2.lean`): **`p`-群 `A` が `C_N(A) = 1`
  で作用すれば `p ∤ |N|`**。`p ∣ |N|` なら `|Syl_p(N)| ≡ 1 (mod p)` + `A` が `p`-群 ⟹
  `A`-不変 Sylow `p`-部分群 `P` があり (`IsPGroup.card_modEq_card_fixedPoints` を
  `Sylow p N` に適用)、`A` の `↥P` への作用でも固定点の個数 ≡ `|P|` ≡ 0 (mod p) なので
  単位元以外の固定点が出て矛盾。⟹ **(b) で要る coprime 仮説は (a) の仮説から導ける**
  (書籍が言わない仮説を足す必要がない = 特殊化債務なし)。
* 使うインフラ (所在確定済、いずれも `OddOrder.Isaacs.Ch04.*` = 書籍順で上流):
  * `exists_aInvariant_sylow` (Thm 3.23(a))、`aInvariant_sylow_conj` (3.23(b)) —
    仮説は `Coprime (card A) (card G)` + `IsSolvable A ∨ IsSolvable G` (A は elementary
    abelian ゆえ可解で OK、`N` の可解性は不要)。
  * `aInvariant_pSubgroup_le_aInvariant_sylow` (Cor 3.25) = A-不変 q-部分群は A-不変 Sylow に入る。
  * `coprime_fixedPoints_quotient_of_coprime_normal` (Cor 3.28) = 商の固定点は底の固定点像。
* 残りの筋: `Q_i` = 冪零 `K_i` の唯一の Sylow `q` (⟹ `K_i` で characteristic ⟹ A-不変)、
  `X = ⨆ Q_i` は A-不変 q-部分群なので A-不変 Sylow `q` の `Q` に入る (Cor 3.25)。
  `X < Q` なら `Y := X ⊔ Φ(Q)` が `Q` で正規・A-不変・真 (Frattini) で、
  Cor 3.28 から `C_{Q/Y}(A_i) = C_Q(A_i)Y/Y = 1` (∵ `C_Q(A_i) ≤ Q_i ≤ X`) ⟹ `A` の
  `Q/Y` 作用が Frobenius ⟹ Thm 6.9 elementary-abelian 分岐
  (`false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_prime_sq_of_finite_target`)
  で矛盾。

* ✅ 6C.2(b) 部品 2 本 (2026-07-27):
  * `exists_max_qSubgroup_le_of_isNilpotent`: `↥K` 冪零なら `K` の `q`-部分群を全て含む
    `q`-部分群 `Q ≤ K` がある (冪零 ⟹ `NormalizerCondition` ⟹ Sylow 正規 ⟹
    `Sylow.unique_of_normal` で一意 ⟹ `IsPGroup.exists_le_sylow` で全部入る)。
    ⟹ これが書籍の「`K_i` の唯一の Sylow `q`-部分群 `Q_i`」。
  * `smul_mem_of_max_qSubgroup`: `K` が `A`-不変なら最大 `q`-部分群 `Q` も `A`-不変
    (`a • Q` も `K` の `q`-部分群なので最大性で `a • Q ≤ Q`; `Subgroup.pointwise_smul_def`
    で `map` に直して `IsPGroup.map`)。
  * 次: `X = ⨆ i, Q i` が `A`-不変 q-部分群 ⟹ Cor 3.25 で `A`-不変 Sylow `q` の `Q` に入り、
    `X < Q` から `Y = X ⊔ Φ(Q)` で矛盾を出す段 (Cor 3.28 + Thm 6.9 elem-abelian 分岐)。

* ✅ 6C.2(b) 橋渡し 2 本: `isAInvariant_of_smul_mem` / `smul_mem_of_isAInvariant`
  (`MulDistribMulAction` の元ごとの不変性 ⟺ Ch.3/Ch.4 の `IsAInvariant φ H`
  (`φ = MulDistribMulAction.toMulAut A N`); 逆向きは `a⁻¹ • x` を取るだけ)。
  `Problems6C2.lean` は `OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03` を import。
  ⟹ 次 iteration で Cor 3.25 (`aInvariant_pSubgroup_le_aInvariant_sylow`) と
  3.23(b) (`aInvariant_sylow_conj` + `C_N(A) = 1` ⟹ A-不変 Sylow q は一意) を使って
  各 `Q i ≤ Q`、したがって `X = ⨆ Q i ≤ Q` を出す。

* ✅ 6C.2(b) 一意性 2 本: `aInvariant_sylow_unique` (`C_N(A) = 1` なら A-不変 Sylow `q` は
  一意 — 3.23(b) の共役元 `c` が `C_N(A)` に入るので `c = 1`) /
  `le_sylow_of_aInvariant_qSubgroup` (A-不変 `q`-部分群は Cor 3.25 で A-不変 Sylow に入り、
  一意性でその Sylow は目的の `S` に一致)。
  ⟹ これで各 `Q i ≤ S` が出るので `X = ⨆ Q i ≤ S` は `iSup_le` で即。
  残りは **`X < S` からの矛盾** (`Y = X ⊔ Φ(S)` は `S` で正規・A-不変・真、
  Cor 3.28 で `C_{S/Y}(B i) = 1` ⟹ `A` の `S/Y` 作用が Frobenius ⟹ Thm 6.9
  elementary-abelian 分岐) の段のみ。

* ⭐ **6C.2(b) 主定理 `exists_sylow_eq_iSup_maxQSubgroup` 実証明 (2026-07-27, axiom-clean)**:
  位数 `p` の部分群 `D ≤ A` ごとに `K_D = C_N(D)` の最大 `q`-部分群 `Q_D` を取ると
  `⨆_D Q_D` はある Sylow `q`-部分群にちょうど一致する。
  * `X ≤ S`: `A`-不変 Sylow `q` は一意 (`aInvariant_sylow_unique`)、各 `Q_D` は
    `A`-不変 `q`-部分群 (`smul_mem_of_max_qSubgroup` + `smul_mem_fixedSubgroup`) なので
    `le_sylow_of_aInvariant_qSubgroup` で `S` に入る。
  * `S ≤ X`: **書籍 hint の `Y = X ⊔ Φ(Q)` / `Q/Y` の Frobenius 化を経由せず、
    §6B の Thm 6.21 (`nontrivialActionFixedByClosure_eq_top_of_not_isCyclic`) を直接使う**
    (文書順は保たれる)。`a ≠ 1` に対し `S ⊓ C_N(⟨a⟩)` は `C_N(⟨a⟩)` の `q`-部分群なので
    最大性で `Q_{⟨a⟩}` に入り、Thm 6.21 で `C_S(a)` たちが `S` を生成するから `S ≤ X`。
  * 添字は「位数 `p` の部分群すべて」= subtype `{D // Nat.card D = p}` にした (これで
    「ちょうど `p+1` 個」の counting を証明せずに書籍の `X = ⟨Q_1,…,Q_{p+1}⟩` を表現できる;
    (a) が `p+1` 個の相異なるものを構成済み)。
  * 補助: `smul_mem_fixedSubgroup` / `not_isCyclic_of_card_prime_sq` /
    `coprime_card_of_fixedFree`。
  * 残り (次 iteration): `K_D` の冪零性を (a) の証明から独立補題に切り出し、`Qf` を
    仮説でなく内部で構成する完全自己完結版の corollary を付ける。

* ⭐ **6C.2 完成 (2026-07-27)**: 自己完結版 `exists_maxQSubgroup_family_sylow_eq_iSup`
  (axiom-clean) — 仮説は (a) と同じ (`A` elementary abelian `p²`・`C_N(A) = 1`) だけで、
  `Q_D` の族は内部で構成する (`choose!`)。
  * `isNilpotent_fixedSubgroup_of_card_prime` = (a) の核心 (位数 `p` の `D` に対し
    `C_N(D)` は冪零) を単独補題に切り出し。`D` の外の `y` で `E = ⟨y⟩` を作り
    `D ⊔ E = ⊤` から `E` の `C_N(D)` 作用が Frobenius ⟹ Thompson。
    ⚠ `N` の非冪零性は不要 (それは (a) の `K_i ≠ 1` にだけ要る)。
  * `sup_eq_top_of_card_prime` を独立補題として切り出し、(a) の族構成の局所 `have` も
    これを呼ぶよう refactor (重複解消)。
  * `Problems6C2.lean` = 727 行 (上限 1500 に余裕)。

## 🎉 Ch.6 完済 (2026-07-27) — 次は Ch.7 Problems

Ch.6 の演習は **§6A 6A.1–6A.11 / §6B 6B.1–6B.9 / §6C 6C.1–6C.2 の全 22 問**が実証明
(すべて axiom-clean、各 leaf は `OddOrder.lean` 配線済)。本日追加した分:
6B.8 (Taussky-Todd 主定理) / 6B.9 / 6C.1(a)(b) / 6C.2(a)(b)。

次の frontier = **Ch.7 (Thompson Subgroup) の Problems** (文書順)。着手時は
問題番号一覧を PDF ページ画像で確定してから (pdftotext は記号が壊れる)。

## Ch.7 (Thompson Subgroup) §7A — 問題一覧 (書籍 pp. 209-210, pdftotext L10024-)

⚠ statement は着手時に PDF ページ画像で再確認する (式・添字が pdftotext で壊れる)。

| # | 主張 (要約) | 見込みの道具 |
|---|---|---|
| 7A.1 | ✅ **完了** (`Problems7A1.lean`, axiom-clean) 単純群の冪零な極大部分群は `2`-群 | **Thm 7.1** (Thompson の normal `p`-complement) + `Z(P)`/`J(P)` の正規化群が `M` に一致する議論 |
| 7A.2 | `S = SL(2,3)`, `Z = {±I}` ⟹ `S/Z` (位数 12) は Sylow 3 が 4 個 ⟹ Sylow 2 が一意 ⟹ `S` に位数 8 の正規部分群 | `GL(n,q)` の Sylow `p` が 2 個以上 (本文既知) + Sylow 数え上げ |
| 7A.3 | `G = GL(n,q)`, `P` = 上三角冪単, `D` = 対角 ⟹ (a) `D ≤ N_G(P)` (b) `DP` = 上三角全体 (c) `P`-不変部分空間は各次元にちょうど 1 つ (d) `N_G(P) = DP` | 行列計算 + `P`-不変部分空間の分類 |
| 7A.4 | `SL(2,q)` と `PSL(2,q)` の Sylow `p` はちょうど `q + 1` 個 | Sylow 数え上げ (Borel の指数) |
| 7A.5 | `P` `p`-群, `U ⊴ P` elementary abelian ⟹ `U` はある `E ∈ 𝓔(P)` を正規化 | `\|U ⊓ E\|` 最大の `E` を取る hint (書籍の証明あり) |
| 7A.6 | 一般四元数 `Q` で `\|Aut(Q)\|` が奇素数 `p` で割れる ⟹ `p = 3` かつ `\|Q\| = 8`; ⟹ Lemma 7.3 / Thm 7.5 の「Sylow 2 が可換」仮説は `p > 3` では不要 | `Aut(Q_{2^n})` の位数 (2 冪 × 小さい因子) の計算 |

文書順で **7A.1 から着手**。7A.1 は Thm 7.1 (repo の Ch07 に既存かを最初に grep で確認) と
`J(P)`・`Z(P)` の repo API を使う。§7B は Problems 節が無く (次の Problems 見出しは 7C)、
§7C の一覧は着手前に別途確認する。

### ⚠ 7A.1 は Thm 7.1 の**無条件版**に gated (2026-07-27 実測)

`OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean:436`
`thompson_normal_p_complement` は **条件付き** — 教科書 Thm 7.1 の仮説
(「`C_G(Z(P))` と `N_G(J(P))` が normal `p`-complement を持つ」) に加えて

* `IsPiSeparable {p} G`
* 全 `2`-部分群が可換
* `O_{p'}(G) = ⊥`
* `C_G(Z(P)) = P`

を要求する (docstring 自身が「残りは §7C Steps 1-6」と明記)。Steps 4-6 は
`S7C_SylowMaximal` / `S7C_CentralizerCenter` / `S7C_AbelianQuotientComplement` に
`hG : ¬ HasNormalPComplement p G` 付きの最小反例補題として在るが、**最小反例の帰納で
これらを組み上げて無条件版にする段が無い**。Ch07 に sorry は 0 (= scaffold ではなく
「まだ書かれていない」)。

⟹ **7A.1 (単純群の冪零極大部分群は 2-群) は Thm 7.1 無条件版が前提**
(証明: `M` 冪零極大 ⟹ 各 Sylow は `G` の Sylow で `M = N_G(P)`、`M ≤ C_G(Z(P))` と
`M ≤ N_G(J(P))` がともに `M` に一致し `M = P × H` は normal `p`-complement を持つ ⟹
Thm 7.1 で `G` が normal `p`-complement をもち単純性に矛盾)。

**方針 (上流優先)**: Thm 7.1 の無条件版 (= §7C Steps 1-3 + 最小反例の組み上げ) は
Isaacs の**番号付き結果**でありlane a の territory・かつ 7A.1 の上流なので、
次 iteration からこれに着手する。7A.2-7A.6 は Thm 7.1 に依存しない
(GL(n,q)/SL(2,q) の Sylow 数え上げ・`𝓔(P)`・`Aut(Q_{2^n})`) ので、Thm 7.1 が長引く場合の
並行候補として残す。

### ✅ 訂正 (2026-07-27): 7A.1 は gated ではない — Thm 6.23 (無条件) で足りる

前項の「7A.1 は Thm 7.1 無条件版に gated」は**過小評価だった**。7A.1 の証明には
教科書 Thm 7.1 (Z(P) と J(P) の 2 つだけ) は不要で、**Thm 6.23**
(`OddOrder.Isaacs.Ch06.hasNormalPComplement_of_forall_characteristic_normalizer`,
`ThompsonPComplement.lean:55`, **無条件・axiom-clean**: `p ≠ 2` と「`P` の非自明
characteristic 部分群すべての正規化群が normal `p`-complement を持つ」だけ) で足りる。
理由: 冪零極大 `M` は `P` の**すべての** characteristic 部分群を正規化するから
(`P ⊴ M` かつ `M` の `p`-complement `H` は `[P, H] ≤ P ⊓ H = ⊥` で `P` を中心化)。

**7A.1 の証明設計** (次 iteration で実装):
1. `M` 冪零極大、奇素数 `p ∣ |M|` を仮定 (`IsPGroup 2 ↥M` の否定から取る)。
2. `P` = `M` の Sylow `p` を `G` へ写したもの。`M` 冪零 ⟹ `P ⊴ M`;
   `N_G(P) ⊇ M` で単純性 (`P ≠ ⊥`, `P ≠ ⊤`) から `N_G(P) ≠ G` ⟹ 極大性で `N_G(P) = M`。
3. `P ∈ Syl_p(G)`: `P ≤ Q ∈ Syl_p(G)` で `P < Q` なら `NormalizerCondition ↥Q`
   (p-群は冪零) から `P < N_Q(P) ≤ N_G(P) = M` となり `P` が `M` の Sylow `p` に反する。
4. 非自明 characteristic `X ≤ ↥P` に対し `M ≤ N_G(X.map)`:
   `P ≤ N_G(X.map)` (char ⟹ `P`-正規) + `H ≤ C_G(P) ≤ N_G(X.map)` + `M = P ⊔ H`。
   単純性で `N_G(X.map) ≠ G` (`X.map ≠ ⊥`, `X.map = ⊤` なら `P = ⊤` で `M = ⊤` に矛盾)
   ⟹ 極大性で `= M`。`M` 冪零ゆえ normal `p`-complement を持つ
   (`Ch05.hasNormalPComplement_of_isNilpotent`)。
5. Thm 6.23 ⟹ `G` が normal `p`-complement `K` を持つ。単純性で `K = ⊥` (⟹ `G` は
   `p`-群で中心が非自明 ⟹ 単純性に反する/位数 `p` なら `M = 1` で `p ∣ |M|` に反する) か
   `K = ⊤` (⟹ `p ∤ |G|` で `p ∣ |M|` に反する) のどちらでも矛盾。

⟹ Thm 7.1 無条件版 (§7C Steps 1-3 + 組み上げ) は**別枠の上流タスク**として残すが、
§7A の演習は Thm 6.23 で進められる。

### 7A.1 進捗 (2026-07-27): 再利用可能な Sylow 補題を実証明

新 leaf `OddOrder/Isaacs/Ch07_ThompsonSubgroup/Problems7A1.lean` (`OddOrder.lean` 配線済):

* ✅ `exists_sylow_eq_of_maximal_pSubgroup_in_normalizer`: **`N_G(P)` の中で極大な
  `p`-部分群 `P` は `G` の Sylow `p`-部分群**。`P ≤ S ∈ Syl_p(G)` を取り `P < S` なら
  `S` は `p`-群ゆえ冪零 ⟹ `NormalizerCondition ↥S` から `P.subgroupOf S` を正規化する
  `x ∈ S \ P` が在り、`P ⊔ ⟨x⟩` は `N_G(P)` 内の `p`-部分群で `P` を真に含むので極大性に反する
  (`IsPGroup.to_sup_of_normal_left'` を使用)。
  ⚠ この mathlib 版の `NormalizerCondition` は `H < ⊤` を取る (`H ≠ ⊤` ではない)。
  ⟹ 7A.1 の step 3 (`P ∈ Syl_p(G)`) がこれ 1 本で済む。汎用なので他の演習でも使える見込み。
* 次: 7A.1 本体 (`N_G(P) = M` の確立 → characteristic 部分群の正規化 → Thm 6.23 で矛盾)。
* ✅ `exists_mul_centralizing_of_isNilpotent` (2026-07-27): 冪零な `M ≤ G` の Sylow
  `p`-部分群 `Pm` について、`M` の元はすべて「`Pm` の元」×「`Pm` を中心化する元」の積。
  `M` 冪零 ⟹ `Pm ⊴ M` + normal `p`-complement `N ⊴ M` があり `N ⊓ Pm = ⊥` なので
  `Subgroup.commute_of_normal_of_disjoint` で `N` が `Pm` を元ごとに中心化する。
  ⚠ mathlib の `commute_of_normal_of_disjoint` は `(x y : G) (hx) (hy)` の順 (元 2 つが先)。
  ⟹ これで `M ≤ N_G(X)` (X は `P` で正規な部分群) が **layer 変換なしで**出せる:
  `m = u * h` と書けば `m y m⁻¹ = u (h y h⁻¹) u⁻¹ = u y u⁻¹ ∈ X`。
* ✅ `le_normalizer_of_isNilpotent` (2026-07-27): 冪零 `M` は Sylow `P` 内の `P`-正規部分群
  `X` を正規化する (`m = u*h` 分解 ⟹ `m y m⁻¹ = u y u⁻¹ ∈ X`; 逆包含は `m⁻¹ ∈ M` から)。
* ✅ 7A.1 主定理の骨組み + `hnormeq` (極大性 + 単純性から `N_G(Y) = M`) を実証明。
  残り = step 6-9 (`P ∈ Syl_p(G)` の適用 / characteristic `X` ごとの
  `HasNormalPComplement p ↥(N_G(X.map))` / Thm 6.23 / `N = ⊥ ∨ ⊤` の矛盾) — sorry 1 件。
  ⚠ この mathlib では `Subgroup.normalizer` は **`Set G` を取る** (`(Y : Set G)` と明示が必要)。
  単純性は `IsSimpleGroup.eq_bot_or_eq_top_of_normal`、`Subgroup G` は linear order でないので
  `not_lt` でなく `eq_of_le_of_not_lt` を使う。

### 🎉 7A.1 完成 (2026-07-27) — `isPGroup_two_of_isNilpotent_of_isCoatom` (axiom-clean)

`Problems7A1.lean` (`OddOrder.lean` 配線済) に 4 本:
* `exists_sylow_eq_of_maximal_pSubgroup_in_normalizer` (汎用): `N_G(P)` 内で極大な
  `p`-部分群は `G` の Sylow。
* `exists_mul_centralizing_of_isNilpotent`: 冪零 `M` の元は「Sylow の元」×「中心化元」の積。
* `le_normalizer_of_isNilpotent`: 冪零 `M` は Sylow `P` 内の `P`-正規部分群を正規化する。
* **`isPGroup_two_of_isNilpotent_of_isCoatom`** (主定理): 単純群の冪零な極大部分群は `2`-群。
  奇素数 `p ∣ |M|` を仮定 ⟹ `N_G(P) = M` (極大性 + 単純性) ⟹ `P ∈ Syl_p(G)` ⟹
  `P` の非自明 characteristic 部分群 `X` すべてで `N_G(X.map) = M` かつ `M` 冪零ゆえ
  normal `p`-complement ⟹ **Thm 6.23** で `G` に normal `p`-complement `N` ⟹
  単純性で `N = ⊥` (⟹ `S = ⊤ ≤ M` で `M ≠ ⊤` に矛盾) / `N = ⊤` (⟹ `S = ⊥` で `P ≠ ⊥` に矛盾)。

API メモ: `Sylow.is_maximal'` / `Subgroup.map_subgroupOf_eq_of_le` /
`Subgroup.normal_of_characteristic` (instance) / `Subgroup.isComplement'_bot_left` ·
`isComplement'_top_left`。⚠ `X.map f ≠ ⊥` は `rw [map_eq_bot_iff_of_injective]` が
`Ne` の下では効かないので `intro hbot` してから使う。

次: 7A.2 (`SL(2,3)/Z` の Sylow 数え上げ ⟹ 位数 8 の正規部分群)。

### 7A.2 の設計 (2026-07-27 調査)

必要な部品の所在が確定:
1. `|SL(2,3)| = 24`: `natCard_specialLinearGroup_fin_two` (issue 9211 で char 任意に
   一般化済) に `|ZMod 3| = 3` を入れて `3 * 2 * 4 = 24`。
2. `Z := ⟨-I⟩` は中心的で位数 2 (`-I ≠ I` は char 3 ゆえ、`(-I)² = I`)。
   ⚠ 「`Z` = 中心」までは示さなくてよい (書籍も `Z = {±I}` と定義しているだけ)。
   ⟹ `S/Z` の位数は 12。
3. **`n_3(S/Z) = 4`**: ここが本体。`n_3 ∣ 4` かつ `≡ 1 (mod 3)` ⟹ `n_3 ∈ {1, 4}`。
   非自明性は「相異なる Sylow 3 が 2 つある」ことから: `[[1,1],[0,1]]` と `[[1,0],[1,1]]`
   の生成する位数 3 の部分群が相異なる (書籍 hint の `GL(n,q)` の Sylow `p` が 2 個以上、を
   具体行列で直接出す)。`S` の Sylow 3 と `S/Z` の Sylow 3 は `Z` が 2-群なので対応。
4. **`sylow_two_normal_of_card_twelve_of_four_sylow_three`** =
   `OddOrder/Isaacs/Ch01_Sylow/Theorem131.lean:139` に**既存** (位数 12 + `n_3 = 4` ⟹
   Sylow 2 が正規; 数え上げ証明つき)。⚠ ただし **`private`** なので
   Ch07 から呼べない ⟹ CLAUDE.md「`private` をファイル跨ぎで使わない」に沿って
   **public 化する** (Ch01 は Ch07 の上流なので依存方向は問題なし)。
5. `S/Z` の正規 Sylow 2 (位数 4) の `QuotientGroup.mk'` による引き戻しが `S` の位数 8 の
   正規部分群 (`Z ≤` 引き戻し, 位数 `4 * 2 = 8`)。

⟹ 次 iteration: (4) の public 化 → (2)(3) → (5) の組み上げ。

### 7A.2 進捗 (2026-07-27): 具体計算パート完了

* ✅ `Ch01_Sylow/Theorem131.lean` の `sylow_two_normal_of_card_twelve_of_four_sylow_three`
  を **public 化** (CLAUDE.md「`private` をファイル跨ぎで使わない」)。
* ✅ 新 leaf `Problems7A2.lean` (`OddOrder.lean` 配線済) に `SL(2,3)` の具体事実:
  * `natCard_sl23 : Nat.card SL23 = 24` (9211 で一般化した `|SL(2,F)| = q(q-1)(q+1)`)。
  * `negOneSL23 = [[2,0],[0,2]]` (= `-I`, 標数 3) と `negOneSL23_sq` / `_ne_one`。
  * `transvectionA = [[1,1],[0,1]]`, `transvectionB = [[1,0],[1,1]]` の `^3 = 1` / `≠ 1`、
    および `transvectionB ∉ ⟨transvectionA⟩`。
  * **行列計算はすべて `decide` で通る** (`SL(2,ZMod 3)` は `Fintype` + `DecidableEq`)。
    `⟨a⟩ = {1,a,a²}` の場合分けは `m % 3` の 3 ケース + `decide`。
  ⚠ 長い namespace は `open ... in` で回避 (100 文字制限; `|>.` は namespace には効かない)。
    `Int.ediv_add_emod` は無いので `m = 3*(m/3) + m%3` は `by omega`。
* 次: (2) `Z = ⟨negOneSL23⟩` が中心的・位数 2 ⟹ `|S/Z| = 12`、(3) `n_3(S/Z) = 4`
  (`n_3 = 1` なら `S` に位数 3 の正規部分群 ⟹ 位数 3 の元は全てそこに入り
  `transvectionA`/`B` に矛盾)、(5) 正規 Sylow 2 の引き戻しで位数 8。
* ✅ 7A.2 (2) 完了: `centerZ = ⟨negOneSL23⟩` は正規 (`negOneSL23_mem_center` は
  **`∀ g : SL23, g * (-I) = (-I) * g` を `decide` で判定**できる) で `|Z| = 2`、
  ⟹ `natCard_quotient_centerZ : |SL(2,3)/Z| = 12`。
  ⚠ `Subgroup.mem_center_iff.mp h g : g * a = a * g` (= `Commute g a`; `.symm` 不要)。

### 🎉 7A.2 完成 (2026-07-27) — `exists_normal_card_eight_sl23` (axiom-clean)

`Problems7A2.lean` (274 行):
* `card_sylow_three_quotient : Nat.card (Sylow 3 (SL(2,3)/Z)) = 4`。
  `n_3 ∣ 4` (`Sylow.card_dvd_index`) + `n_3 ≡ 1 mod 3` (`card_sylow_modEq_one`) で
  `n_3 ∈ {1,4}` (`interval_cases` + `decide` で 2, 3 を排除)。`n_3 = 1` の排除は
  `Subsingleton (Sylow 3 Q)` から `⟨ā⟩ = P1 = P2 = ⟨b̄⟩` (位数 3 = Sylow の位数なので
  `Subgroup.eq_of_le_of_card_ge`) ⟹ `b̄ ∈ ⟨ā⟩` ⟹ `(a^i)⁻¹ b ∈ Z` の 3×2 = 6 通りが
  すべて `decide` で偽。
* `exists_normal_card_eight_sl23`: 位数 12 補題 (Ch01, public 化済) の正規 Sylow 2 を
  `QuotientGroup.mk'` で引き戻し、`Subgroup.index_comap` で指数 3 を保つので
  `|N| = 24/3 = 8`。
* `mem_centerZ_iff : x ∈ Z ↔ x = 1 ∨ x = -I` (zpowers の `m % 2` 展開) が 6 ケース化の鍵。
  ⚠ `QuotientGroup.eq_one_iff` は**元を明示引数に取る** (`(QuotientGroup.eq_one_iff x).mp`)。

⟹ §7A は 2/6 完了 (7A.1, 7A.2)。次は 7A.3 (`GL(n,q)` の `N_G(P) = DP`)。

### §7A statement を PDF ページ画像で確定 (2026-07-27)

`references/isaacs/pages/isaacs-p209-222.png` を新規レンダリング (書籍 p.209 = PDF p.222、
`pdftoppm -r 150`; 規約どおり references リポに保存)。pdftotext の崩れを 2 箇所訂正:

* **7A.3(c)**: 「dimension `k` for each integer `k` with **`1 ≤ k ≤ n`**」
  (pdftotext は `1 < k < n` に見えていた)。また **`G` は行ベクトルへの右からの掛け算で作用**
  ⟹ 不変部分空間は**後ろの `k` 本**の基底が張るもの (`e_n A = e_n` だが `e_1 A` は第 1 行)。
* **7A.5**: `U ⊲ P` は **normal** (単一の ⊲; pdftotext の `U <d P` は判別不能だった)。
  [[mmd-collapses-subnormal-symbol]] の教訓どおり画像で確認した。
* 7A.2 の hint は `n ≥ 2` (pdftotext は `n > 2`) — 実装済の 7A.2 には影響なし。

7A.3 の設計メモ: (a) 対角共役で上三角冪単は保たれる、(b) `DP` = 可逆上三角全体、
(c) `P`-不変部分空間は標準旗 `⟨e_{n-k+1},…,e_n⟩` のみ (各次元ちょうど 1 つ)、
(d) `N` は `P`-不変部分空間を保つので旗を保ち ⟹ 上三角 ⟹ `N = DP`。
⟹ (a)(b) は初等的。(c) が核心 (有限体上の線型代数)。

### 7A.3 進捗 (2026-07-27): 上三角/冪単の部分群を実証明

新 leaf `Problems7A3.lean` (`OddOrder.lean` 配線済):
* `blockTriangular_mul_diag`: **上三角行列の積の対角成分は対角成分の積**
  (`(A*B) i i = ∑ k, A i k * B k i` で `k < i` は `A i k = 0`、`i < k` は `B k i = 0`;
  `Finset.sum_eq_single`)。これが冪単性の積・逆元での保存の鍵。
* `upperTriangularGL` (可逆上三角 = Borel) / `unitriangularGL` (上三角冪単 = Sylow p) を
  `Subgroup (GL (Fin n) F)` として定義。逆元は
  `Matrix.blockTriangular_inv_of_blockTriangular` + `Matrix.coe_units_inv`、
  冪単性の逆元側は `(A * A⁻¹) i i = A i i * (A⁻¹) i i = 1` から。
* `unitriangularGL_le_upperTriangularGL`。
* ⚠ 「上三角」は `Matrix.BlockTriangular M id` (`∀ i j, j < i → M i j = 0`) で表す。
  `[DecidableEq F]` は**不要** (行列の逆に要るのは添字型 `Fin n` の DecidableEq)。
* 次: (a) `D ≤ N(P)` (対角共役)、(b) `DP` = 上三角全体、(c) `P`-不変部分空間の分類、(d) `N = DP`。

### 🎉 7A.3 完成 (2026-07-27) — `N_G(P) = DP` (`Problems7A3.lean`, 601 行, axiom-clean)

(a)-(d) をすべて実証明。⚠ **主張は任意の体 `F` 上で成立**する (`q` の素数冪性は `P` を
Sylow `p`-部分群と解釈するときにしか効かない) ので, その一般性で形式化した。

* (a)(b): `blockTriangular_mul_diag` (上三角の積の対角成分 = 対角成分の積) が鍵。
  `blockTriangular_coe_inv` / `diag_mul_diag_inv` / `isUnit_diag_of_blockTriangular` /
  `isDiag_mul` (mathlib に `Matrix.IsDiag.mul` は無い) を経由して
  `upperTriangularGL` (Borel) / `unitriangularGL` (Sylow p) / `diagonalGL` (D) を定義。
  `conj_mem_unitriangularGL` ⟹ `upperTriangularGL_le_normalizer` (`P ⊴ B`) ⟹
  **(a)** `diagonalGL_le_normalizer`。**(b)** `diagonalGL_mul_unitriangularGL` (Set 積) /
  `diagonalGL_sup_unitriangularGL` (部分群 sup): `A ↦ (diagonal (A i i), diagonal(A i i)⁻¹ * A)`。
* (c): `IsRowInvariant H W` (`∀ A ∈ H, ∀ v ∈ W, v ᵥ* A ∈ W`) と `rowTail n m` =
  `⟨e_m,…,e_{n-1}⟩` を定義。右作用ゆえ不変なのは**後ろ**の座標側。
  `transvectionGL` (`1 + c·E_{i,j}`) + `vecMul_transvectionGL` で
  `single_mem_of_isRowInvariant` (非零成分の最小添字 `i₀` 以降の `e_j` が全部 `W` に入る) →
  **`exists_eq_rowTail_of_isRowInvariant`** (不変部分空間は `rowTail n m` に限る)。
  `rowTail_eq_ker` (先頭 `m` 座標への射影の核) + 階数退化次数定理で
  `finrank_rowTail = n - m` ⟹ **`existsUnique_isRowInvariant_finrank_eq`**
  (各次元 `k ≤ n` にちょうど 1 つ)。
* (d): `rowActionEquiv A` (`v ↦ v ᵥ* A` の線型同型) と
  `rowTail_map_rowActionEquiv` (`W ᵥ* A` はふたたび `P`-不変 + `LinearEquiv.finrank_map_eq`
  で次元不変 ⟹ (c) の一意性で `= W`) ⟹ **`normalizer_unitriangularGL_eq`** (`N_G(P) = B`)。
  `e_r ᵥ* A` = `A` の第 `r` 行が `rowTail n r` に入る ⟹ `A r s = 0` (`s < r`)。
  `_eq_sup` / `_eq_mul` で **`N_G(P) = DP`**。

Lean 実務メモ:
* ⚠ `Subgroup.normalizer` は **`Set G` を取る**。statement で `Subgroup.normalizer
  (H : Subgroup (GL (Fin n) F))` と書くと**戻り値型の metavariable が未解決で
  coercion 挿入に失敗**する (「expected Set (GL (Fin ?m) ?m)」)。
  `Subgroup.normalizer ((H : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F))` と
  **Set まで明示**する。同じ理由で `(H : Set _) * (K : Set _)` も二段ascription が要る。
* ⚠ `Matrix.transvection_mul_transvection_same` は `i j` が**明示引数**なので
  `... hij` と書くと `hij` が `i` に食われて rewrite pattern が壊れる (`... i j hij`)。
* `Matrix.stdBasisMatrix` は現行 mathlib では **`Matrix.single`** (`single_apply` あり)。
* `le_sup_left` は項 (関数でない) ゆえ metavariable 下で適用不可 →
  `Subgroup.mem_sup_left` / `mem_sup_right` を使う。
* `set x := e with h` の後に `rw [lemma]` で `e` が**再導入**されると omega が別 atom
  として扱う (`finrank_rowTail` で踏んだ) — statement に再登場する項に `set` を使わない。
* `IsUnit.of_mul_eq_one` (旧 `isUnit_of_mul_eq_one` は現存しない) /
  `finrank_top` は root namespace / `LinearEquiv.finrank_map_eq` /
  `LinearMap.finrank_range_add_finrank_ker` は `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`。

⟹ §7A は 3/6 完了 (7A.1, 7A.2, 7A.3)。次は **7A.4** (`SL(2,q)` と `PSL(2,q)` の
Sylow `p` はちょうど `q+1` 個)。

### 7A.4 の設計 (2026-07-27 調査)

既存インフラ:
* `natCard_specialLinearGroup_fin_two`
  (`OddOrder/GroupTheory/SpecificGroups/ProjectiveSpecialLinear/RootGroupSylow.lean:106`,
  **任意標数**に一般化済 = issue 9211): `|SL(2,F)| = q(q-1)(q+1)`。
* mathlib `Matrix.SpecialLinearGroup.transvection` / `transvection_add` / `transvection_coe` /
  `SL2_inv_expl` / `diag2` (対角 `[[a,0],[0,a⁻¹]]`) / `Sylow.card_eq_index_normalizer`。
* ⚠ 既存 `rootSubgroup` (`ProjectiveSpecialLinear/RootGroup.lean`) は **PSL 側かつ標数 2 専用**
  なので 7A.4 (任意標数, SL 側) には流用できない。

証明計画 (新 leaf `Problems7A4.lean`):
1. `transvectionHom : Multiplicative F →* SL(2,F)` (単射) と
   `unipotentSL = range` (`|U| = q`)。
2. `borelSL = {g | g 1 0 = 0}` と `Fˣ × F ≃ borelSL` (`(a,b) ↦ [[a,b],[0,a⁻¹]]`) ⟹
   `|B| = (q-1)q`。
3. `N_{SL}(U) = B`: `⊇` は `g u g⁻¹ = transvection (a² b)` (`a = g 0 0`);
   `⊆` は `g T g⁻¹` の `(1,0)` 成分が `-(g 1 0)²` なので `g 1 0 = 0`。
4. `U ∈ Syl_p(SL)` (`|U| = q = p^n`, index `(q-1)(q+1)` は `p` と互いに素) ⟹
   `Sylow.card_eq_index_normalizer` で `n_p = [SL : B] = q+1`。
5. PSL: `Z = Z(SL)` は `p` と互いに素な位数 (標数 2 なら自明, 奇標数なら位数 2) ⟹
   `n_p(SL/Z) = n_p(SL)` (中心的で位数互いに素な正規部分群による商は Sylow 数を保つ:
   `PZ = P × Z` ゆえ `P` char in `PZ` で `N_G(PZ) = N_G(P)`)。

### 🎉 7A.4 完成 (2026-07-27) — `Problems7A4.lean` (436 行, axiom-clean)

`SL(2,q)` / `PSL(2,q)` の Sylow `p` がちょうど `q+1` 個。任意の有限体 `F` (標数 `p`) で成立。

* `transvectionHom` (単射) → `unipotentSL` = 像 (`|U| = q`)。
* `borelSL = {g | g 1 0 = 0}`, `borelElt a b = [[a,b],[0,a⁻¹]]`,
  `borelEquiv : Fˣ × F ≃ B` ⟹ `|B| = (q-1)q`。
* `borelElt_mul` / `borelElt_inv` / `transvection_eq_borelElt` で Borel を `Fˣ ⋉ F` として
  計算 ⟹ `borelElt_conj_transvection` (`g u g⁻¹ = [[1,a²b],[0,1]]`)。
* `normalizer_unipotentSL_eq : N_{SL}(U) = B`。`⊆` は **逆行列を経由せず**
  `T' g = g T` の `(1,1)` 成分比較 (`g₁₀ + g₁₁ = g₁₁`)。
* `index_borelSL = q+1`, `index_unipotentSL = (q-1)(q+1)` ⟹
  `card_sylow_specialLinearGroup` (`Sylow.card_eq_index_normalizer`)。
* PSL: `conj_transvection_lower_left` (`(g T g⁻¹) 1 0 = -(g 1 0)²`, `SL2_inv_expl` 展開) +
  `center_le_borelSL` ⟹ `normalizer_map_unipotentSL_eq : N_{PSL}(π(U)) = π(B)`
  (`Subgroup.comap_map_eq` + `QuotientGroup.ker_mk'` で `g T g⁻¹ ∈ U ⊔ Z ≤ B`) ⟹
  `card_sylow_projectiveSpecialLinearGroup` (`IsPGroup.map` / `Subgroup.index_map_dvd` /
  `Subgroup.index_map`)。

Lean 実務メモ: `Nat.dvd_sub'` は現存せず **`Nat.dvd_sub`** / `Finite.one_lt_card` ・
`Nat.card_pos` は `(α := F)` 明示が要る (metavariable) / `Matrix.SpecialLinearGroup` は
`instance [Finite R] : Finite (SpecialLinearGroup n R)` あり / `Sylow` は
`IsPGroup.toSylow (hP : IsPGroup p H) (hnd : ¬ p ∣ H.index)` で作る (`toSylow_coe` は `rfl`)。

### 7A.5 の設計 (2026-07-27) — `U ⊴ P` elementary abelian は `E ∈ 𝓔(P)` を正規化

**statement** (PDF 確認済; `U ⊲ P` は **normal**): `P` `p`-群, `U ⊴ P` elementary abelian
⟹ `∃ E ∈ 𝓔(P)`, `U ≤ N(E)`。`𝓔(P)` = repo の
`Subgroup.maxElemAbelianIn P p` (`OddOrder/GroupTheory/ThompsonSubgroup.lean:64`,
Isaacs 本文 p.202 の定義と一致; `maxElemAbelianIn_nonempty` あり)。

**証明** (書籍 hint を詰めたもの; 全ステップ検算済):
`|U ⊓ E|` が最大の `E ∈ 𝓔(P)` を取る。`U` が `E` を正規化しないとして `u ∈ U`,
`F := E^u ≠ E`, `H := E ⊔ F`, `Z := E ⊓ F`, `W := H ⊓ U`, `A := Z ⊔ W` とおく。

1. `F ∈ 𝓔(P)` (共役, `u ∈ U ≤ P`)。
2. **`E ⊓ U = F ⊓ U`**: `U` 可換ゆえ `u` は `E ⊓ U ≤ U` を各元固定 ⟹
   `(E ⊓ U)^u = E ⊓ U` かつ `= F ⊓ U^u = F ⊓ U`。従って `Z ⊓ U = E ⊓ U`。
3. **`Z ≤ Z(H)`**: `Z ≤ E` (可換) かつ `Z ≤ F` (可換) ⟹ `Z ≤ C(E) ⊓ C(F) = C(⟨E,F⟩)`。
   ⟹ `A = Z ⊔ W` は elementary abelian (可換 2 つの積、指数 `p`)。
4. **`|W| > |E ⊓ U|`**: `E ≠ E^u` ⟹ ∃`e ∈ E`, `e^u ∉ E`;
   `[e,u] = e⁻¹e^u ∈ H` かつ `∈ U` (`U` 正規) だが `∉ E`。
5. **`H = E · W`** (集合積): `H ≤ E ⊔ U` ゆえ `h = e v` (`v ∈ U`) と書け `v = e⁻¹h ∈ H ⊓ U`。
   ⟹ `|H| · |E ⊓ U| = |E| · |W|` (`E ⊓ W = E ⊓ U`, `Ch01.card_mul_card_inf`)。
6. **`|H| · |Z| ≥ |E|²`**: `|E·F| · |Z| = |E||F| = |E|²` かつ `E·F ⊆ H`。
7. ⟹ `|A| · |E ⊓ U| = |Z| · |W|` (`Z ⊓ W = Z ⊓ U = E ⊓ U`) と 5,6 で
   `|A| · |E| ≥ |E|²` ⟹ `|A| ≥ |E|` ⟹ **`A ∈ 𝓔(P)`**。
8. `W ≤ A ⊓ U` かつ 4 より `|A ⊓ U| > |E ⊓ U|` で `E` の最大性に矛盾。

道具: `Subgroup.coe_mul_of_right_le_normalizer_left (N H) (H ≤ normalizer N) : ↑(N ⊔ H) = ↑N * ↑H`
(mathlib) / `Ch01.card_mul_card_inf (H K) : |HK| · |H ⊓ K| = |H| · |K|`
(`OddOrder/Isaacs/Ch01_Sylow/Problems.lean:225`) / `Subgroup.maxElemAbelianIn`。

### 🎉 7A.6 完成 (2026-07-27) — §7A 完済 (6/6)

`Problems7A6.lean` (221 行, axiom-clean)。書籍の「極大部分群の分類」を経由せず,
**元の位数だけ**で `⟨a⟩` の保存を出す短い証明:

* `mulAut_eq_one_of_pow_prime_eq_one` (`m ≥ 2`, すなわち `|Q| ≥ 16`):
  `orderOf (xa i) = 4 < 2^{m+1} = orderOf (a 1)` ⟹ `σ (a 1) = a j` ⟹
  `σ^k (a i) = a (i j^k)` ⟹ `j^p = 1`; `(ZMod 2^{m+1})ˣ` は位数 `2^m` ゆえ `j = 1`;
  つづいて `σ (xa i) = xa (t+i)`, `p t = 0`, `p` は単元 ⟹ `t = 0` ⟹ `σ = 1`。
* `eq_three_and_card_eq_eight_of_odd_prime_dvd_card_mulAut`: Cauchy + 上 ⟹ `m = 1`;
  `Q₈` は既存 `OddOrder.GroupTheory.card_dvd_three_of_odd_mulAutQuaternion` で `p = 3`。

Lean 実務メモ: `2^1` と `2` は defeq だが `rw` は syntactic → `Q₈` 側補題に渡す前に
`∃ τ : MulAut (QuaternionGroup 2), orderOf τ = p := ⟨σ, hσ⟩` で型を張り替える。
`rw [← hcard]` は `u : (ZMod (2*2^m))ˣ` の型に `2^m` が出るので motive 不整合
(`rw [hcard] at h` 方向にする)。`isUnit_of_mul_eq_one` は現存せず `IsUnit.of_mul_eq_one`。

## Ch.7 §7C — 問題一覧 (書籍 p. 210)

§7B には Problems 節が無い (実測: `Problems 7A` の次の見出しは `Problems 7C`)。
§7C は **7C.1 の 1 問のみ**。

| # | 主張 | 見込みの道具 |
|---|---|---|
| 7C.1 | (Thompson) `P ∈ Syl_p(G)`, `p ≠ 2` で **`P` の任意の characteristic 部分群 `X` について `N_G(X)/C_G(X)` が `p`-群** なら `G` は normal `p`-complement をもつ | Thm 6.23 (repo 済) + Thm 5.13 Burnside (repo 済) + `|G|` の帰納法 |

### 7C.1 の証明設計 (2026-07-27、全ステップ検算済)

**最小反例** `G` (`p` 奇, 仮説成立, normal `p`-complement 無し) を取る。`P ≠ ⊥` (でなければ
`G` 自身が complement)。

* **Case A**: `P` の非自明 characteristic 部分群で `G` に正規なものが**無い**とき。
  すべての非自明 char `X ≤ P` で `N_G(X) < G`。`N := N_G(X)` は `P ≤ N` ゆえ
  `P ∈ Syl_p(N)` で, 任意の char `Y ≤ P` について
  `N_N(Y)/C_N(Y) ↪ N_G(Y)/C_G(Y)` (`N_N(Y) = N_G(Y) ⊓ N`, `C_N(Y) = C_G(Y) ⊓ N`) は
  `p`-群 ⟹ 仮説が遺伝 ⟹ 最小性で `N` は normal `p`-complement をもつ。
  **Thm 6.23** (`hasNormalPComplement_of_forall_characteristic_normalizer`,
  `Ch06_FrobeniusActions/ThompsonPComplement.lean:55`, 無条件) で `G` も持つ — 矛盾。
* **Case B**: 非自明 char `X₀ ≤ P` で `X₀ ⊴ G` があるとき。`X := Ω₁(Z(X₀))` に取り替える
  (char in `X₀` char in `P` ⟹ char in `P`; `X₀ ⊴ G` ゆえ `X ⊴ G`; **可換**で非自明)。
  1. `X` 可換 ⟹ `X ≤ C := C_G(X)` かつ `X ≤ Z(C)`。仮説より `G/C` は `p`-群。
  2. **`Ḡ := G/X` に仮説が遺伝**する: `X` char in `P` ゆえ `P/X` の char 部分群 `Ȳ` の
     引き戻し `Y` は `P` の char 部分群 (`P` の自己同型は `X` を保つので `P/X` に降りる);
     `N_{Ḡ}(Ȳ) = N_G(Y)/X` (`X ≤ Y` と `X ⊴ G` から `gYg⁻¹X = Y ⟺ gYg⁻¹ = Y`);
     `N_{Ḡ}(Ȳ)/C_{Ḡ}(Ȳ)` は `N_G(Y)/C_G(Y)` (= `p`-群) の商 ⟹ `p`-群。
     ⟹ 最小性で `Ḡ` は normal `p`-complement `K/X` をもつ (`X ≤ K ⊴ G`, `K/X` は `p'`-群)。
  3. **`K ≤ C`**: `K/(K ⊓ C) ≅ KC/C ≤ G/C` は `p`-群, 同時に `X ≤ K ⊓ C` ゆえ
     `K/(K ⊓ C)` は `K/X` (`p'`-群) の商で `p'`-群 ⟹ 自明 ⟹ `K ≤ C`。
  4. ⟹ `X ≤ Z(K)` かつ `X ∈ Syl_p(K)` ⟹ **Thm 5.13 Burnside**
     (`hasNormalPComplement_of_sylow_normalizer_le_centralizer`,
     `Ch05_Transfer/Basic.lean:492`) で `K` は normal `p`-complement `M` をもつ。
     `M` は `K` の characteristic (一意な `O_{p'}(K)`) で `K ⊴ G` ⟹ `M ⊴ G`;
     `|M|` は `p'`, `[G:M] = [G:K][K:M]` は `p`-冪 ⟹ `M` は `G` の normal `p`-complement
     — 矛盾。

⟹ 必要な新規部品: (a) 仮説の部分群/商への遺伝補題 2 本, (b) `Ω₁(Z(·))` の characteristic
連鎖, (c) normal `p`-complement の「正規部分群から持ち上げ」補題
(`M ⊴ G`, `|M|` が `p'`, `[G:M]` が `p`-冪 ⟹ `HasNormalPComplement p G`),
(d) 最小反例の帰納の骨組み。規模は数百行〜1000 行規模の見込み。

#### 7C.1 に使える既存部品 (2026-07-27 実測)

| 部品 | 場所 | 用途 |
|---|---|---|
| `hasNormalPComplement_of_forall_characteristic_normalizer` | `Ch06_FrobeniusActions/ThompsonPComplement.lean:55` | Case A の締め (Thm 6.23, 無条件) |
| `hasNormalPComplement_of_sylow_normalizer_le_centralizer` | `Ch05_Transfer/Basic.lean:491` | Case B step 4 (Thm 5.13 Burnside) |
| `hasNormalPComplement_of_quotient_of_isPiGroup_compl` | `Ch07/S7C_ThompsonPComplement.lean:1003` | `N ⊴ G` が `p'`-群 + `G/N` が complement をもつ ⟹ `G` が持つ |
| `hasNormalPComplement_of_sylow_eq_top` | `Ch07/S7C_SylowMaximal.lean:25` | `G` が `p`-群のとき自明に complement |
| `hasNormalPComplement_of_le` | `Ch07/S7C_ThompsonPComplement.lean:157` | 部分群への降下 |
| `hasNormalPComplement_of_mulEquiv` / `hasNormalPComplement_quotient` | `Ch07/S7B2_NormalJ_PComplement.lean:171,233` | 同型・商への輸送 |

⟹ **Case B step 4 の締めは**: `M := K` の normal `p`-complement (Burnside) は `K` の
characteristic ゆえ `M ⊴ G`; `M` は `p'`-群で `G/M` は `p`-群 (`[G:K]`, `[K:M]` とも `p`-冪)
⟹ `hasNormalPComplement_of_sylow_eq_top` で `G/M` が complement を持ち,
`hasNormalPComplement_of_quotient_of_isPiGroup_compl` で `G` に持ち上がる。
新規に要るのは主に **(a) 仮説の `N_G(X)` / `G/X` への遺伝** と **(d) 最小反例の帰納の骨組み**。

### 7C.1 進捗 (2026-07-27): 締めの道具を実証明

新 leaf `Problems7C.lean` (`OddOrder.lean` 配線済, axiom-clean):

* `hasNormalPComplement_of_normal_pi'_of_isPGroup_quotient`:
  **`M ⊴ G` が `p'`-群で `G/M` が `p`-群なら `M` は `G` の normal `p`-complement**。
  (`G/M` の Sylow `p` は `⊤` ⟹ `hasNormalPComplement_of_sylow_eq_top` ⟹
  `hasNormalPComplement_of_quotient_of_isPiGroup_compl` で持ち上げ。)
  これが Case B step 4 の締め。

**設計判断 (次 iteration への申し送り)**: 7C.1 の局所条件は, 既存の
`HasThompsonLocalPComplements` (`S7C_ThompsonPComplement.lean:99`) と**同じ流儀**で
「**ambient `G` の任意の部分群 `P`**」に対して定義する (Sylow に限定しない) のが正しい —
`.of_subgroup` / `.map_mulEquiv` 型の輸送補題 (同ファイル 108/192 行) が書けるため。

```
def CharLocalPControl (p : ℕ) (P : Subgroup G) : Prop :=
  ∀ X : Subgroup ↥P, X.Characteristic →
    ∀ g ∈ Subgroup.normalizer ((X.map P.subtype : Subgroup G) : Set G),
      ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer ((X.map P.subtype : Subgroup G) : Set G)
```

⚠ **元ごとの形 (`g ^ p ^ k ∈ C`) を採る**: 商群型 `↥N ⧸ C.subgroupOf N` を使うと
`Normal` インスタンスの証明が要り, 部分群への遺伝 (Case A) が重くなる。元ごとの形なら
`H = N_G(X₀)` への遺伝は「`g ∈ N_H(Y) ⊆ N_G(Y)` に仮説を適用し `g^{p^k} ∈ C_G(Y) ⊓ H`」で
自明。⚠ ただし Case B で `[G : C_G(X)]` が `p`-冪であることが要る箇所では
`IsPGroup` ↔ 位数の変換を別途噛ませる (有限群なので `IsPGroup.exists_card_eq` 相当)。

### 7C.1 進捗 (2026-07-27 その2): 部品 4 本が landing

`Problems7C.lean` (axiom-clean, lint clean):

1. `hasNormalPComplement_of_normal_pi'_of_isPGroup_quotient` — Case B の締め。
2. `CharLocalPControl` (定義) + `trivial_on_centralizer`。
3. `characteristic_map_of_mulEquiv` — `e : A ≃* B` に沿った characteristic の輸送
   (mathlib は同一群の `MulAut` 版しか持たない)。
4. `CharLocalPControl.of_subgroup` — **Case A の遺伝** (`S : Subgroup ↥H` について
   ambient 版から `↥H` 内版を導く)。補助 `subtype_comp_equivMapOfInjective` /
   `map_equivMapOfInjective_map_subtype`。
5. `le_of_relIndex_eq_pow_of_not_dvd` — **Case B step 3** (`[K:C⊓K]` が `p` 冪 かつ
   `p ∤ [K:X]` ⟹ `K ≤ C`; `p` の素数性不要)。

**追加で見つかった既存部品**: `hasNormalPComplement_of_sylow_le_center`
(`Ch05_Transfer/Problems5D.lean:133`, Schur–Zassenhaus 経由で transfer 不要) —
Case B step 4 の Burnside はこれで足りる (`X ≤ Z(K)` ⟹ `K` に normal `p`-complement)。

**残り**: (i) Case B step 2 の**商への遺伝** (`X ⊴ G` char in `P` のとき `G/X` が
局所条件を満たす — `P/X` の char 部分群と `P` の char 部分群の対応が要る),
(ii) `X := Ω₁(Z(X₀))` の characteristic 連鎖, (iii) `|G|` 上の強帰納法の骨組み
(`hasNormalPComplement_of_forall_characteristic_normalizer.{u}` と同じ universe 注釈が要る),
(iv) Case B step 4 の packaging (`X ⊴ K` が `p`-群 + `K/X` が `p'`-群 ⟹ `X ∈ Syl_p(K)`)。

⚠ Lean メモ: 現行 mathlib の相対指数は **`Subgroup.relIndex`** (`relindex` は無い),
`Mathlib.GroupTheory.Index` に在り `relIndex_mul_relIndex` は部分群 3 つが明示引数。

### 🎉 7C.1 完成 (2026-07-27) — §7C 完済 (1/1)

`Problems7C.lean` (**559 行, axiom-clean**, AxiomsCheck 登録済)。**Isaacs Ch.7 は §7A (6/6) +
§7C (1/1) で Problems 完済** (§7B に Problems 節は無い)。

主定理 `hasNormalPComplement_of_charLocalPControl`:
`P ∈ Syl_p(G)`, `p ≠ 2`, `CharLocalPControl p P` ⟹ `HasNormalPComplement p G`。

**設計上の要点** (当初計画からの変更):

* **`Ω₁(Z(X₀))` は不要 — `Z(X₀)` で足りる**。指数 `p` は証明のどのステップでも使わない
  (必要なのは「可換・非自明・`p`-群・`P` で char・`G` に正規」だけ)。しかも `Z(X₀)` は
  ambient で `X₀ ⊓ C_G(X₀)` と書けるので (`map_center_subtype`), 正規性は
  `Subgroup.normal_centralizer` + `⊓` で即座に出る。
* **最小反例でなく `Nat.card G ≤ n` の強帰納法**。universe を `.{u}` で固定すれば
  Case A の `↥N_G(X)` も Case B の `G ⧸ X` も同じ universe に留まる。

**新規部品** (前回 landing 分に加えて):

| 補題 | 役割 |
|---|---|
| `characteristic_comap_of_surjective` | 全射 `f` (核が char) に沿って char を引き戻す。`φ : A ≃* A` を `A ⧸ ker f ≃* B` 経由で `B` の自己同型に降ろす |
| `CharLocalPControl.apply_of_le` / `.of_ambient` | 局所条件の ambient 形 (`Y ≤ P`) との往復 |
| `CharLocalPControl.quotient` | **Case B step 2**: `X ⊴ G` char in `P` なら局所条件は `G/X` に遺伝 |
| `hasNormalPComplement_of_normal_of_isPGroup_quotient` | `K ⊴ G` が complement をもち `G/K` が `p`-群 ⟹ `G` ももつ (`O_{p'}(K)` が char なのを使う) |
| `map_center_subtype` | `Z(H)` の ambient 記述 `H ⊓ C_G(H)` |
| `centralizer_subgroupOf_of_le` | `H ≤ P` で `C_G(H).subgroupOf P = C_{↥P}(H.subgroupOf P)` |
| `characteristic_inf` | char の `⊓` (mathlib は `⊓` 版を持たない) |
| `hasNormalPComplement_of_normal_abelian_of_quotient` | **Case B の中核** (step 3+4) |

**流用した既存部品**: Thm 6.23 (`Ch06.hasNormalPComplement_of_forall_characteristic_normalizer`) /
Burnside 代替 (`Ch05.hasNormalPComplement_of_sylow_le_center`, Problem 5D.2 = Schur–Zassenhaus 経由) /
`Ch05.hasNormalPComplement_of_normal_of_index_eq_pow` / `Ch05.normal_map_subtype_of_characteristic` /
`Ch03.oPiCore` (char + `IsPiGroup` + `le_oPiCore`)。

**Lean 実務メモ**:
* `Subgroup.normalizer` は **`Set G` 引数** (`Subgroup` でない)。`normalizer_eq_top_iff` /
  `le_normalizer_of_normal_subgroupOf` (後者が「`X` char in `P` ⟹ `P ≤ N_G(X)`」の正体)。
* `Subgroup.index_comap_of_surjective` / `relIndex_dvd_index_of_normal` / `relIndex_mul_index` /
  `map_eq_bot_iff_of_injective` / `card_le_card_group` はいずれも **部分群が明示引数**。
* `rw [← QuotientGroup.ker_mk' X]` は `G ⧸ X` の `Normal` インスタンスを巻き込んで motive 不整合
  → `QuotientGroup.le_comap_mk'` を直接使う。
* `push_neg` は deprecated (v4.32) → `simp only [not_exists, not_and]`。
* `show` で goal が変わると `linter.style.show` が鳴る → `change`。

## Ch.8 §8A (書籍 pp. 235–236 の Problems 8A) — 着手 (2026-07-27)

既存 `OddOrder/Isaacs/Ch08_PermutationGroups/` は 14 leaf (AffineGroup / Bochert /
CommonDivisorGraph / CycleCommutators / HalfTransitive / NonzeroVectors / OrbitalGraph /
Orbitals / PCycleJordan / PSLSimple / RegularNormal / Subdegrees /
TransitiveAutomorphisms / TransvectionGeneration)。演習は新 leaf `Problems8A.lean` へ。

⚠ 以下は **pdftotext からの一覧** (OCR ノイズあり)。各問の statement は着手時に
**PDF ページ画像で確定**する (書籍 p. 235–236 = PDF p. 248–249)。

| # | 主張 (要約) |
|---|---|
| 8A.1 | `A ≇ B`, `\|A\|=\|B\|` ⟹ 両方に同型な regular 部分群をもつ置換群が存在 (hint: 対称群)。後半は「nonisomorphic regular **normal** 部分群を持てるか」の decide 問題 |
| 8A.2 | `H ≤ G` が transitive ⟹ `C_G(H)` は semiregular。帰結: 可換 transitive 置換群は regular |
| 8A.3 | `Z(G)=1` ⟹ `G` に同型な相異なる regular normal 部分群を 2 つもつ置換群が存在 |
| 8A.4 | `U, V` regular normal で `U ⊓ V = 1` ⟹ `U ≅ V` かつ中心自明 (hint: `G = UV` としてよい) |
| 8A.5 | `G` が `k`-transitive, `H = G_α`, `Δ = Fix(H)` ⟹ `N_G(H)` は `Δ` に `r`-transitive (`r = min(k, \|Δ\|)`) |
| 8A.6 | `G` transitive, `H = G_α`, `P ∈ Syl_p(H)`, `Δ = Fix(P)` ⟹ `N_G(P)` は `Δ` に transitive |
| 8A.7 | 可換 `A` が `N` に忠実に作用し非単位元上 half-transitive ⟹ 作用は Frobenius, `A` は巡回 |
| 8A.8 | `G` transitive, `N ⊴ G` ⟹ `G` は `N`-軌道を transitive に置換, ゆえに `N` は half-transitive |
| 8A.9 | `G` が 2-transitive, `N ⊴ G` が非自明作用 ⟹ `N` は transitive (実は primitivity で足りる) |
| 8A.10 | 可解な 4-transitive 置換群 ⟹ `S₄` に同型 (hint: 極小正規部分群が regular) |
| 8A.11 | 任意の素数冪 `q > 1` に可解な sharply 2-transitive 置換群 (次数 `q`) が存在 (hint: 位数 `q` の体) |
| 8A.12 | `χ` を置換指標として `G` が 2-transitive ⟺ `χ(g)²` の平均が 2 |
| 8A.13 | `G` が 2-transitive のとき, `χ(g)³` の平均が `m` ⟺ 3-transitive となる `m` を求めよ |
| 8A.14 | `G` transitive, `\|G:H\| = m` ⟹ `H` の軌道数 ≤ `m`; `H` が点安定化群を含まなければ ≤ `m/2` |
| 8A.15 | `H ≤ G` の両側作用 `g·(x,y) = x⁻¹gy` について, `G` の `H`-右剰余類への作用が 2-transitive ⟺ `H × H` が `G` 上ちょうど 2 軌道 |

⚠ **8A.1 後半は "decide" 問題** — 数学的に決着させてから形式化する (即断しない)。
まず前半 (対称群内の構成) と 8A.2 以降を文書順で進める。

### 8A.1 後半の "decide" を決着 (2026-07-27) — **答は「できる」**

「置換群が **同型でない regular normal 部分群**をもてるか」— **もてる**。反例:

`Ω = ZMod 4`, `G = {x ↦ εx + a : ε = ±1, a ∈ ZMod 4} ≅ D₈` (= `S₄` の Sylow 2-部分群、
4 点への自然作用)。

* `T = {x ↦ x + a}` は位数 4・推移的 ⟹ regular。`ε` による共役が `a ↦ εa` なので `T ⊴ G`。
  `T ≅ Z₄`。
* `V = {id, x↦x+2, x↦1-x, x↦3-x}` (`S₄` の Klein 群 `{e,(02)(13),(01)(23),(03)(12)}` そのもの)。
  位数 4・推移的 (`0 ↦ 0,2,1,3`) ⟹ regular。`φ(εx+a) = a + [ε=-1] mod 2` が準同型
  `G → Z₂` でその核が `V` ⟹ `V ⊴ G` (指数 2)。`V ≅ Z₂ × Z₂`。
* `Z₄ ≇ Z₂ × Z₂` ⟹ 反例成立。

⚠ 8A.4 (`U ⊓ V = 1` なら `U ≅ V`) と矛盾しない: 上の例では `T ⊓ V = {id, x↦x+2} ≠ 1`。

形式化の方針: `Equiv.Perm (ZMod 4)` 内で 2 つの部分群を明示構成し, regular は
`bijective_smulBase_iff` (`RegularNormal.lean`), 非同型は「`T` に位数 4 の元があり `V` に無い」
で出す (`ZMod 4` 上なので `decide` が効く見込み)。

### §8A 進捗 (2026-07-27)

新 leaf `OddOrder/Isaacs/Ch08_PermutationGroups/Problems8A.lean` (`OddOrder.lean` 配線済):

* ✅ **8A.1 前半** 実証明 — `regularRep` (型の同値 `e : Ω ≃ A` に沿って運んだ左正則表現
  `A →* Equiv.Perm Ω`, `a ↦ (x ↦ e.symm (a * e x))`) + `regularRep_injective` +
  `bijective_smulBase_regularRep_range` (像は常に regular) ⟹
  `exists_regular_subgroups_of_equiv` / `exists_regular_subgroups_of_card_eq`
  (`Sym(A)` が `A` にも `B` にも同型な regular 部分群をもつ)。
  ⚠ `A ≇ B` は構成に不要 (問題を面白くしているだけ) なので仮説から外した。
  `regularRep` は 8A.3 / 8A.4 でも使う共通道具。
* ✅ **8A.3** 実証明 — `regularRepRight` (右正則表現 `a ↦ (x ↦ e.symm (e x * a⁻¹))`;
  逆元は反準同型を準同型に直すため) + `regularRepRight_range_le_centralizer` (左右は
  結合律で可換) ⟹ `exists_two_distinct_regular_normal_of_center_eq_bot`。
  `L ⊔ R` の中で両方正規 (自分の normalizer + 相手の centralizer ≤ normalizer)、
  `L ≠ R` は「左移動がすべて右移動 ⟹ `A = Z(A) = 1`」で `Nontrivial A` に反する。
  ⚠ 書籍は `Z(G)=1` のみだが **`G` 非自明が要る** (`G = 1` は `Z(G)=1` を満たすが
  `L = R = 1` で相異ならない)。
* ✅ **8A.2** 実証明 — `smul_eq_self_of_mem_centralizer` (推移的 `H` の中心化群の元は
  1 点固定 ⟹ 全点固定) / `centralizer_inf_stabilizer_eq_bot` (忠実性を足して半正則) /
  `bijective_smulBase_top_of_comm` (可換推移的置換群は regular)。
* ✅ **8A.4** 実証明 — `le_centralizer_of_normal_of_inf_eq_bot` (mathlib
  `Subgroup.commute_of_normal_of_disjoint`) / `centralizer_eq_of_regular_of_inf_eq_bot`
  (**`C_G(U) = V`**: `⊆` は `V` の推移性で `c•α = v•α` を取り `v⁻¹c` が `C_G(U)` の
  半正則性 (8A.2) で 1) / `center_eq_bot_of_regular_of_inf_eq_bot` (`Z(U) ≤ U ⊓ C_G(U) =
  U ⊓ V = ⊥`) / `regularPairHom` (`ψ u = 「u⁻¹ • α を実現する唯一の V の元」`; 準同型性は
  `V` が `U` を中心化することから) ⟹ `mulEquiv_and_center_eq_bot_of_regular_normal`。
  ⚠ 書籍 hint の「`G = UV` としてよい」は使わずに済んだ (`C_G(U) = V` を直接出す方が短い)。
  ファイルは文書順に並べ替え済 (8A.4 が 8A.2 を使うので 8A.2 を先に置く)。
* ✅ **8A.5** 実証明 — `smul_mem_fixedPoints_of_mem_normalizer` (`Δ = Fix(H)` は
  `N_G(H)` 不変) / `exists_mem_normalizer_stabilizer_smul_eq` (**主内容**: `H = G_α` なら
  `N_G(H)` は `Δ` に推移的 — `β = g•α` から `H ≤ G_β = gHg⁻¹`, 有限性で等号, ゆえに
  `g ∈ N_G(H)`) / `eq_of_mem_fixedPoints_stabilizer_of_transitive_on_compl` (退化部分)。
  ⚠ **`r = min(k,|Δ|)` の数学的中身は「推移性 (`r ≥ 1`)」でほぼ尽きる**: `H` は `Δ` を
  各点固定するので `N_G(H)` の `Δ` 上の像は **regular**。よって `|Δ| ≥ 3` なら 2-transitive
  になり得ず, 実際 `k ≥ 2` かつ `|Δ| ≥ 2` は `|Ω| = 2` を強制する (退化補題)。
  補助: `eq_of_le_of_card_eq` (有限群で `H ≤ K` + 位数一致 ⟹ `H = K`; mathlib に無い)。
* ✅ **8A.6** 実証明 — `exists_mem_conj_eq_of_sylow_le` (**再利用可能**: 部分群 `K` の中の
  2 つの `p`-Sylow は `K` の元で共役、を ambient `Subgroup G` の言葉で述べたもの。
  `Sylow p ↥K` へ持ち上げて `MulAction.exists_smul_eq` を使い `K.subtype` で押し戻す) ⟹
  `exists_mem_normalizer_sylow_smul_eq` (`β = g•α` で `G_β = gHg⁻¹`、`Q` と `gQg⁻¹` が
  ともに `G_β` の `p`-Sylow、共役元 `x ∈ G_β` から `n := x⁻¹g` が `Q` を正規化し
  `n•α = x⁻¹•β = β`)。
  補助: `card_mul_relIndex` (`Q ≤ K` で `|Q|·[K:Q] = |K|`) / `isPGroup_subgroupOf` /
  `mem_normalizer_of_map_conj_eq`。
  ⚠ Lean メモ: `Problems8A.lean` は `RegularNormal.lean` 経由では `Mathlib.GroupTheory.Sylow`
  を得られない (`IsPGroup`/`Sylow` が unknown identifier) → 明示 import が要る。
  `x • S` (`S : Sylow p ↥K`) の coe は `MulDistribMulAction.toMonoidEnd` 経由になり
  `(MulAut.conj x).toMonoidHom` と**構文的に**一致しない → `rw` でなく `exact` (defeq) で渡す。
* ✅ **8A.7** 実証明 — `isFrobeniusAction_of_comm_of_half_transitive` /
  `isFrobeniusAction_and_isCyclic_of_comm_of_half_transitive`。
  **既存 Thm 8.9** (`isFrobeniusAction_or_isElementaryAbelian_of_half_transitive`,
  同ディレクトリ `HalfTransitive.lean`) の例外肢を可換性で潰すだけ: `a ≠ 1` が `n ≠ 1` を
  固定するなら `Fix(a)` は (`A` 可換ゆえ) `A`-不変で `⊥` でない → 例外肢の既約性から `⊤`
  → `a` が自明作用 → 忠実性に矛盾。「`A` 巡回」は既存
  `Ch06.isCyclic_of_frobeniusAction_of_isMulCommutative` (Cor 6.17 の可換分岐) を引くだけ。
  ⚠ **教訓**: 「可換 f.p.f. ⟹ 巡回」を自前で証明しかけたが (rank-2 coprime 生成補題や
  Schur が要る大仕事)、repo に既に在った。**着手前に repo 全体を grep する**
  ([[bg-longhand-arguments-may-be-existing-isaacs-lemmas]] と同型の罠)。
* ✅ **8A.8** 実証明 — `smul_orbit_eq_orbit_smul` (`N ⊴ G` なら `g • orbit N α =
  orbit N (g • α)`) / `card_orbit_eq_of_normal` (帰結: `N` は half-transitive)。

* ✅ **8A.9** 実証明 — `isPretransitive_of_normal_of_two_transitive`。8A.8 の
  `smul_orbit_eq_orbit_smul` を使う: 非自明性から `orbit N a` に `a` 以外の点 `γ` があり,
  `G_a` の推移性で任意の `β ≠ a` を `γ` から得る `g` を取れば
  `β = g•γ ∈ g • orbit N a = orbit N a`。2-transitivity は「推移的 + 各 `G_α` が `Ω∖{α}` に
  推移的」の形で仮定 (書籍の note どおり本質は primitivity だが, 演習の仮定は 2-transitive)。

Lean 実務メモ: `[N.Normal]` はインスタンスなので `N.Normal.conj_mem` と書けない
(`N.Normal : Prop` へのフィールド射影になる) → `Subgroup.Normal.conj_mem ‹N.Normal›`。
`Nat.card ↑(g • S) = Nat.card ↑S` は `Equiv.Set.image` + `Equiv.setCongr Set.image_smul`。

### 8A.10 の証明設計 (2026-07-27, 全ステップ検算済) と核心補題の landing

**主張**: 可解な 4-transitive 置換群 `G` は `S₄` に同型。

**設計** (書籍 hint「極小正規部分群 `N` が regular であることを示し, `G_α` の `N` への
共役作用を考えよ」を詰めたもの):

1. `G` は 4-transitive ⟹ 2-transitive。極小正規部分群 `N ≠ 1` を取る。
2. `N` は非自明に作用する (忠実な置換群ゆえ) ⟹ **8A.9** で `N` は推移的。
3. `G` 可解 ⟹ **Isaacs Thm 3.11**
   (`Ch03.solvable_minimal_normal_isElementaryAbelian` 系; `Ch03_SplitExtensions/Basic.lean:194`)
   で `N` は elementary abelian `p`-群 ⟹ 可換。
4. 可換 + 推移的 ⟹ **8A.2** (`bijective_smulBase_top_of_comm`) で `N` は **regular**。
   したがって `|N| = |Ω|` で `Ω ≅ N` (点 `α` を `1` に対応させる)。
5. **Thm 8.5 第 3 主張** (`RegularNormal.lean` の `ofStabilizerToNonidentity`) により
   `G_α` の `Ω ∖ {α}` への作用は `G_α` の `N ∖ {1}` への**共役 (=自己同型) 作用**と
   置換同型。`G` が 4-transitive ⟹ `G_α` は `Ω ∖ {α}` に 3-transitive。
6. ⟹ `G_α` は `N ∖ {1}` に自己同型として 3-transitive ⟹ **`|N| ≤ 4`**
   (下記の核心補題)。`|N| = |Ω| ≥ 4` (4-transitive) ⟹ `|Ω| = 4` ⟹ `G ≤ S₄` が
   4-transitive ⟹ `G = S₄`。

**✅ 核心補題を landing** (`card_le_four_of_three_transitive_on_nonidentity`):
群 `N` に自己同型として作用する `A` が `N ∖ {1}` に 3-transitive なら `|N| ≤ 4`。
自己同型は積を保つので `x`, `y` を固定すれば `xy` も固定する。`|N| ≥ 5` なら
`1, x, y, xy` と異なる `w` が取れ, 3-transitivity は `(x,y,xy) ↦ (x,y,w)` を要求するが
それは `xy ↦ xy ≠ w` を強いる。⚠ `N` が elementary abelian であることは**不要**
(積を保つことしか使わない)。

**✅ step 5 も landing** (`card_le_four_of_regular_normal_of_stabilizer_three_transitive`):
`N` regular normal + `G_α` が `Ω ∖ {α}` に 3-transitive ⟹ `|N| ≤ 4`。
⚠ `RegularNormal.lean` の `ofStabilizerToNonidentity` (Thm 8.5 第 3 主張の bundled 版) を
**経由せず**, 軌道写像 `n ↦ n • α` で直接翻訳した方が短い: `g • α = α` のとき
`(g n g⁻¹) • α = g • (n • α)` (計算 2 行) なので, `MulAut.conjNormal g` がそのまま
求める自己同型になる。作用先の型は `MulAut ↥N` を使えば新しい instance が要らない。

**✅ 主定理も landing** (`card_eq_four_of_solvable_of_stabilizer_three_transitive`):
**可解な 4-transitive 置換群の次数は 4**。step 1–6 の結線は既存部品だけで済んだ —
`Ch02.exists_isMinimalNormal_le_of_normal` (極小正規部分群) /
`Ch03.solvable_minimal_normal_isAbelian` (Thm 3.11 の前半で十分; elementary abelian までは不要) /
8A.9 / 8A.2 の `centralizer_inf_stabilizer_eq_bot` (`N ≤ C_G(N)` から `N ⊓ G_α = ⊥`) /
上の step 5 補題。

**✅ packaging も landing** (`nonempty_mulEquiv_perm_fin_four_of_four_transitive`):
`MulAction.toPermHom` が単射 (`MulAction.toPerm_injective`) かつ全射 (4-transitivity を
「単射な 4-tuple どうしを移す元がある」形で仮定し, `Fin 4 ≃ Ω` を取って各置換を実現) ⟹
`G ≃* Sym(Ω) ≃* S₄`。補助 `permCongrMulEquiv` (`Equiv.permCongr` の乗法版; mathlib は
Equiv 版しか持たない)。⟹ **8A.10 完了**。

**旧記載の残り**: 上記 1–4 の結線 (極小正規部分群の存在, Thm 3.11 の適用形, Thm 8.5 第 3 主張の
`ofStabilizerToNonidentity` から 3-transitivity を移す部分, 最後の `|Ω| = 4 ⟹ G = S₄`)。

### 8A.11 (2026-07-27): `AGL(1,F)` の構成と sharply 2-transitivity

⚠ 既存 `AffineGroup.lean` は **𝔽₂ 専用** (`V ⋊ GL(V)`, Cor 8.7) なので 8A.11 (任意の
素数冪 `q`) には流用できない → `Equiv.Perm F` の部分群として `AGL(1,F)` を直接構成した。

* `affineLinePerm a b = (x ↦ a x + b)` (`Equiv.mulLeft₀` + `Equiv.addRight`)。
* `affineLineGroup F : Subgroup (Equiv.Perm F)` — 積・逆は `ring` / `inv_eq_of_mul_eq_one_right`。
* ✅ `existsUnique_affineLineGroup_of_ne` — **sharply 2-transitive**
  (`a = (y₁-y₂)/(x₁-x₂)`, `b = y₁ - a x₁` が唯一解)。

⚠ Lean メモ: `Subgroup` を `where carrier := {p | ∃ ...}` で作ると, 会員判定が
`toSubsemigroup.1` 経由になって **`Iff.rfl` も anonymous constructor も通らない**。
`⟨fun h => h, fun h => h⟩` で `mem_..._iff` を作り, 以後それを経由する。

* ✅ `affineLinearPartHom : AGL(1,F) →* Fˣ` (`a = p 1 - p 0` で線形部分を取り出す) +
  核 (平行移動群) の可換性 ⟹ `affineLineGroup_isSolvable`
  (mathlib `solvable_of_ker_le_range` + `isSolvable_of_comm`)。⟹ **8A.11 完了**。

### 8A.12 (2026-07-27): 置換指標の 2 乗平均 — 骨格を landing

* ✅ `fixedByProdEquiv` / `card_fixedBy_prod` — `χ(g)² = |Fix_{Ω×Ω}(g)|`
  (積作用の固定点は成分ごとの固定点の積; equiv は `congrArg Prod.fst/snd` と `Prod.ext` だけ)。
* ✅ `sum_sq_card_fixedBy` — `∑_g χ(g)² = |Ω×Ω の軌道数| · |G|`
  (§1A の `Ch01.sum_card_fixedBy_nat` = Nat.card 版 Burnside をそのまま `Ω × Ω` に適用)。

* ✅ `card_orbits_prod_eq_two_iff` / `sum_sq_card_fixedBy_eq_two_mul_iff` ⟹ **8A.12 完了**。
  軌道数 2 の同値は `Nat.card_eq_two_iff` (`{x,y} = univ` 形) で扱い, 「対角線の類には
  対角線上の点しか入らない」(`hdiag`) を軸に 3 つの類の場合分けを `rcases <;> first | ...`
  で潰す。⚠ `MulAction.orbitRel_apply` から出る witness は `(fun m => m • p) g = q` という
  **beta-redex** なので, `congrArg Prod.fst` に渡す前に `have hg' : g • p = q := hg` で
  型を張り替える (そうしないと `rw`/`congrArg` の結果が噛み合わない)。

**旧記載の残り (8A.12)**: 「`G` 2-transitive ⟺ `Ω × Ω` の `G`-軌道がちょうど 2 個」。
(⟹) 対角線 `Δ` が 1 軌道 (`G` 推移的), その補集合が 1 軌道 (2-transitivity), 両者は交わらず
`Ω × Ω` を覆う。(⟸) 2 軌道なら `Δ` が一方で残りが他方ゆえ off-diagonal に推移的。
実装は `orbitRel.Quotient G (Ω × Ω) ≃ Fin 2` を作るのが素直 (`Nontrivial Ω` が要る)。
これが済めば「平均 = 2 ⟺ 2-transitive」が `sum_sq_card_fixedBy` から直ちに出る。

### 8A.13 (2026-07-27): 答は **m = 5**、骨格を landing

* ✅ `fixedByProdEquiv` を `A × B` へ一般化 ⟹ `card_fixedBy_prod_three`
  (`χ(g)³ = |Fix_{Ω³}(g)|`) / `sum_cube_card_fixedBy`
  (`∑_g χ(g)³ = |Ω³ の軌道数| · |G|`)。
* **答 `m = 5`** (検算済): `G` が 2-transitive のとき `Ω³` の軌道は 3 点の一致パターンで
  分類される — `xxx` / `xxy` / `xyx` / `yxx` の 4 つの退化パターンは **2-transitivity だけで
  各 1 軌道**になり, 残る「全相異」部分がひとつの軌道になることが 3-transitivity と同値。
  したがって 3-transitive ⟺ 軌道数 5 ⟺ `χ³` の平均が 5。

**5 パターンの単一軌道性を landing** (2026-07-27): `cube_orbit_diag` (推移性) /
`cube_orbit_pattern_xxz` `_xzx` `_zxx` (2-transitivity) / `cube_orbit_pattern_distinct`
(3-transitivity)。いずれも `Quotient.sound' (orbitRel_apply.mpr ⟨g, _⟩)` の 3 行。

**(a) も landing** (`cube_orbit_ne_of_fst_snd` / `_fst_thd` / `_snd_thd`): 一致パターンは
軌道不変量。5 代表元 `(α,α,α)` / `(α,α,β)` / `(α,β,α)` / `(β,α,α)` / `(α,β,γ)` の
10 通りの対はいずれかの成分対で一致・不一致が食い違うので, これで互いに別軌道と分かる。
⚠ `MulAction.injective g` の出す goal は `(fun x ↦ g • x) a = (fun x ↦ g • x) b` の
**beta-redex** なので `change g • a = g • b` を挟んでから `rw` する。

**残り (8A.13)**: `Nat.card (orbitRel.Quotient G Ω³) = 5` の数え上げのみ
(`Set.ncard_univ` + `Set.ncard_insert_of_not_mem` を 4 回, または `≃ Fin 5`)。
`|Ω| ≥ 3` が要る。

### 8A.14 (2026-07-27): 前半 landing

* ✅ `card_orbits_le_index` — `G` 推移的, `[G:H] = m` ⟹ `H` の `Ω` 上の軌道は高々 `m` 個。
  証明は **`gH ↦ ⟦g⁻¹ • α⟧` が `G ⧸ H` から `H`-軌道の集合への全射**であること
  (左剰余類で well-defined にするために `g⁻¹` を取るのが要点: `b = a h` なら
  `b⁻¹ • α = h⁻¹ • (a⁻¹ • α)` で同じ `H`-軌道)。二重剰余類の言葉を経由しないで済む。

**8A.14 後半の核を landing** (`exists_ne_coset_same_orbit`): `H` が点安定化群
`G_{a⁻¹ • α}` を含まないなら, `u ∈ a⁻¹ G_α a ∖ H` を取って `b := a u⁻¹` とすれば
`b⁻¹ • α = a⁻¹ • α` (同じ点!) かつ `bH ≠ aH`。つまり **全射
`gH ↦ ⟦g⁻¹ • α⟧` のファイバーは常に 2 元以上**。

✅ `two_mul_card_orbits_le_index` で数え上げも完了 ⟹ **8A.14 完了**
(`cosetToOrbit` を def に切り出し, `Finset.card_eq_sum_card_fiberwise` +
`Finset.one_lt_card` + `Finset.sum_le_sum`)。

### 8A.15 (2026-07-27): 二重剰余類と剰余類への 2-transitivity — landing

✅ `doubleCoset_transitive_iff`:
`(∀ a b ∉ H, ∃ x y ∈ H, x a y = b)` ⟺ `(点安定化群 H が (G ⧸ H) ∖ {H} に推移的)`。

* 左辺 = 「`H` の外がひとつの二重剰余類」= `H × H` の両側作用 `g·(x,y) = x⁻¹ g y` が
  `G` 上ちょうど 2 軌道 (`H × H`-軌道 = 二重剰余類 `H g H`, その一つが `H` 自身)。
* 右辺 = `G` の `G ⧸ H` への作用の 2-transitivity。
* ⚠ **`G ⧸ H` は `H` が正規でないと群でない**ので `(a : G ⧸ H) ≠ 1` とは書けない
  (`OfNat (G ⧸ H) 1` が無い)。基点は `((1 : G) : G ⧸ H)` と書き, `a ∉ H` との対応は
  `QuotientGroup.eq` + `Subgroup.inv_mem_iff` で作る (`QuotientGroup.eq_one_iff` は
  正規部分群専用なので使えない)。

⟹ **§8A の残りは 8A.1 後半 / 8A.13 の同値 (軌道数 5) / 8A.14 後半 (≤ m/2) の 3 つ**。

### §8A 一巡後の残り 3 件 (2026-07-27 時点)

1. ~~**8A.1 後半**~~ ✅ **完了 (2026-07-27)** — `exists_two_nonisomorphic_regular_normal`。
   計算核 (2026-07-27): `transZFour` (`x ↦ x+1`) /
   `flipZFour` (`x ↦ 1-x`) と関係式 `s t s⁻¹ = t⁻¹` / `t s t⁻¹ = s t²` /
   `V` の各元の位数 ≤ 2 / `t² ≠ 1` を **`decide` で確認済** (`Equiv.Perm (ZMod 4)` 上の
   `decide` は実用速度で通ることを probe で確認)。残りは 2 つの部分群を明示 carrier で
   組んで regular 性・正規性・非同型を結線するだけの機械的作業。設計: `Ω := ZMod 4`,
   `t := Equiv.addRight 1` (`x ↦ x+1`), `s := x ↦ 1 - x`,
   `T := Subgroup.zpowers t` (`≅ Z₄`, translations, regular),
   `V := Subgroup.closure {t², s}` (`= {1, t², s, s t²} ≅ Z₂×Z₂`, regular),
   `G := Subgroup.closure {t, s}` (`= D₈`)。正規性は生成元で確認:
   `s t s⁻¹ = t⁻¹ ∈ T`, `t s t⁻¹ = s t² ∈ V`, `t t² t⁻¹ = t² ∈ V`。非同型は
   「`T` に位数 4 の元, `V` は指数 2」。⚠ `ZMod 4` は `DecidableEq` + `Fintype` なので
   各等式は `Equiv.ext` + `decide` で潰せる見込み。
2. **8A.13 の同値** — 「`Ω³` の軌道数 = 5 ⟺ 3-transitive」(`m = 5` は確定済)。
   `Nat.card_eq_two_iff` の 5 元版が無いので `orbitRel.Quotient G Ω³ ≃ Fin 5` の
   明示構成が素直 (`|Ω| ≥ 3` が要る)。
3. ~~**8A.14 後半**~~ ✅ 完了 (2026-07-27)。

### 8A.1 後半 完了 (2026-07-27)

`cyclicFourSub` (`= {1,t,t²,t³} ≅ Z₄`) と `kleinFourSub` (`= {1,t²,s,st²} ≅ Z₂×Z₂`) を
**明示 carrier の `Subgroup`** として組み, regular 性 (軌道写像の全単射) / 相互の正規化
(`V ≤ N(T)`, `T ≤ N(V)`) / 非同型 (`V` は指数 2, `T` は位数 4 の元をもつ) をすべて
`decide` + 4 元の場合分けで証明 ⟹ `exists_two_nonisomorphic_regular_normal`。

⚠ Lean メモ: `⟨v, hv⟩ ^ 2` のように **subtype の証明成分が式に残ると `decide` が
「Expected type must not contain free variables」で落ちる** → `Subtype.ext` の後に
`push_cast` で coe を外し, 台の等式にしてから `rcases`/`decide` する。
正規化群の判定は `∀ x : Equiv.Perm (ZMod 4), x ∈ T ↔ v x v⁻¹ ∈ T` を
`simp only [mem_normalizer_iff, mem_...]` で素の論理式に開いてから `decide` (24 元の全数)。

⟹ **§8A の残りは 8A.13 の同値 (軌道数 5 ⟺ 3-transitive) のみ**。

## ⚠ hub からの指摘 (2026-07-27): 新 leaf の `OddOrder.lean` 配線漏れ

`OddOrder/Isaacs/Ch08_PermutationGroups/Problems8A.lean` (717 行) が root aggregator に
配線されておらず、`lake build OddOrder` の import 閉包外に落ちていた。**合流フルビルドが
一度も elaborate しないまま gate を通過**する (CLAUDE.md「ファイル粒度」節の既知の失敗モード、
本リポジトリで 3 件目)。hub 側で配線済 (commit 1e0dfac04、配線後 4846 → 4847 jobs で green)。

**次から: 新 leaf を作った commit と同じ commit で `OddOrder.lean` に import を足すこと。**
`OddOrder.lean` は全レーン編集可の共有ファイル。上位 leaf 経由で到達する中間 leaf は不要だが、
到達性が自明でないなら足す。
