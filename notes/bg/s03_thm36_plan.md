# BG Theorem 3.6 形式化プラン (§3 p-length-one サブプログラム, 2026-06-07)

worktree `bg-s10-spine`。§10 スパインの根本ブロッカー (10.6 経由) として着手。
**Thm 3.6 は単独定理でなく §3 サブツリーの頂点**である。下から積む。

## Thm 3.6 (mmd L955)

「`G` 可解奇数位数, `H ⊴ G` normal Hall, `R` を `H` の補群, `R₀ ≤ R` prime order `r` で
`C_H(R₀)` が Z-群。任意素数 `p` で `[H,R]` は p-length one」。
証明 = 最小反例法、~4 ページ、equation (3.6)–(3.38)。

### 証明フェーズ (equation 番号)
- **Phase A 還元** (3.6)–(3.11): `H=[H,R]` (3.6); 商帰納 (3.7); `O_{p'}(H)=1` (3.8, **Lem 1.21(b)**);
  `V=F(H)=O_p(H)` elementary abelian (3.9, **Lem 1.21(c)** + Lem 1.7/Thm 1.8/Prop 1.3); `C_H(V)=V`
  (3.10, Prop 1.3); `V` に唯一の minimal normal (3.11, **Lem 1.21(e)**)。
- **Phase B 補群 K の構造** (3.12)–(3.16): `U=preimage F(H/V)`, `K`= R-不変補群 (Prop 1.5a + S-Z);
  Frattini で `H=VN_H(K)` (3.12); `[K,P]≠1` (3.13); `[V,K]=V, C_V(K)=1` (3.14, Prop 1.6d + 3.11);
  `K=F(N_H(K))` (3.15); `C_H(K)⊆K` (3.16, Prop 1.3)。
- **Phase C R₀ の作用** (3.17)–(3.21): `[K,R₀]≠1` (3.17, Prop 1.4); `C_{KR₀}(V)=1` (3.18);
  `C_V(R₀)≠1` ⟸ **Thm 3.4** (3.18→faithful→[K,R₀]=1 矛盾); `|C_V(R₀)|=p` (3.19, Z-群); `C_P(R₀)=1`
  (3.20, Z-群); `P=[P,R₀]` (3.21, Prop 1.6a)。
- **Phase D G の構造確定** (3.22)–(3.31): 最小性帰納で `[X,P]=1 (X=X^{PR}⊂K)` (3.22); `G=VKPR₀`,
  `H=VKP, R=R₀` (3.23); `K=[K,P]` (3.24, Prop 1.6b); `K` は special q-群 (**Gorenstein 5.3.7**)
  + `C_{K/K'}(P)=1` (3.25); `K` exp q (3.26, Thm 1.13); `C_{PR}(K)=1` (3.28); `C_{PR}(K/K')=1`
  (3.29, Thm 1.8); `C_{K/K'}(R)≠1` (3.30, **Thm 3.4**); `|C_K(R)|=q, C_K(R)∩K'=1` (3.31, Z-群 + 3.26)。
- **Phase E K elementary abelian** (3.32)–(3.37): `K≠[K,R]` (3.32); `C_{[K,R]}(R)=1` (3.33);
  `[K,R]R` Frobenius (Lem 3.1); **Thm 3.5** で `[K,R]` abelian (3.34); `[K,R]` not P-invariant
  (3.35); `|K:Z(K)|≤q` ⟸ **Thm 2.6(a)** (✅) ⟹ `K` elem abelian (3.36); `|K|>q²` (3.37, Thm 2.6)。
- **Phase F 最終矛盾** (3.38–): `V=⊕V_i` (V_i=C_V(K_i)≠1, index-q K_i; **Prop 1.16** ✅);
  `RP` transitive on {V_i} (3.11); orbit 長さ解析 + `|V_1|=p` (3.19) + parity (n odd vs even) で矛盾。

## 依存サブツリーと状態

| 依存 | mmd | 状態 | 備考 |
|---|---|---|---|
| **Lem 1.21(a)** | L566 | ✅ | `hasPLengthOne_subgroup` (= p-length 部分群単調性, **10.6 でも必要**) |
| **Lem 1.21(b)** | L567 | ✅ | `hasPLengthOne_of_isPiPrime_normal_quotient`。(3.8) で使用 |
| **Lem 1.21(c)** | L568 | ✅ | `hasPLengthOne_of_isPGroup_normal_quotient`。(3.9) |
| **Lem 1.21(d)** | L569 | — bypass | `⟨p-elements⟩` 特徴づけ。(e) を product-core 経由にしたので不要 |
| **Lem 1.21(e)** | L570 | ✅ | `hasPLengthOne_of_inf_eq_bot`。(3.11)。product 埋め込み + (a) |
| **Thm 3.4** | L863 | ❌ 未 (本体) | 可解奇 G, normal Hall K + prime-order 補群 R, V 上 (char∤\|G\|), `C_V(R)=0 ⇒ [R,K]⊆C_K(V)`。reduction は Maschke/Prop1.5/Lem3.1/Lem3.3 で組める。**真の残り = BG §2 (Thm 2.5)**、Gorenstein 系は下記の通り被覆済 |
| **Thm 3.5** | L903 | ❌ 未 | Frobenius G=KR (K 可解, R cyclic prime), V 上, `C_V(R) 1-dim ⇒ K'⊆C_K(V)`。Clifford/Maschke/Wedderburn/Prop2.2/Lem3.3 |
| **Lem 3.3** | L845 | ✅ | S03b_Lemma33 `kernel_acts_trivially_of_centralizer_eq_bot` 等 |
| **Lem 3.1** | — | ✅ | S03 `isFrobeniusGroup_iff_complement_centralizer_inf_kernel_eq_bot` |
| **Gorenstein 5.3.7** (BG 番号; = 当 ed. **Gor 3.7/3.8/3.10**) | — | ✅ **被覆済** | coprime minimal 作用 ⇒ special + irred on K/K' + trivial K'。`S04e_GorThm37.exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction_with_minimality` (sorry-free, AxiomsCheck:1250)。BG 3.4 では K に適用 (existence-of-minimal → K=Q bridge は §3.4 内部) |
| **Gorenstein 3.2.2** (Z(G) cyclic) | — | △ ほぼ被覆 | faithful irreducible ⇒ Z(G) cyclic。ℂ 版 machinery = Isaacs CTFG Cor 2.30 `SchurCenterBound.lean` (`exists_central_scalar` 他, sorry-free)。一般体 F 版 capstone = Schur→`Module.End` division ring + mathlib `isCyclic_of_subgroup_isDomain` で短い追加 |
| **BG Thm 2.5** (+ Prop 2.1/2.2/2.4, Gor 5.5.4-5) | L716 | ❌ 未 (真の frontier) | extraspecial+cyclic faithful irred の最終矛盾。**Gorenstein でなく BG 自前 §2 表現論**。Thm 3.4 完成の本丸。下記 §2 ↔ Peterfalvi 棚卸し参照 |
| §1 Prop1.3/1.4/1.5/1.6/1.7/1.8/1.13/1.16, Thm2.6 | — | ✅ (要再確認) | S01_Solvable / S01b_Prop116 / S02_Representations (使用時に各個検証) |
| special q-group def `IsSpecial` | — | ✅ def | GroupTheory/IsExtraspecial.lean:84 |

## BG §2 ↔ Peterfalvi `RepresentationTheory` 棚卸し (2026-06-07 検証, main `ae2eccc`)

Peterfalvi 用に構築された `OddOrder/GroupTheory/RepresentationTheory/*` 共有 module が BG §2 をどこまで
被覆するか、実測 (decls / LOC / 体)。**「sorry-free だが空 skeleton」の罠に注意**([[scaffold-sorry-free-not-done]])。

| BG §2 | RepresentationTheory module | 実体 | 体 | BG (一般体 F, char∤\|G\|) で使えるか |
|---|---|---|---|---|
| **Prop 2.1** (Schur/abs irred) | `AbsolutelyIrreducible.lean` | **空 skeleton** (0 decls, issue #) | — | ❌ 未。S02 に signature 案のみ |
| **Prop 2.2** (Clifford) | `Clifford.lean` | ✅ 実体 (65 decls, 1172 LOC, sorry-free) | **ℂ 限定** (`Representation ℂ G V`) | △ ℂ専用 ⇒ BG 一般体は **base-change か一般体版**要 |
| **Prop 2.4** (eigenspace under cyclic) | `EigenspaceUnderCyclicAction.lean` | ✅ 実体 (48 decls, 918 LOC, sorry-free) | **一般体** (`[Field F]`) | ◯ 直接再利用可 |
| **Thm 2.5** (extraspecial faithful) / Gor 5.5.4-5 | `ExtraspecialFaithful.lean` | **空 skeleton** (0 decls, issue #34) | — | ❌ 未。Thm 3.4 本丸 |
| **Thm 2.6** (奇数 2-dim) | `PGroupFixedVector.lean` + S02 | ✅ sorry-free (`odd_two_dim_abelian` 他) | 一般体 | ◯ 完了 |
| **Gor 3.2.2** (Z cyclic) | `SchurCenterBound.lean` | ✅ 実体 (= Isaacs CTFG Cor 2.30) | **ℂ 限定** | △ 一般体 capstone 短い追加要 |

**結論**: Peterfalvi 進捗は **大量の再利用可能な ℂ 表現論 + 一部一般体 module** を提供するが、BG §2 を**完全代替はしない**。
(1) Thm 2.5 / Prop 2.1 は空 skeleton で未着手、(2) Clifford/Schur は **ℂ 限定**で BG の一般体 F 設定に直接は乗らない
(BG Thm 2.5 証明自身が代数閉体へ base-change するので、その橋 or ℂ-module の代数閉体一般化が要)。
Prop 2.4 (eigenspace) のみ一般体で即再利用可。**Thm 3.4 着手時の設計判断 = §2 を「ℂ/代数閉体で組んで base-change」か「一般体で再構築」か**。

## base-change レイヤ確立 + Thm 3.4 の真の bottleneck (2026-06-07, main)

**✅ base-change インフラ完了** (`OddOrder/GroupTheory/RepresentationTheory/BaseChange.lean`, 共有レイヤ, sorry-free):
- `baseChangeRepresentation` (+ `_apply_tmul`, `_faithful`) — S02 から移設 (scalar 拡張 `F→K`)
- `invariants_baseChangeRepresentation_eq_bot` — **BG (2.9)** `C_V(R)=0 ⇒ C_{K⊗V}(R)=0` (flat + `piRight`)
- `baseChangeRepresentation_comp` — restriction 互換 (部分群 `H=Z(P)` へ (2.9) 適用)
- **BG (2.8) (dim 不変) は意図的に省略**: Thm 2.5 の "C_V(H)≠0" 方向専用で、Thm 3.4 は "C_V(H)=0 ⇒ h=pⁿ+1" 方向 (= (2.9) 経由) しか使わない。demand-driven。

**Thm 3.4 の残り = Thm 2.5 本体 = 代数閉体上の extraspecial 表現論** (repo・mathlib に**無い**が **mathlib の Wedderburn–Artin (`RingTheory/SimpleModule/IsAlgClosed.lean`) + Schur で構築可能**, from-scratch ではない)。bottom-up:
1. **Prop 2.1** (faithful absolutely irreducible ⇒ `E(P)=Hom_F(V,V)`; Burnside) — Wedderburn-Artin/alg-closed から。`AbsolutelyIrreducible.lean` は空 skeleton。
2. **Gor 5.5.4-5** (extraspecial faithful irreducible: 中心指標で決まり dim=pⁿ; 二乗和 `p^{2n}·1+(p-1)(pⁿ)²=|P|` から) — `ExtraspecialFaithful.lean` 空 skeleton (issue #34)。
3. **Prop 2.2(a)** (Clifford `V_P=M`) — `Clifford.lean` は ℂ 限定ゆえ代数閉体版 or base-change。
4. **Prop 2.4(j)(k)** (eigenspace counting) — ✅ `EigenspaceUnderCyclicAction` (一般体)。
5. **Thm 2.5 assembly** → Thm 3.4 special case (K extraspecial) → 矛盾 (h=qⁿ+1 even vs odd)。
これは複数セッションの表現論サブプロジェクト。char-p (有限体) のため ℂ-Clifford は不可、代数閉体 F̄ 版が要る。

## 推奨着手順序 (bottom-up)

1. **Lem 1.21** (新ファイル `OddOrder/BG/Ch1_Preliminary/PLength.lean` 拡張 or `S01d_Lemma121.lean`)。
   自己完結 (oPiPrimePiCore/oPiCore 商対応 API は S06 に precedent: 第3同型 + `oPiCore_compl_le_oPiPrimePiCore` +
   `oPiPrimePiCore_eq_oPiCore_of_compl_bot`)。**(a)=10.6 でも再利用**。順序 (a)(b)(c) → (d) → (e)。
2. **Thm 3.4** (S03 新ファイル)。表現論。Lem 3.3 (✅) を使う。
3. **Thm 3.5** (S03 新ファイル)。Clifford/Maschke/Wedderburn が要 (mathlib `Representation`/`Module` + 既存 S02)。最重量。
4. **Gorenstein 5.3.7** (special q-群)。`references/gorenstein/finite-groups.{pdf,mmd}` 参照。
5. **Thm 3.6 本体** (S03 新ファイル `S03d_Thm36.lean`)。Phase A–F を組む。

## メモ
- Thm 3.6 は 10.6 の r_p≥3 ケースのエンジン。10.6 はさらに Lem 10.4(b) (lane A1) も要 ([[s10_spine_blockers]])。
- Lem 1.21(a) を landing すれば 10.6 の reduction (H≤M⇒) が解け、10.6 は「easy case 完成 + hard case=Thm3.6+10.4b」に縮む。
- このセッションの成果: 10.14(d) landing (f21eb12) + スパイン/§3 ブロッカー精査。

## Lemma 1.21 着手状況 (2026-06-07)

ファイル `OddOrder/BG/Ch1_Preliminary/PLengthTransfer.lean` (新規)。**(b)(c) + 全 infra 完了 (sorry-free)**。

**✅ Landed (sorry-free):**
- `card_quotient_oPiPrimePiCore_eq` / `hasPLengthOne_iff_card_quotient` (`4a9bf08`): 第3同型 bridge
  `|G/O_{p',p}(G)| = |(G/O_{p'}(G))/O_p(…)|`。(a)–(e) 共通の出発点。
- `oPiCore_quotient_eq_of_isPiGroup` (`db0a10d`): **汎用 engine** — `H ⊴ G` が π-群 ⇒
  `O_π(G/H) = O_π(G).map mk'` (`|N|=|H|·|Kbar|` + `primeFactors_mul` + `IsPiGroup.le_oPiCore`)。(b)=π{p}ᶜ, (c)=π{p}。
- **(b)** `hasPLengthOne_of_isPiPrime_normal_quotient` (`1179617`): normal `p'` 商。
- `oPiPrimePiCore_eq_oPiCore_of_compl_bot` (`6a7a705`, S06 private を §1 layering 維持で再証明)。
- **(c)** `hasPLengthOne_of_isPGroup_normal_quotient` (`6a7a705`): normal `p` 商 + `O_{p'}(G/H)=1`。

**(a) 用 building block 4つ landed (sorry-free, overnight loop 2026-06-07):**
- `le_oPiPrimePiCore_of_quotient_isPGroup` (`2ffd94a`): `K⊴G`, `K.map(mk' O_{p'}(G))` p-群 ⇒ `K ≤ O_{p',p}(G)`。
- `isPGroup_map_oPiPrimePiCore` (`aa64421`): `O_{p',p}(G).map(mk' O_{p'}(G))` は p-群 (=`O_p(G/O_{p'}(G))`)。
- `oPiCore_compl_subgroupOf_le` (`885f8ca`): `(O_{p'}(G)).subgroupOf H ≤ O_{p'}(↥H)`。
- `isPGroup_inf_map_oPiPrimePiCore` (`3b841e9`): `(O_{p',p}(G)⊓H).map(mk' O_{p'}(G))` は p-群。

**✅ (a) DONE** `hasPLengthOne_subgroup` (`2271b55`, crux `oPiPrimePiCore_subgroupOf_le` = `5aeb6f0`):
`hasPLengthOne p G ⇒ hasPLengthOne p ↥H`。crux は `A=O_{p',p}G⊓H` からの 2 hom `gA`(→G/O_{p'}G, range=p群)
/`fA`(→↥H/O_{p'}↥H, range=K.map mk') で `ker gA ≤ ker fA` (`oPiCore_compl_subgroupOf_le`) ⇒ `quotientKerEquivRange`
+`index_dvd_of_le` で `|range fA| ∣ |range gA|`=p冪 ⇒ IsPGroup ⇒ `le_oPiPrimePiCore_of_quotient_isPGroup`。
最終 index 鎖は `index_dvd_of_le` + `relIndex_dvd_index_of_normal` (O_{p',p}G normal)。**(a) は Thm 10.6 の H≤M reduction を解く**。

**✅ Lemma 1.21 完了: (a)(b)(c)(e) すべて sorry-free + axiom-clean。(d) は bypass (不要)。**
PLengthTransfer.lean を `OddOrder.lean` root に配線済 (full build 3587 + AxiomsCheck allowlist OK)。

(e) は product 埋め込み経由で landing (2026-06-07, この章の最終チャンク):
- ✅ `oPiCore_prod` (`ee73dac`): `O_π(A×B) = O_π A ×' O_π B`。product 段の土台。
- ✅ **(e)-1 iso 不変** `hasPLengthOne_of_mulEquiv (e : G ≃* G')`: bridge の double quotient を
  `QuotientGroup.congr` + `oPiCore.map_eq_of_mulEquiv` で O_{p'}/O_p の 2 段 transport ⇒ `Nat.card` 不変。
- ✅ **(e)-2 product 商 iso** `quotientProd_mulEquiv : (A×B)/(H ×' K) ≃* (A/H)×(B/K)`:
  `quotientKerEquivOfSurjective (prodMap (mk' H)(mk' K))` (`ker_prodMap`+`ker_mk'`) + `quotientMulEquivOfEq`。
- ✅ **(e)-3 `hasPLengthOne_prod`** A,B plen1 ⇒ A×B plen1: double quotient を (e)-1/(e)-2/`oPiCore_prod` で
  `DQ(A×B) ≃* DQ(A)×DQ(B)` に分解 ⇒ `Nat.card_prod` + `Nat.Prime.dvd_mul`。
- ✅ **(e) 本体** `hasPLengthOne_of_inf_eq_bot`: `(mk' H).prod (mk' N) : G →* (G/H)×(G/N)`,
  `ker = H⊓N = ⊥` (`ker_prod`) ⇒ injective ⇒ `MonoidHom.ofInjective` で `G ≃* range`;
  `hasPLengthOne_prod` + `hasPLengthOne_subgroup` (=1.21a) + (e)-1 iso 不変。
- **(d)** `hasPLengthOne ⟺ ⟨p-elements⟩=O^{p'}` は (e) 近道で回避 (不要)。Thm 3.6 (3.11) は (e) を cite。

**Thm 3.6 残ブロッカー (1.21 完成済, ここから本丸)**: **Thm 3.4** (L863) + **Thm 3.5** (L903)
= 表現論 (Clifford/Maschke/Wedderburn, 最重量) + **Gorenstein 5.3.7** (special q-群)。

**進捗ログ**: overnight loop (`4a9bf08`..`3b841e9`, 7 commits: foundation+(b)+(c)+(a) building block 4つ)、
朝 attended (`5aeb6f0` crux + `2271b55` (a) 完成)、(e) landing (このセッション: (e)-1〜本体 4 補題 +
root 配線)。**Lemma 1.21 全完。次 = Thm 3.4 着手** (S03 表現論新ファイル, Lem 3.3 ✅ を使う)。

## ✅ 2026-06-09 session 4 cont. (a-keystone): Thm 3.4/3.5 完成後の Thm 3.6 着手準備 — 依存監査 COMPLETE

**Thm 3.4 (`S03d.thm34`) + Thm 3.5 (`S03e.thm35`) とも任意体で完全形式化済** (sorry-free+axiom-clean,
AxiomsCheck 登録)。⟹ Thm 3.6 の 2 大表現論ブロッカーは解消。残りの依存を全て **repo 内で実在確認**:

| 依存 | 実体 (検証済 exact name) |
|---|---|
| Lem 1.21(b) | `PLengthTransfer.hasPLengthOne_of_isPiPrime_normal_quotient` |
| Lem 1.21(c) | `PLengthTransfer.hasPLengthOne_of_isPGroup_normal_quotient` |
| Lem 1.21(e) | `PLengthTransfer.hasPLengthOne_of_inf_eq_bot` |
| Lem 1.21(a) | `PLengthTransfer.hasPLengthOne_subgroup` |
| Thm 3.4 | `S03d.thm34` (一般体), `S03d.thm34_algClosed` |
| Thm 3.5 | `S03e.thm35` (一般体), `S03e.thm35_algClosed` |
| Lem 3.3 | `S03b.kernel_acts_trivially_of_centralizer_eq_bot` 他 |
| Prop 1.3 | `S01_Solvable:181` (Fitting self-centralizing) |
| Prop 1.5(a)(b)(c)(e) | `S01_Solvable:655/1401/688/1480` |
| Prop 1.6(b) | `OperatorQuotientAction:101` (semidirect-product 形, `[[H,R],R]=[H,R]`) |
| Prop 1.6(c)(d) | `S01_Solvable:1521/1540` |
| Lem 1.7 | `S01_Solvable:1575+` / `FrattiniPGroup` |
| Prop 1.16 | `S01b_Prop116` |
| Thm 1.8 | `S01_Solvable:1702` (Burnside operator on p-group) |
| Thm 1.13 | `CriticalSubgroup` (`S6`/`S8` 等) |
| Thm 2.6(a) | `S04_PGroupsSmallRank:86/96` |
| Gor 5.3.7 | `S04e.exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction_with_minimality` |
| IsZGroup | `OddOrder.GroupTheory.IsZGroup` (ZGroup.lean:26; ⚠ mathlib `_root_.IsZGroup` と曖昧→明示修飾) |

**✅ statement 型検証済** (`S03f_Thm36.lean`, **local untracked scaffold**, proof = sorry, leaf build 3016 green,
long-line 0)。exact form:
```lean
theorem thm36 {G} [Group G] [Finite G] [IsSolvable G] (hodd : Odd (Nat.card G))
    {H R : Subgroup G} [H.Normal] (hcompl : Subgroup.IsComplement' H R)
    (hHall : Nat.Coprime (Nat.card ↥H) (Nat.card ↥R))
    {R₀ : Subgroup G} (hR₀R : R₀ ≤ R) (hR₀p : ∃ r : ℕ, r.Prime ∧ Nat.card ↥R₀ = r)
    (hZ : OddOrder.GroupTheory.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)))
    {p : ℕ} (hp : p.Prime) : hasPLengthOne p ↥(⁅H, R⁆ : Subgroup G)
```
docstring に Phase A–F の equation-by-equation roadmap 込み。**bare-sorry は commit しない方針** (merge-monitor
の sorry-不増 auto-merge を阻害しないため; thm34 も untracked scaffold だった先例)。

**▶ 次セッション (Thm 3.6 本体, multi-session)**: minimal-counterexample induction backbone
(`thm36_aux` を thm34_aux/thm35_aux 型で strong induction on `|G|`) を組み、Phase A (3.6–3.11) から着地。
- (3.6) は Prop 1.6(b) の semidirect-product 形を `⁅H,R⁆ < H` ケースの `⁅⁅H,R⁆,R⁆=⁅H,R⁆` に適応する要あり。
- Phase A の reusable standalone helper 候補: `F(H)=O_p(H) when O_{p'}(H)=1` (Fitting=∏O_q 分解)。
- 最重量は Phase D–F (Gor 5.3.7 適用 + special q-group 構造 + orbit-length parity 矛盾)。

## ✅ 2026-06-09 session 5 (a-keystone): インフラ 3 commit + Phase A (3.6) 着地

このセッションは **standalone infra を 3 commit + scaffold で thm36_aux backbone + (3.6) を完全証明**
(後者は untracked scaffold ゆえ未 commit、precedent 通り)。

### committed infra (3 commit, full build 3618 green, all axiom-clean)
1. **Z-群インフラ** (`af71f3a6`, `OddOrder/GroupTheory/ZGroup.lean`):
   - `isZGroup_iff_mathlib`: repo `OddOrder.GroupTheory.IsZGroup` ↔ mathlib `_root_.IsZGroup`
     (フィールド同一)。これで mathlib の Z-群 API (`of_injective`/`of_surjective` 部分群/商閉包、
     `exponent_eq_card`、`IsPGroup.isCyclic_of_isZGroup`) が使える。
   - `card_eq_prime_of_isZGroup_exponent_dvd`: 非自明 Z-群で全元 `g^p=1` ⟹ `|G|=p`。
   - `card_eq_prime_of_le_isZGroup`: `A ≤ Z` (Z-群)・非自明・exponent|p ⟹ `|A|=p`。
     **⟹ (3.19) `|C_V(R₀)|=p`、(3.31) `|C_K(R)|=q` で直接使う**。
2. **actionCommutator↔subgroup 基盤橋** (`c307c0fa`, `OperatorQuotientAction.lean`):
   `actionCommutator_conjNormal_map_subtype_eq : (actionCommutator (conjNormal∘R.subtype)).map H.subtype = ⁅H,R⁆`
   (`H ⊴ G`)。内部共役作用の actionCommutator 言語 ↔ 部分群交換子 `⁅H,R⁆` の翻訳土台。
3. **Prop 1.6(b) subgroup 形** (`fabbeed1`, `OperatorQuotientAction.lean`):
   `commutator_commutator_right_eq : ⁅⁅H,R⁆,R⁆=⁅H,R⁆` (`H ⊴ G`, coprime, `G` solvable)。
   `actionCommutator_restrict_self_map_subtype_eq` (= `[[N,A],A]=[N,A]`、`⁅H,R⁆⊴G` 不要) を
   2 段 nest して bridge #2 経由で導く。**核 = nested generator 橋** (`toMulAutHom_apply_val` で
   制限作用が φ と一致、`↑↑(nN·(ψr)nN⁻¹)=⁅↑↑nN,↑r⁆`)。⟹ (3.6)/(3.24)/(3.32) で使う。

### scaffold (`S03f_Thm36.lean`, **untracked**, leaf build 3016 green, 唯一 real sorry = (3.7)-(3.38))
- `thm36_aux` (strong induction on `|G|`) + `by_contra hcounter` backbone を組んだ。
- **✅ (3.6) `⁅H,R⁆ = H` を完全証明** (sorry-free within (3.6)):
  - subgroup-IH を `S := ⁅H,R⁆ ⊔ R` (= `⁅H,R⁆R`) に適用 (thm34 の wiring_check パターン)。
  - `S ⊴`-normality: `subgroup_le_normalizer_commutator_self R H` (Isaacs Lem 4.1, 仮定なし) +
    `commutator_comm` で `R ≤ N(⁅H,R⁆)`、`Subgroup.le_normalizer` で `⁅H,R⁆ ≤ N(⁅H,R⁆)`。
  - **Z-群 hyp transport** (新パターン): `C_S(R₀').map S.subtype ≤ ⁅H,R⁆⊓C_G(R₀) ≤ H⊓C_G(R₀)`
    ⟹ `IsZGroup.of_injective` (`inclusion_injective hle`) + `equivMapOfInjective` で `IsZGroup ↥(C_S(R₀'))`。
  - 結論橋: IH → `hasPLengthOne p ↥⁅H'.subgroupOf S, R'.subgroupOf S⁆`、`map_commutator`+
    `subgroupOf_map_subtype` で `(...).map S.subtype = ⁅⁅H,R⁆,R⁆`、`equivMapOfInjective`+
    `hasPLengthOne_of_mulEquiv` で transfer、`commutator_commutator_right_eq` で `=⁅H,R⁆` ⟹ `hcounter` 矛盾。

### 次セッション (Phase A 続き (3.7)–(3.11) → Phase B–F)
- **(3.7) 商 IH** (`G/X`, `1≠X⊴H` R-invariant): thm36_aux の **新しい IH 適用形** (subgroup でなく商)。
  - `X ⊴ G` (char H ◁ G より)、`G/X` で `H/X` normal Hall、`R` 商で補群、`R₀` 商 prime。
  - **Z-群 transport (商側)**: Prop 1.5(d) `C_{H/X}(R₀)=C_H(R₀)X/X` (= image of Z-群) ⟹
    mathlib `of_surjective` で Z-群。**Prop 1.5(d) の clean 形** (`C_{G/N}(A)=C_G(A)N/N`) の repo 所在を
    要確認 (`S03_FrobeniusActions` に bridge 形あるが `hlift` 付き; Isaacs Cor 3.28 が underlying)。
  - (3.7) は (3.6) `H=⁅H,R⁆` を使い `⁅H/X,R⁆=H/X` ⟹ `H/X` plen1。
- **(3.8) `O_{p'}(H)=1`**: `O_{p'}(H)≠1` なら X:=O_{p'}(H) で (3.7) + Lem 1.21(b) ⟹ H plen1 ⟹ 矛盾。
- **(3.9) `V=F(H)=O_p(H)` elem abelian**: `F(H)=O_p(H)` (O_{p'}=1; **opCore↔oPiCore 橋 + fitting sup-split
  が要**, `fitting=⨆opCore p`/`oPiCore {p}ᶜ=O_{p'}`)、Φ(V)=1 reduction (Lem 1.21(c)+Thm1.8+Prop1.3)、Lem 1.7。
- **scaffold の既知 cleanup (commit 前に要)**: long-line 6 箇所 (117,123,153,155,188,191) を ≤100 に。
- 最重量は依然 Phase D–F (Gor 5.3.7 + special q-group + orbit-parity)。
