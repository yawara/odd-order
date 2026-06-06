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
| **Lem 1.21(a)** | L566 | ❌ 未 | `H≤G, plen1 G ⇒ plen1 H` (= p-length 部分群単調性, **10.6 でも必要**) |
| **Lem 1.21(b)** | L567 | ❌ 未 | `H ⊴ G normal p'-sub, plen1(G/H) ⇒ plen1 G`。(3.8) で使用 |
| **Lem 1.21(c)** | L568 | ❌ 未 | `H ⊴ G normal p-sub, O_{p'}(G/H)=1, plen1(G/H) ⇒ plen1 G`。(3.9) |
| **Lem 1.21(d)** | L569 | ❌ 未 | `plen1 G ⟺ ⟨p-elements⟩ が normal p-complement を持つ`。(e) の engine |
| **Lem 1.21(e)** | L570 | ❌ 未 | `H,N ⊴ G, H∩N=1, plen1(G/H), plen1(G/N) ⇒ plen1 G`。(3.11) |
| **Thm 3.4** | L863 | ❌ 未 | 可解奇 G, normal Hall K + prime-order 補群 R, V 上 (char∤\|G\|), `C_V(R)=0 ⇒ [R,K]⊆C_K(V)`。表現論 (Clifford/Maschke/special) |
| **Thm 3.5** | L903 | ❌ 未 | Frobenius G=KR (K 可解, R cyclic prime), V 上, `C_V(R) 1-dim ⇒ K'⊆C_K(V)`。Clifford/Maschke/Wedderburn/Prop2.2/Lem3.3 |
| **Lem 3.3** | L845 | ✅ | S03b_Lemma33 `kernel_acts_trivially_of_centralizer_eq_bot` 等 |
| **Lem 3.1** | — | ✅ | S03 `isFrobeniusGroup_iff_complement_centralizer_inf_kernel_eq_bot` |
| **Gorenstein 5.3.7** | — | ❌ 未 | special q-群の coprime 作用 (3.25)。CLAUDE.md 方針: Gorenstein 原文を読み Lean 化 |
| §1 Prop1.3/1.4/1.5/1.6/1.7/1.8/1.13/1.16, Thm2.6 | — | ✅ (要再確認) | S01_Solvable / S01b_Prop116 / S02_Representations (Explore 2026-06-07 報告、楽観気味なので使用時に各個検証) |
| special q-group def `IsSpecial` | — | ✅ def | GroupTheory/IsExtraspecial.lean:84 |

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

**(a) 完成の残 crux (設計確定・Lean grind のみ、~40 行 fiddly で wind-down):**
中間補題 `(oPiPrimePiCore {p} G).subgroupOf H ≤ oPiPrimePiCore {p} ↥H` を `le_oPiPrimePiCore_of_quotient_isPGroup` (↥H で) に帰着。要 `IsPGroup p ↥(K.map (mk' (oPiCore {p}ᶜ ↥H)))`, `K=(oPiPrimePiCore{p}G).subgroupOf H`。
- `A := oPiPrimePiCore{p}G ⊓ H` (≤ H), 2 つの hom from `↥A`:
  `gA := (mk' (oPiCore{p}ᶜ G)).comp A.subtype` (range `= A.map(mk' O_{p'}G) =` isPGroup_inf_map の p-群),
  `fA := (mk' (oPiCore{p}ᶜ ↥H)).comp (Subgroup.inclusion (A≤H))` (range `= (A.subgroupOf H).map(mk' O_{p'}↥H) = K.map f`)。
- `ker gA ≤ ker fA`: `a∈↥A, ↑a∈O_{p'}(G) ⇒ (a:↥H)∈(O_{p'}G).subgroupOf H ≤ O_{p'}(↥H)` (`oPiCore_compl_subgroupOf_le`)。
- card: `|range fA| = (ker fA).index`, `|range gA| = (ker gA).index` (`quotientKerEquivRange` + index 定義); `index_dvd_of_le (ker gA ≤ ker fA)` ⇒ `(ker fA).index ∣ (ker gA).index` ⇒ `|range fA| ∣ |range gA|` (=p冪) ⇒ `IsPGroup.of_card`+`Nat.dvd_prime_pow`。
  (別路: `IsPGroup.of_surjective` (PGroup.lean:74) で `↥A/ker gA ↠ ↥A/ker fA` (`QuotientGroup.map`) 経由。)
- 続く index 鎖: `Subgroup.index_dvd_of_le 中間補題` で `(oPiPrimePiCore{p}↥H).index ∣ ((oPiPrimePiCore{p}G).subgroupOf H).index ∣ (oPiPrimePiCore{p}G).index = |G/O_{p',p}G|` ⇒ p∤ ⇒ `hasPLengthOne p ↥H`。最終 `hasPLengthOne_of_le`。

**残 (d)(e) — さらに別チャンク:**
- **(d)** `hasPLengthOne ⟺ ⟨p-elements⟩=O^{p'}(G) が normal p-complement`。`⟨p-elements⟩` の新規形式化要
  (`pResidual` 等 mathlib/repo に無し)。`HasNormalPComplement` 部分群継承 (`Ch05:1985`) 既存 → (d) で (a)(e) も即。
- **(e)** `H,N⊴G, H∩N=1, G/H・G/N plen1 ⇒ G plen1`: (d) 経由。Thm 3.6 (3.11) cite。

**overnight loop 総括 (2026-06-07)**: foundation + (b) + (c) + (a) building block 4つ を sorry-free landing
(7 commits, `4a9bf08`..`3b841e9`)。(a) crux (~40行 fiddly, 設計上記) と (d)(e)/Thm 3.4/3.5/Gorenstein 5.3.7/Thm 3.6
は heavy なため、無人 grind を避け clean handoff で loop 終了。再開は上記 crux から (building block 全部揃い)。
