# BG Theorem 7.4 (transitivity_propagates) 実装プラン — living note

## ✅✅✅ COMPLETE (2026-06-04, commits 0cf0c48..cddd184 + AxiomsCheck bd38fdd)
`transitivity_propagates` **sorry-free・axiom-clean** ([propext,choice,Quot.sound], #print 確認),
AxiomsCheck 登録済, full build 3562 + AxiomsCheck 3522 green。statement は原形 (4-conjunct) 不変=laundering 無。
全 helper (7.3 `tp_exists_normalized` / (b) `tp_b` / (d) `tp_d` (Lem6.5a 経由) / base `tp_base` / R3 strong-induction)
完成。S07 が S06 を import (Lem6.5a)。**§7 残 = Prop 7.5 case1 (Thm 6.7 待ち) のみ** + S06 Lem6.5(c) (別件)。
以下は実装中の living plan (歴史的記録)。

> 2026-06-03。`S07_Transitivity.lean` の `transitivity_propagates` (mmd L2197-2250) を埋める。
> §7 残 2 sorry の一つ (もう一つは Prop 7.5 case1 = Thm 6.7 待ち)。
> **規模注意**: §7 最大級。`|P:A|` composition-series 帰納 + base case (b)(c)(d) で ~470 行見込み。

## ✅ 完成済インフラ (build-green, commits 3ef12c4 / a889362)

1. **`tp_centralizer_eq` = (a)** `C_G(P)⊓K = O_{π'}(C_G(P))` (axiom-clean)。
   `A≤P⟹C_G(P)⊆C_G(A)`; ⊆ は `le_opiCoreInG_of_normal_of_isPiSubgroup`
   (C_G(P)⊓K は C_G(P) の正規 π'); ⊇ は §7 Note `mem_kSubgroup_of_piPrime_mem_centralizer`。
2. **`primesOf_eq_of_le_of_isPiSubgroup`** : `A≤B≤P`, P が π(A)-群 ⟹ π(B)=π(A)。帰納で B を A の役に。
3. **`tp_hyp71_of_le`** : Hypothesis71 単調性 (A≤B, π(B)=π(A) ⟹ Hyp71 B; mmd L2212)。
4. **`exists_conj_eq_of_isHall_subgroupOf`** = **Hall-C-in-subgroup** (`↥V` 可解 + H₁,H₂ ↥V内π-Hall
   ⟹ ∃w∈V, wH₁w⁻¹=H₂)。**Thm7.4(b) と Lem6.5(c) の共通エンジン**。`Ch03.hall_C`@↥V を翻訳。

**(d) の §6 依存 = Lem 6.5(a) (`inf_commutator_eq_of_coprime`) は完成済** (commit f5160ee)。

### ✅ 追加完成 (commits f57a538 / 474a517)
5. **`exists_normal_index_prime_of_solvable`** (R1a) = nontrivial 有限可解 ⟹ ∃ N⊴, |G:N| prime
   (card最大 proper 正規 N → Q⧸N simple+solvable → abelian → `is_simple_iff_prime_card`)。
6. **`exists_normal_lt_top_of_isSubnormal`** (R1 step1) = A' subnormal, A'<⊤ ⟹ ∃ B⊴Q, A'≤B<⊤
   (`IsSubnormal` 帰納)。

### ✅✅ R1 完結 (commit c7bf8d9): `tp_reduction`
`A<P` subnormal, P 可解 ⟹ `∃ B, A≤B<P, B⊴P, |P:B| prime`。step1+R1a+pullback+G-translate 全組立済。
(「A subnormal in B」clause は外し、R3 で `inf_isSubnormal_subgroupOf`+equiv-transport で別途導出。)

### ✅ R2 base-case helpers (commit dfddd4e)
8. **`eq_of_inf_normalizer_le`**: Q≤Q₁ (q-群), Q₁⊓N_G(Q)≤Q ⟹ Q=Q₁ (mmd L2230-2232 finish)。
9. **`le_opiCoreInG_normalizer_self`**: π-部分群 Q ≤ O_π(N_G(Q))。

## 残タスク = R2 (base case 数学核心) + R3 (wiring)

### 🔑 (c) core の決定的パターン = `commonConstruction` (S07:358-457) を P で再利用
`commonConstruction` が Prop 1.5(b) を `↥N` (N=O_{π'}(H)) に relativize する手順を完全に示している:
`opiCoreInG`+`hG.solvable_of_lt_top`(↥N solvable)+`isAInvariant_conjAction_iff`+`IsAInvariant.restrict`
+`isAInvariant_subgroupOf_restrict`+`coprime_of_isPiGroup_of_isPiGroup_compl`+
`aInvariant_piSubgroup_le_aInvariant_hall`(Prop 1.5b)+`map N.subtype` 戻し。
**(c) はこれを A→P, H→N_G(Q), N→M:=O_{π'}(N_G(Q)) に置換**して `Q.subgroupOf M ≤ P-inv Hall{q} R`
を得る (Q≤M は helper 9, Q P-inv は P≤N(Q))。+ Hyp7.1 で `N_{Q₁}(Q)⊆O_{π'}(N(Q))`, 順序不等式
`|Q|=|R戻し|=|M|_q ≥ |N_{Q₁}(Q)| ≥ |Q|`, helper 8 で `Q=Q₁`。Q=⊥ は (7.3) 経由 (degenerate)。
### ✅✅ 追加完成 (commits dd26919 + N(A)-stability): 11→13 lemma
- **`isPGroup_of_isPiSubgroup_singleton`** ({q}-部分群は q-群)。
- **`tp_c_main`** = (c) 主要 case (非自明 Q∈ℋ*(P;q) ⟹ ∈ℋ*(A;q))。← **base case 数学核心、完成**。
- **`conj_smul_mem_hInvariant_of_normalizer`** + **`..._hInvariantStar_of_normalizer`** = ℋ(*)が N(A)-共役安定。

### (7.3) p-群不動点 [残, MulAction tail が要注意] — 構造は確定:
statement `tp_exists_normalized`: `(∀x∈P, conj x•A=A) (g∈P) (g^p∈A) (A⊔zpowers g=P) (¬p∣|ℋ*(A;q)|)
⟹ ∃Q∈ℋ*(A;q), P≤N(Q)`。証明:
1. `letI act : MulAction ↥P ↥S` (S:=ℋ*(A;q)): `x•Q := ⟨conj↑x•Q.1, conj_smul_mem_hInvariantStar_of_normalizer Q.2 (hPnA ↑x x.2)⟩`; one_smul/mul_smul は Subtype.ext + `Subgroup.coe_mul`/`map_mul`/`mul_smul`。
2. `σ := MulAction.toPermHom ↥P ↥S ⟨g,hgP⟩`; `σ^p=1` via `← map_pow` + `(⟨g,hgP⟩^p:↥P)=g^p` (push_cast) + `g^p∈A≤N(Q)` で各 Q 不変。
3. `IsPGroup p (zpowers σ)`: `Nat.dvd_prime`+`orderOf_dvd_of_pow_eq_one hσp`+`Nat.card_zpowers`+`IsPGroup.of_card`。
4. `card_modEq_card_fixedPoints` + `¬p∣|ℋ*|` ⟹ `0<card(fixedPoints (zpowers σ) ↥S)` (`Nat.modEq_zero_iff_dvd`)。
5. **⚠️ tail (要 careful)**: fixedPoint x から `σ x = x` (`mem_fixedPoints` + ⟨σ,mem_zpowers⟩) →
   subgroup/Perm/toPermHom smul を **explicit lemma で** unfold (rfl 不可の恐れ) → `conj g•x.1.1=x.1.1` →
   `g∈N(x.1.1)` + `A≤N` で `P=A⊔zpowers g≤N`。`p∤|ℋ*|` は assembly で htrans (|ℋ*|∣|K| π', p∈π) から。
### (b): (c)+htrans で Q₂=Q₁^k, P,P^k は N_{KP}(Q₂)=(K∩N(Q₂))P の Hall{π}, `exists_conj_eq_of_isHall_subgroupOf` で共役, kg∈C_K(P)。
### (d): L=N(P)∩N(Q), N(P)=L·C_K(P) (a)(b), `inf_commutator_eq_of_coprime` (Lem6.5a) で P∩N(P)'⊆N(Q)'。
### R3 wiring: strong induction on |P:A|, tp_reduction で B, A=B⟹base, A<B⟹二重再帰+(c)合成。「A subn in B」= inf_isSubnormal_subgroupOf+equiv-transport。
`A < P` subnormal (P 可解=`hG.solvable_of_lt_top`) ⟹ `∃ B, A≤B, (B.subgroupOf P).Normal, B<P,
(P:B index) prime, (A.subgroupOf B).IsSubnormal`。
- **step1**: subnormal 系列の second-from-top を取る。mathlib `Subgroup.isSubnormal_iff`
  (`GroupTheory/IsSubnormal.lean:177`, chain 表現) で系列を出し `H_{m-1} ⊴ H_m=⊤`。
  (↥P 内で A.subgroupOf P subnormal ⟹ ∃ B' ⊴ ↥P, A.subgroupOf P ≤ B' < ⊤)。
- **step2**: prime index 化。`P/B'` nontrivial 可解 ⟹ **`exists_normal_index_prime_of_solvable`**
  (要新規, R1a)。pull back で B。`inf_isSubnormal_subgroupOf` (Ch02:131) で A subnormal in B。

### R1a. `exists_normal_index_prime_of_solvable` (nontrivial 有限可解 ⟹ ∃ N⊴, |G:N| prime) (~40-60行)
G' = commutator G < ⊤ (可解 nontrivial)。G/G' nontrivial 有限 abelian ⟹ ∃ 極大部分群 M̄
(`IsCoatomic.exists_coatom`, `Order/Atoms.lean:346`)。M̄ ⊴ (abelian)、G/G'/M̄ simple
(coatom⟹simple quotient, **要橋**) + abelian ⟹ `Group.is_simple_iff_prime_card`
(`Cyclic.lean:252`) で |index| prime。pull back (G→G/G'→(G/G')/M̄)。
- ⚠️ gap = 「coatom M̄ ⟹ G/G'⧸M̄ simple」(normal-lattice correspondence)。または abelian で
  「∃ 部分群 index prime」を直接 (Z/p 商)。

### R2. base case `tp_base` : A ⊴ P, |P:A| prime or A=P ⟹ (b)(c)(d) (~250行, 数学的核心, mmd L2218-2250)
- **(7.3) 不動点** (~60行): P が ℋ*(A;q) の元を normalize。A は各元を normalize (A-不変) ⟹ 作用は
  P/A 経由。K 推移 ⟹ |Ω| ∣ |K| (π')。P/A は位数 1/prime の p-群、p∤|Ω| ⟹ 不動点 (mathlib
  `IsPGroup`/`MulAction.card_modEq_card_fixedPoints` 系)。
- **(c)** (~80行, mmd L2224-2232): Q∈ℋ*(P;q) ⟹ A normalize Q ⟹ Q⊆Q₁∈ℋ*(A;q)。
  `N_{Q₁}(Q)⊆O_{π'}(N_G(Q))` (Hyp7.1)。**Prop 1.5** (`aInvariant_hall_conj` S01:606) で Q⊆ P-不変
  Sylow q Q₂ of O_{π'}(N_G(Q)); Q∈ℋ*(P;q)⟹Q=Q₂ ⟹ |Q|≥|N_{Q₁}(Q)|≥|Q| ⟹ Q=Q₁∈ℋ*(A;q)。
- **(b)** (~80行, mmd L2234-2244): Q₁,Q₂∈ℋ*(P;q); (c)+K推移 ⟹ Q₂=Q₁^k。P,P^k ≤ N_{KP}(Q₂);
  `N_{KP}(Q₂)=(K∩N_G(Q₂))P` ⟹ P,P^k は N_{KP}(Q₂) の π-Hall (**order 計算**, Lem6.5(c)と同型) ⟹
  **`exists_conj_eq_of_isHall_subgroupOf`** で共役 g∈K∩N_G(Q₂); kg∈N_K(P)=C_K(P)。
- **(d)** (~40行, mmd L2246-2248): L=N_G(P)∩N_G(Q)。(a)(b)で N_G(P)=L·C_K(P)。**Lem 6.5(a)**
  (`inf_commutator_eq_of_coprime`, G:=N_G(P),K:=C_K(P),U:=L,H:=P) で P∩N_G(P)'=P∩L'⊆L'⊆N_G(Q)'。

### R3. 帰納配線 `tp_aux` (~120行)
`Nat.strong_induction_on` on `n=(A.subgroupOf P).index`。A も量化 (B を A の役に)。
- A=P: 自明 base ((b)=htrans, (c)=refl, (a)=tp_centralizer_eq, (d)=Lem6.5(a)@P=A)。
- A<P: R1 で B。A=B ⟹ R2 (A⊴P prime)。A<B ⟹ ih(A,B) [|B:A|<n] + ih(B,A 役,P) [|P:B|<n] 合成
  ((c) は ℋ*(P)⊆ℋ*(B)⊆ℋ*(A) 連鎖; primesOf B=primesOf A で rewrite; (b)(d) は A/B非依存; (a)=tp_centralizer_eq)。
  ih(B,P) には Hyp71 B (`tp_hyp71_of_le`) + htrans B (= ih(A,B) の (b)) を供給。

## 確認済 mathlib/repo lemma
- `Subgroup.isSubnormal_iff` (chain), `Subgroup.IsSubnormal.step`, `inf_isSubnormal_subgroupOf` (Ch02:131)
- `aInvariant_hall_conj` (Prop 1.5, S01:606), `IsPGroup.exists_normal_index_eq_prime` (Ch01:420, p群版)
- `Group.is_simple_iff_prime_card` (abelian), `IsSimpleGroup.comm_iff_isSolvable`, `IsCoatomic.exists_coatom`
- `exists_conj_eq_of_isHall_subgroupOf` (本ファイル), `inf_commutator_eq_of_coprime` (S06, Lem6.5(a))

## 判定
完了 = `transitivity_propagates` sorry-free + axiom-clean + AxiomsCheck 登録。
現状 = インフラ 4 本完成、base case + 還元 + 配線 が残 (multi-session)。
