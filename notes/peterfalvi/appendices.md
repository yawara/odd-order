# Peterfalvi Appendices A–E — Lane H 計画 + AUDIT

> Lane H = worktree `pf-s10` / branch `pf-s10` / issue base **2000** / model Opus 4.8 (1M)。
> §10–13 が BG §14/§15 (Lane F/G) に gate されて STANDBY の間、LAUNCH.md の指示で
> BG spine とも character API とも独立な **Peterfalvi Appendices** を形式化する。

## 0. AUDIT 結論 (session 1, 2026-06-14)

5 ファイル (`OddOrder/Peterfalvi/Appendices/{Huppert,NearFields,Suzuki2Groups,FeitSibley,Suzuki}.lean`)
は **すべて opaque-`Prop` scaffold** (`foo : Prop` + `foo_holds : foo`、結論は `∃ data, data.foo ∧ …`
で rider が vacuous)。LAUNCH の「難度低め・今すぐ実証明できる」は**楽観**で、実体は全 appendix が
**研究級の古典定理**に bottom-out する:

- **B (Huppert)**: 可解 2-重可移群の Huppert 分類の特殊版。Lemma は **Huppert V.8.15 (FPF p-群 ⟹ cyclic)**
  + Huppert III.7.5 + Schur (F_q 上) に依存。
- **C (NearFields)**: 有限 near-field の Zassenhaus 分類。
- **D (Suzuki2Groups)**: Higman の Suzuki 2-群分類。
- **E (FeitSibley)**: Feit–Sibley coherence (S07 coherence API 依存 = Lane B 領域)。
- **A (Suzuki)**: 最難 (PSU₃(q) 特徴付け)。後回し。

これらは **FT 最短経路外** (Peterfalvi Part II = Suzuki 特徴付け; FT 定理本体は Part I + BG §7-16)。
⟹ off-critical-path の self-contained 群論。空 scaffold 量産はしない ([[scaffold-sorry-free-not-done]])。
**正攻法 = opaque を faithful 型に置換し、citeable な上流があるものは完全証明、無いものは gap を
精密に局所化** (scaffold_opaque_prop_convention.md の cleanup path)。

## 1. ⭐ 唯一の citeable shortcut: BG Prop 3.9 (Appendix B 用)

`OddOrder.BG.Ch3.S12.isCyclic_of_coprime_fpf_pgroup_action`
([S12_Theorem1212.lean:55](../../OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem1212.lean)) =
**Huppert V.8.15 = Gorenstein 5.3.14**: 有限 p-群 R (p odd) が非自明 H に coprime かつ FPF 作用 ⟹
`IsCyclic R`。**proved・axiom-clean** (AxiomsCheck:4115)。Appendix B Lemma の核 (FPF⟹cyclic) を cite 可。
他の appendix には同等の citeable 上流が repo に**無い**。

## 2. Appendix B de-opaque 進捗 (session 1)

`Huppert.lean` を opaque scaffold → **faithful 型**に全面書換 (build-green, sorry 2→2 不変)。

**完全証明 (0 sorry, axiom-clean = propext/choice/Quot のみ; #print axioms で確認):**
- `smul_eq_of_sq_smul_eq_of_odd_orderOf` — part (1) の「奇位数元は 2 点を入れ替えられない」
  (`g²•a=a ∧ Odd(orderOf g) ⟹ g•a=a`; `exists_pow_eq_self_of_coprime` で `⟨g⟩=⟨g²⟩`)。
- `isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian` — **Lemma の cyclic 結論**。
  ⚠ thin wrapper ではない: **coprimality `q ≠ p` を FPF から導出** (q=p なら p-群 P が非自明
  p-群 E に作用 ⟹ `card_modEq_card_fixedPoints` で非零共通不動点 ⟹ FPF と矛盾) してから Prop 3.9 を cite。

**faithful statement + 局所化 sorry (×2):**
- `pGroup_cyclic_fixedPointFree` (Lemma) — sorry = **part (1)-(2) reduction** (定 point-stabilizer
  位数 ⟹ FPF; Clifford 分解 `E=⊕Eᵢ` + 既約ケース via Schur)。cyclic は keystone を cite 済。
- `fitting_cyclic_fixedPointFree` (Prop 1) — sorry = F(D) 構造 (F(D) cyclic ∧ FPF ∧ `commutator D ≤ F(D)`)。

`pointStabilizer φ a := (stabilizer (MulAut E) a).comap φ` (faithful な `P_a`)。

### session 2 (2026-06-14): p.136 復元 + Prop 1 bridge

**✅ mmd p.136 MISSING_PAGE 復元** (PDF 画像読み, [[nougat-missing-page-recovery]]):
- **Lemma part (2) 末尾**: P 既約・非 cyclic 仮定 → R⊴P type-(p,p), Schur で End(E)=有限体 → Z(P) cyclic →
  |R∩Z(P)|=p, P は R の他の位数 p 部分群 {T_i} を置換, `C_E(R∩Z(P))=0`, `E_i:=C_E(T_i)`,
  `E=⊕E_i` (直和は帰納法; t∈T_k は E_i=C_E(T_i) を中心化 → R=⟨T_k,T_i⟩ 中心化 → x_i=0) を P が置換
  → part (1) で P cyclic, 矛盾。
- **Prop 1 証明**: 各奇素数 p で `P=O_p(F)⊴D`, D transitive on E^# → `P_a,P_b` は D-共役 (∵ d·a=b, P正規) →
  定 stabilizer → Lemma で O_p(F) cyclic+FPF。`F=∏_p O_p(F)` → F cyclic+FPF。`C_D(F)=F`
  (Feit-Thompson+Fitting [H]III.4.2, D 可解) → `D/F ↪ Aut(F)` cyclic ゆえ abelian。

**✅ bridge lemma landed** (complete, axiom-clean): `card_pointStabilizer_comp_eq_of_normal_of_transitive`
= Prop 1 の「P_a,P_b 共役」step (N⊴D + transitive ⟹ N-stabilizer 位数一定; 共役 `N_b=dN_ad⁻¹` を
conjugation Equiv で). sorry 不変 (2→2)。

### 残 TODO (Appendix B)
- [x] **part (1) key step** ✅ `fixes_components_of_permutes_indep` (complete, axiom-clean, session 4):
      φ x が独立族 `S:ι→Subgroup E` (`iSupIndep`) を置換 + a∈S i, b∈S j (i≠j, ≠1) + x 奇位数 +
      φx(a·b)=a·b ⟹ φx a=a ∧ φx b=b。論文の「ax=a,bx=b or ax=b,bx=a (奇位数で後者不可)」二分法を
      `iSupIndep`(component pin) + swap補題で完全形式化。**DirectSum/projection 不要** — `iSupIndep`
      の disjoint だけ (E_σi ⊓ (E_i⊔E_j⊔E_σj)=⊥ via `(hind k).mono_right` + `disjoint_def`; pair
      kill は s·t=1∧disjoint⟹両 triv)。⚠ 技法: `letI:CommGroup E:={Group with mul_comm:=hcomm}` +
      AC 並べ替え `simp only [mul_assoc,mul_comm,mul_left_comm]` (group は comm 非対応)。scratch 開発→統合。
- [x] **part (1) stabilizer 組立** ✅ (session 5, 3 lemmas complete/axiom-clean):
      `pointStabilizer_mul_eq_inf_of_components` (P_{a·b}=P_a⊓P_b ⟸ key step + map_mul) /
      `mul_ne_one_of_components` (a·b≠1 ⟸ disjoint) / `pointStabilizer_eq_of_components_of_constant`
      (定 stab ⟹ P_a=P_b; `Subgroup.eq_of_le_of_card_ge` で P_a⊓P_b=P_a 両向き)。
- [x] **part (1) 完成** ✅ `fpf_of_constant_stabilizer_of_permuted_decomp` (complete, axiom-clean,
      session 6): `iSupIndep S` + `⨆S=⊤` + ≥2 nontrivial summands + faithful + 奇位数 + 定 stabilizer
      ⟹ FPF (`∀x≠1, actionFixedBy φ x=⊥`)。a₀∈S_{i₀}^# で P_{a₀}=⊥ (x∈P_{a₀} は P_a=P_b 経由で全 S_k
      pointwise 固定 ⟹ actionFixedBy=⊤ ⟹ φx=1 ⟹ x=1) → 定 stab で全 a 伝播。⚠ subst 方向: `eq_or_ne k i₀`
      は `rfl` だと i₀ 消える → `hki` 保持 + `hki ▸ hsk`。**Appendix B Lemma part (1) は完投**。
- [ ] **imprimitive 分解 `E=⊕Eᵢ` 存在 (Maschke/Clifford)**: 既約でない coprime 加群 → P-置換される
      isotypic/imprimitive 分解。これと part (1) で Lemma の reducible ケース。**残 setup の本丸**。
- [x] **part (2) cyclic case** ✅ `fpf_of_abelian_of_irreducible` (complete, axiom-clean [propext/Quot
      のみ!], session 7): abelian + faithful + irreducible ⟹ FPF。x≠1 で C_E(x)=actionFixedBy φ x は
      P-invariant (可換) かつ ≠E (faithful) ⟹ ⊥ (irreducible)。群論のみ・Schur 不要。一発 build 通過。
      ⚠ MulAut mul app は `rw [map_mul]; rfl` で comp 展開。
- [ ] **part (2) 非 cyclic case (hard rep-theory)**: P 既約・非 cyclic → R⊴P type-(p,p)
      (`exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic`) + Schur over F_q (`IsSimpleModule.End`)
      → `E=⊕C_E(T_i)` (r=p≥2, P-permuted) → part (1) で FPF → keystone で cyclic、非cyclic と矛盾
      (∴ 既約⟹cyclic⟹part(2)cyclic)。
- [x] **reducible case の wrapper** ✅ `fpf_of_constant_stabilizer_of_invariant_compl` (complete,
      axiom-clean, session 8): `IsCompl U W` + 両 nontrivial + 両 P-invariant ⟹ FPF。**🔑 重要発見:
      part(1) は perm=id (P-invariant 各 summand) でも成立** → reconstruction gap は無い (imprimitivity
      不要)。Maschke complement (P-invariant U⊕W=⊤) を `Bool` 2-family + `iSupIndep_pair` で part(1) に投入。
- [x] **Maschke bridge ✅ 完成** (`exists_aInvariant_complement_of_elementaryAbelian`, complete,
      axiom-clean, session 10): coprime `φ:P→*MulAut E` + elem-abelian E + `IsAInvariant φ U`
      ⟹ ∃ P-invariant complement W (`U⊓W=⊥`, `U⊔W=⊤`)。**案 B (direct) で着地** — OperatorMaschke 本体
      (L186-254) を E に直接 mirror、quotient 層を除去。`mulAutToEnd E q` (公開) でρ構成 →
      `AddSubgroup.toZModSubmodule`+`invtSubmodule` で U → submodule → `ComplementedLattice.exists_isCompl`
      (Maschke; `neZero_natCast_zmod_of_coprime` で NeZero) → `Φ` order-iso で Subgroup E に戻す。
      ⚠ instance 知見: `CommGroup E` は infer 不可 → `{ (inferInstance:Group E) with mul_comm:=hE.comm }`
      で構成; `mulAutToEnd`/`neZero_…` は `OddOrder.BG.Ch1_Preliminary` 公開、Huppert 閉包に在 (import 不要,
      open のみ)。Huppert に `open Isaacs.Ch03`+`open BG.Ch1_Preliminary` 追加。
- [x] **reducible case 組立 ✅** `fpf_of_reducible` (complete, axiom-clean, session 11): ∃ proper
      nonzero P-invariant U ⟹ Maschke で W → `IsCompl U W` (W≠⊥ は U⊔W=⊤ ∧ U≠⊤ から) →
      `fpf_of_constant_stabilizer_of_invariant_compl` → FPF。IsAInvariant→`.map`-eq 変換は inline
      `conv` (smul_mem/inv_smul_mem + `MulAut.apply_inv_self`)。一発 build。
- [ ] **part(2) 非cyclic (最後の hard piece)**: P 既約・非cyclic → R⊴P type-(p,p) + Schur over F_q
      (`IsSimpleModule.End` field) → `E=⊕C_E(T_i)` (r=p≥2 P-permuted) → part(1) で FPF。
- [x] **Lemma case-split assembly ✅** (session 12): `pGroup_cyclic_fixedPointFree` を case split で再構築
      → reducible=`fpf_of_reducible`、irreducible-cyclic=`fpf_of_abelian_of_irreducible`(P abelian は
      `IsCyclic.commGroup`、hirr 変換は `isAInvariant_iff_smul_mem.mpr`)、irreducible-非cyclic=**唯一の sorry**。
      `(hqp : q≠p)` を仮説追加 (hcop/hqE 導出)、hPodd は `orderOf x ∣ p^m` odd から。**Lemma を section
      Maschke 直後に移動** (fpf_of_reducible 前方参照回避)。⟹ **Lemma の sorry は irreducible-非cyclic のみ**。
- [ ] **唯一残る real math = part(2) 非cyclic** (Lemma の sorry): P 既約・非cyclic → R⊴P type-(p,p)
      (`exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic`) + Schur over F_q (`IsSimpleModule.End`)
      → `E=⊕C_E(T_i)` (r=p≥2 P-permuted) → part(1)(`fpf_of_constant_stabilizer_of_permuted_decomp`)。最難。

### Prop 1 assembly 進捗 (sessions 13-15)
完成済 building block (全 axiom-clean):
- `isAInvariant_eq_bot_or_top_of_transitive` (transitive on E^# ⟹ irreducible) [s13]
- `normal_isPGroup_eq_bot_of_faithful_irreducible` (faithful+irreducible ⟹ no normal q-subgroup
  ⟹ q∤|F|) [s14]
- `card_pointStabilizer_comp_eq_of_normal_of_transitive` (bridge: 定 stabilizer) [既存]
- `commutator_le_fitting_of_isCyclic_fitting` (D solvable + F cyclic ⟹ commutator≤F) [既存]
- `opCore_isCyclic_and_fpf_of_transitive` (per-prime: O_p(D) cyclic+FPF; Lemma を cite ゆえ explicit
  sorry 無だが Lemma の sorry に transitive 依存) [s15]
**Prop 1 残** (s16 で F-cyclic の blocker を精査):
- **(a) F cyclic = gate**. 経路: `[Finite][IsZGroup ↥(fitting D)][IsNilpotent ↥(fitting D)] → IsCyclic`
  (mathlib ZGroup:127; `fitting.isNilpotent` instance 在)。IsZGroup ↥F = ∀ Sylow P of ↥F, IsCyclic ↑P。
  F nilpotent ⟹ 各 Sylow 一意 (`Sylow.normal_of_isNilpotent`+`characteristic_of_normal`)、かつ
  `opCore p ↥F = ⨅ Sylow = ↑P` (`opCore_le`+`normal_pgroup_le_opCore`、`opCore=⨅Sylows`)。⚠ **fiddly chain**:
  per-prime は `IsCyclic ↥(opCore p D)` を与えるが、IsZGroup ↥F が要るのは `IsCyclic ↑(Sylow p ↥F)` =
  `IsCyclic ↥(opCore p ↥F)`。**`opCore p D ↔ opCore p ↥(fitting D)` の subgroup-of-subgroup 同定**が要
  (両者 = 最大 normal p-subgroup、fitting char in D ゆえ等しいはずだが map/subgroupOf で証明要)。
  IsCyclic transfer は `isCyclic_of_surjective _ (Subgroup.equivMapOfInjective P f hf).symm.surjective`
  (ZGroup.lean:71 pattern)。~40 行・複数 uncertain step。**次 session で grind**。
  - 代替: per-prime を `opCore p ↥(fitting D)` 版で作り直す (bridge は inclusion 経由で煩雑) → 不採用見込み。
- **(b) F FPF**: 各 O_p FPF + F=∏O_p の ∏ 分解 (f∈F^#, f_p∈⟨f⟩ で C_E(f)⊆C_E(f_p)=⊥)。F cyclic 後なら容易化。
- **(c) commutator≤F**: `commutator_le_fitting_of_isCyclic_fitting` (要 `[IsSolvable D]` 追加 = FT 帰結) + (a)。
- ⟹ (a) が gate。組めば explicit sorry 2→1 (Lemma 非cyclic のみ残)。

### ✅ session 3 (2026-06-14): Prop 1 完全 assembled — explicit sorry 2→1
- **(a) F cyclic = DONE**: `opCore p D ↔ opCore p ↥(fitting D)` の subgroup-of-subgroup 同定を
  `opCore_fitting_map_subtype_eq` (`(opCore p ↥F).map subtype = opCore p D`; ≤ は char→normal-map +
  `normal_pgroup_le_opCore`、≥ は `subgroupOf`+`map_subgroupOf_eq_of_le`) で解決 → blocker 消滅。
  `isCyclic_fitting_of_forall_opCore_isCyclic` は F nilpotent⟹各 Sylow=O_p(↥F) (一意) を `IsZGroup ↥F` に
  し mathlib `[IsZGroup][IsNilpotent]⟹IsCyclic`。**仮説は prime のみ** (`∀ p, p.Prime → IsCyclic ↥(opCore p D)`;
  証明が p を prime でしか使わない)。
- **(b) F FPF = DONE** `fitting_fpf_of_transitive`: f∈F^# で prime p|orderOf f、g=f^(|f|/p) は order p →
  `g∈O_p(↥F)` (zpowers≤ 一意 Sylow) → `(g:D)∈O_p(D)` (= opCore_fitting_map_subtype_eq) → per-prime FPF で
  C_E(g)=⊥、`C_E(f)⊆C_E(g)` (mono helper: fixed by f ⟹ fixed by f^n)。⟹ C_E(f)=⊥。
- **(c) commutator≤F = DONE** (既 session 3 の `commutator_le_fitting_of_isCyclic_fitting`)。
- **assembly** `fitting_cyclic_fixedPointFree`: `[IsSolvable D]` 追加 (FT 帰結, C_D(F)≤F に必須) + `q∣|E|` を
  `hE.isPGroup`+`IsPGroup.iff_card`+nontrivial で導出 → ⟨hcyc, F-FPF, commutator⟩。axiom-clean modulo Lemma sorry。
- **⟹ Huppert.lean の explicit sorry = 1 本** (`pGroup_cyclic_fixedPointFree` の irreducible-非cyclic case のみ)。
  full build 3802 jobs ~10s, AxiomsCheck OK。**残 frontier = Lemma 非cyclic case (Schur over F_q + type-(p,p))** 一点。
- (旧 session 9 偵察メモ) 実装経路 2 案を確定していた (案 B を採用):
   - **案 A (reuse, 推奨初手)**: `OddOrder.BG.Ch1.S04b…OperatorMaschke.exists_aInvariant_complement_in_omega1_quotient`
     を **S=⊥, R=E, p=q, A=P** で適用 → `X.map(mk'⊥) ⊓/⊔ U.map(mk'⊥)` の条件を E⧸⊥≅E で pull back。
     要: `IsAInvariant φ U` (= my hUinv 形を IsAInvariant に変換), `Omega (E⧸⊥) q 1 = ⊤` (E⧸⊥ elem-ab),
     `Subgroup.map_inf`/`map_sup`/injective(`mk'⊥` ker=⊥)で `X⊓U=⊥`/`X⊔U=⊤` に翻訳, `IsCompl.of…`。
   - **案 B (direct)**: OperatorMaschke 本体 (L186-258) を S/Ω₁ 抜きで E に直接 mirror。
     `MulDistribMulAction.compHom E φ` → `ElementaryAbelianRepresentation` で `Representation (ZMod q) P
     (Additive E)` → `AddSubgroup.toZModSubmodule`+`ρ.invtSubmodule` で U を invtSubmodule 化 →
     `MonoidAlgebra.Submodule.exists_isCompl` → `Representation.mapSubmodule` 逆で Subgroup E に戻す。
   - **完成すれば**: `fpf_of_constant_stabilizer_of_invariant_compl` に投入 → Lemma の **reducible ケース完了**。
- ⚠ **session 9 は偵察のみ (Lean commit 無し)**; 11 補題・part(1)完投済で group-theoretic core は完成、
   残 2 piece (Maschke bridge + part(2)非cyclic Schur) は heavy rep-theory infra。off-critical-path。
- ⟹ **Lemma sorry 解消 = reducible 分解存在 + part(2) 非cyclic の 2 つの heavy rep-theory が gate**。
      part(1)+part(2)cyclic の FPF producer は完備。mathlib `Representation`/`IsSimpleModule`/Maschke 調査要。
- [ ] **part (2) irreducible case**: Schur over F_q (`IsSimpleModule.End`=division ring) + type-(p,p)
      (`exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic`) + `E=⊕C_E(T_i)` → part(1)。
- [x] **Prop 1 abelian-quotient step** ✅ `commutator_le_fitting_of_isCyclic_fitting` (complete, axiom-clean,
      session 3): D 可解 + F(D) cyclic ⟹ `commutator D ≤ F(D)`。citeable 部品で組立:
      `S01.centralizer_fitting_le_fitting` (C_D(F)≤F, 可解) + `IsCyclic.mulAutMulEquiv`+`commGroupOfInjective`
      (MulAut F abelian) + `Abelianization.commutator_subset_ker` + `MulAut.conjNormal`(ker=C_D(F))。
- [ ] **Prop 1 残**: 「F cyclic」= **mathlib `ZGroup.lean:127`** `[IsZGroup G][IsNilpotent G]⟹IsCyclic G`
      が使える (F nilpotent + 各 Sylow=O_p cyclic[Lemma 依存])。「F FPF」assembly (各 O_p FPF⟹F FPF) +
      odd⟹solvable (FT 依存) が残。Lemma が最大の gate。
- [ ] file が sorry-free 化したら keystone+bridge を AxiomsCheck の **新 Appendices section** に登録
      (LAUNCH rule #4; 現状 file に 2 sorry 残ゆえ未登録; 完成済 3 本は #print axioms で clean 確認済)。

### ✅ session 4 (2026-06-14): Lemma 非cyclic 判定 + Appendix I **Prop 2** 発見 → 攻略順 改訂
- **Lemma 非cyclic sorry の真ボトルネック = [H] III.7.5 = Gorenstein 5.4.10** (non-cyclic odd p-group ⟹
  normal type-(p,p))。Peterfalvi p.135-136 原文確認: Schur ([Is]1.5) で End_{𝔽_q[P]}(E)=有限体 ⟹ Z(P) cyclic
  ⟹ `Ω₁(Z(P))` 位数 p ⟹ repo の available `…_of_prime_sq_dvd_card_omega1Center` (abelian-center) は **不適用**,
  まさに S04 ≈L911 で deferred な cyclic-center case。**→ issue 2004 で BG lane に委譲** (S04 は所有権外)。
  Huppert.lean の sorry comment に精密化記録済。**この sorry は当面 park** (off-critical-path Part II)。
- **🆕 Appendix I に Proposition 2 が在る** (p.136, PDF 画像で全文復元 — mmd は MISSING_PAGE, 既存 note も
  Prop2 を見落としていた)。**現状 Huppert.lean に未形式化**。statement:
  > U が elem-ab E (order pⁿ) に faithful 作用, T⊴U cyclic normal が E に **irreducible** 作用。
  > **(a)** F=𝔽_p[T]⊆End(E) は pⁿ 元の体, E は F 上 1 次元。**(b)** U は semilinear; s∈E^# で C_U(s)≅Aut(F) の部分群。
  - 証明 (p.136): (a) Schur で F₁=End_T(E)=有限 division ring, T 可換ゆえ F=𝔽_p[T]⊆F₁ は可換部分環=体;
    E は既約 F-加群=F 上 1 次元 ⟹ |F|=|E|。(b) u∈U は加法的自己同型, σ(λ): u(λs)=σ(λ)u(s) が体自己同型
    (U が E⋊T に作用するので σ(λμ)=σ(λ)σ(μ)), u semilinear; C_U(s)→Aut(F) が群同型。
  - **🔑 Gorenstein 不要・Schur のみ ⟹ 非cyclic sorry より遥かに tractable**。mathlib `IsSimpleModule`/Schur
    (End=division ring) + 有限可換 domain=体 + 体上既約=1次元。`IsElementaryAbelian.zmodModule` (PRank.lean:87)。
  - **🔗 Appendix C (NearFields) Prop 2 は "Appendix I, Prop 2" を引く ⟹ Prop 2 は Appendix C の前提**。
    かつ Prop 2(a) の Schur 部品 (End=体 ⟹ Z 部分が cyclic) は **Lemma 非cyclic の Z(P) cyclic 部分も再利用可**。
- **改訂 攻略順**: **Prop 2 (Huppert.lean, 次の主目標, tractable)** → Appendix C/D → Lemma 非cyclic (issue 2004 待ち)。
  既存 scaffold: `NearFields.lean`/`Suzuki2Groups.lean`/`FeitSibley.lean`/`Suzuki.lean` (各 ~2.5-5.6k, opaque, 要 audit)。

### ✅ session 5 (2026-06-14): Prop 2 形式化 — 設計確定 + mathlib 部品検証 (probe で実証)
**目標**: Appendix I Prop 2 を `OddOrder/Peterfalvi/Appendices/SemilinearField.lean` (新 leaf) に。
**検証済 mathlib 部品** (全て probe build で確認):
- 作用→表現: `(mulAutToEnd E p).comp ψ : Representation (ZMod p) T (Additive E)` (`mulAutToEnd` =
  `OddOrder.BG.Ch1_Preliminary`, `OperatorMaschke.lean:140`)。module = `AddCommGroup.zmodModule hpsmul`
  (hpsmul : ∀ x:Additive E, p•x=0)。
- 既約⟺単純: `Representation.irreducible_iff_isSimpleModule_asModule ρ : IsIrreducible ρ ↔ IsSimpleModule k[T] ρ.asModule`
  (mathlib `RepresentationTheory/Irreducible.lean`)。`IsIrreducible ρ = IsSimpleOrder (Subrepresentation ρ)`。
- Schur: `Mathlib/RingTheory/SimpleModule/Basic.lean:530` `[DecidableEq (End)][IsSimpleModule R M] → DivisionRing (Module.End R M)`。
- 有限除環=体: `littleWedderburn` (instance, `LittleWedderburn.lean:166`, priority 100, 自動)。
- 単純⟹1次元: `isSimpleModule_iff_finrank_eq_one {R}[DivisionRing R] : IsSimpleModule R M ↔ finrank R M = 1`
  (`SimpleModule/Rank.lean:17`)。
- 1次元⟹|F|=|E|: `FiniteField.pow_finrank_eq_natCard` 系 / `card = (card F)^finrank` (PRank に既出パターン)。
**🔑 設計 (probe で確定): 抽象 core + bridge の 2 層**:
- **core** = 抽象 `k[T]`-module 上で述べる: `variable {k}[Field k][Finite k]{T}[CommGroup T][Finite T]
  {M}[AddCommGroup M][Module (MonoidAlgebra k T) M][Finite M][IsSimpleModule (MonoidAlgebra k T) M]`
  → `End_{k[T]}(M)` は体 (✅ probe9 で tactic-mode build 通過: `Finite.of_injective _ DFunLike.coe_injective`
  で End 有限 → littleWedderburn)。残: `finrank (End) M = 1` (M を End 上単純にする or 像 F=𝔽_p[T] 経由) + |·|。
- **bridge** = multiplicative E + φ から core を起動 (M := ρ.asModule, instances を term-mode で供給)。
**🛑 GOTCHAS (probe で判明・再調査不要)**:
  1. `Group+IsMulCommutative→CommGroup` は **scoped instance** (`Defs.lean:1391`) ⟹ `open scoped IsMulCommutative` 必須。
  2. ρ は `let ρ := ...` で導入 (**`set` は asModule instance 解決を阻害**)。
  3. **ZMod p の Field-vs-CommSemiring diamond**: `[Fact p.Prime]` が Field-path semiring を強制 →
     core を `ZMod p` でなく **generic `[Field k]`** で述べ、bridge で `k := ZMod p` 起動 (probe C/D/E で回避確認)。
  4. **noncomputable `asModule` Module instance は term-mode で解決するが tactic-mode (`letI/haveI := inferInstance`)
     で失敗** (probe7/8) ⟹ core を **抽象 `[Module (MonoidAlgebra k T) M]`** で述べ asModule を core 内で使わない (probe9 で解決)。
  5. `Finite ρ.asModule` は `inferInstanceAs (Finite (Additive E))` (asModule は def, 自動 Finite 不発)。
  6. 定義は `noncomputable` (Module instance が noncomputable)。
**次 session**: leaf 作成 → core (Field 部 done, finrank=1 を詰める) → bridge → Prop 2(a)、その後 (b) semilinear。
sorry を増やさない方針ゆえ **core を sorry-free にしてから commit** (中間 sorry leaf は出さない)。

### ✅ session 6 (2026-06-14): Prop 2(a) CORE landed (sorry-free, axiom-clean)
新 leaf `SemilinearField.lean` (namespace `Appendices.Huppert`, OddOrder.lean Appendices block に import 追加)。
抽象 core (k 有限体, T 可換, M 有限単純 k[T]-module):
- `endField` : `End_{k[T]}(M)` は体 (`noncomputable def`, Schur+Wedderburn auto)。
- `isSimpleModule_end` : M は D=End 上単純 (k[T] 可換ゆえ scalar map `LinearMap.lsmul r ∈ D` →
  D-submodule = k[T]-submodule → k[T] 単純で ⊥/⊤; `refine { eq_bot_or_eq_top := ... }`, `Submodule.eq_top_iff'`)。
- `finrank_end_eq_one` : `finrank D M = 1` (`isSimpleModule_iff_finrank_eq_one`)。
- `natCard_end_eq` : `|D| = |M|` (`Module.card_eq_pow_finrank` は **Fintype.card** ゆえ `Fintype.ofFinite`+`Nat.card_eq_fintype_card`)。
全て propext/choice/Quot のみ。full build 3807 jobs ~7s, AxiomsCheck OK。
**次 session = bridge**: 教科書 data `(E elem-ab p-group, φ:U→*MulAut E faithful, T⊴U cyclic irreducible)` から
core 起動。M := ρ.asModule (ρ=(mulAutToEnd E p).comp φ|_T), instances を term-mode 供給 (gotchas 4 参照),
`IsSimpleModule k[T] ρ.asModule` を「E が T-irreducible」から `irreducible_iff_isSimpleModule_asModule` で。
k := ZMod p (Field via Fact)。→ Prop 2(a) 完全形 (F=𝔽_p[T] の体構造 + E 1次元 + |F|=pⁿ)。その後 (b) semilinear/C_U(s)≅Aut(F)。

### ⚠ session 7 (2026-06-14): core 一般化 (CommRing k) 済 + bridge は asModule 詰まり (要別経路)
- **core 改良 (commit 済)**: `[Field k][Finite k]` → **`[CommRing k]`** に弱化 (End=体 は M 有限のみ依存)。
  bridge で `k:=ZMod p` 起動時の **ZMod p semiring diamond** (Field-path via Fact vs CommRing-path via zmodModule)
  を回避するのに必須。leaf sorry-free, full build 3807 jobs ~3s。
- **🛑 bridge BLOCKED on asModule instance 不安定性** (probe 多数で診断):
  - `(mulAutToEnd E p).comp ψ : Representation (ZMod p) T (Additive E)` の構築は OK (probe11-13)。
  - **`Module (MonoidAlgebra (ZMod p) T) ρ.asModule` の synth が arg-position で不安定**:
    `have h : Module ... := inferInstance` (goal-position) 単独では通る (probe13/15) が、
    `Module.End ... ρ.asModule` や `IsSimpleModule ... ρ.asModule` を **型に書く (arg-position)** と失敗、
    かつ後続行があると先行の goal-position synth まで連鎖失敗 (probe14/18/21)。haveI/letI 切替も別の壁
    (letI zmodModule → `MulOne` stuck; probe20)。`open scoped Classical` も阻害 (除去要)。
  - `[Representation.IsIrreducible ρ]` を入れると `IsSimpleModule k[T] ρ.asModule` は mathlib instance
    (Irreducible.lean:53) で auto 化できる (probe18 で hsimp 行は解決) が、`Module.End` 形成は別途失敗。
  - これは **数学的 gap でなく Lean4/mathlib の noncomputable asModule typeclass-elaboration 摩擦**。
- **▶ 次 session で試す別経路** (優先順):
  1. **asModule を使わず `Additive E` に直接 k[T]-module を張る**: `Module.compHom (Additive E)
     (ρ.asAlgebraHom).toRingHom` で clean type 上の instance を letI。core の M := Additive E。
     `Module.End (k[T]) (Additive E)` は clean type ゆえ arg-position synth が通る可能性。
     (注意: 既存 `Module (ZMod p) (Additive E)` と two-scalar; `IsScalarTower` 整合, IsSimpleModule 変換要)。
  2. core を `ρ : Representation` 直接取りに再構成 (asModule を core 内 1 箇所に閉じ込め)。
  3. 全 instance を `@natCard_end_eq (ZMod p) _ T _ _ ρ.asModule _ <term> ...` で term-position 明示供給。
  - downstream (App C / Lemma の Z(P) cyclic) は core を直接使う手も (bridge は便宜 adapter)。

### ✅ session 8 (2026-06-14): bridge plumbing SOLVED (compHom on clean Additive E) + core refactor
- **🎯 bridge plumbing 解決 (probe29 で実証)**: asModule wrapper を**使わず**、clean type `Additive E` に
  直接 k[T]-module を張る:
  ```
  let ρ : Representation (ZMod p) T (Additive E) := (mulAutToEnd E p).comp ψ
  letI : Module (MonoidAlgebra (ZMod p) T) (Additive E) :=
    Module.compHom (Additive E) ρ.asAlgebraHom.toRingHom   -- = asModule の中身を Additive E に
  ```
  → `Module.End (MonoidAlgebra (ZMod p) T) (Additive E)` が **arg-position で形成可能** (clean type ゆえ
  asModule の synth 不安定を回避)、`natCard_end_eq (M := Additive E)` 適用 OK、
  `Nat.card (End) = Nat.card E` (via `Nat.card_congr Additive.toMul`)。**再調査不要: asModule は罠, compHom on Additive E が正解。**
- **core refactor (commit c83c65a0)**: 過剰な global `instance : Finite (Module.End ...)` は
  asModule+IsIrreducible synth と干渉 → `theorem finite_end` 化し各定理内 haveI に (防御的)。leaf sorry-free, axiom-clean。
- **▶ 残り = IsSimpleModule (MonoidAlgebra (ZMod p) T) (Additive E) を群論的既約性から** (compHom 構造上):
  bridge の唯一 sorry。`IsSimpleOrder (Submodule (k[T]) (Additive E))`: k[T]-submodule N (compHom 構造) は
  ZMod p-subspace かつ T-stable → ψ-invariant subgroup H (OperatorMaschke の `toZModSubmodule`/`toSubgroup'`
  対応を流用) → hirr (ψ-inv subgroup は ⊥/⊤) で N=⊥/⊤。Nontrivial は Nontrivial E から。~50-80 行見込み。
  注意: compHom の k[T]-action は `of t • x = ρ.asAlgebraHom (of t) x = (ψ t) を Additive 上に`。
- これで Prop 2(a) 完全形 (F=End=𝔽_p[T], E 1次元, |F|=pⁿ) → その後 (b) semilinear/C_U(s)≅Aut(F)。

### ✅✅✅ session 9 (2026-06-14): Prop 2(a) COMPLETE (textbook form, sorry-free, axiom-clean)
`exists_field_of_irreducible` (SemilinearField.lean, Prop2Bridge section, commit 246390e1):
T 可換が elem-ab p-group E に irreducible 作用 ⟹ `∃ 有限体 F` が E に作用、E は F 上 1 次元、|F|=|E|
(F = 𝔽_p[T] = End_{𝔽_p[T]}(E))。**4 session 越しの asModule bridge blocker 解除**。
- bridge 構成: (1) clean type `Additive E` に compHom で k[T]-module (asModule wrapper 回避), (2) key:
  `(of t)•x = ofMul (ψ t (toMul x))` (`show ... from rfl` + `asAlgebraHom_of` + rfl), (3) IsSimpleModule:
  k[T]-submodule N → ψ-invariant subgroup `{e | ofMul e ∈ N}` → hirr で ⊥/⊤ (compHom action 経由), (4) core 適用。
- 🔑 知見 (再調査不要): ∃ の F は `Type u` 明示 (Type _ は universe mismatch); End-apply-module は
  `Module.End.applyModule` 明示供給; E は `[CommGroup E]` で取る (Additive E instances が statement で解決)。
- full build 3807 jobs ~3.3s, axiom-clean。
- **▶ 次 = Prop 2(b)**: U semilinear + s∈E^# で C_U(s) ≅ Aut(F) 部分群。U faithful + T⊴U 必要。
  (b) は (a) の F に対する semilinear 写像論 (σ(λ): u(λs)=σ(λ)u(s) が体自己同型)。その後 Appendix C へ。
  あるいは Appendix C は Prop2(a) で十分かもしれない (要精査) → C へ進む選択肢も。

### session 10 (2026-06-14): Prop 2(a) AxiomsCheck 登録済 + C/D/E audit + Prop 2(b) path 確定
- **Prop 2(a) → AxiomsCheck 登録済** (commit a4e9bab7, LAUNCH rule 4): AxiomsCheck.lean 末尾 Appendices section に
  isSimpleModule_end/finrank_end_eq_one/natCard_end_eq/exists_field_of_irreducible (全 propext/choice/Quot)。
- **C/D/E/A audit**: 全て opaque-Prop scaffold (structure Hypothesis + theorem w/ sorry, 67-158 行)。
  NearFields 2 / Suzuki2Groups 4 / FeitSibley 3 / Suzuki 5 sorry。**easy win 無し** — どれも未構築の
  research-level infra (FT+Brauer-Suzuki, 体構成, coherence 等) に bottom-out。⟹ Appendix I を続けるのが最善。
- **🎯 Prop 2(b) path 確定 (mathlib API 検証済, 実装は次 session)**:
  - **`LinearEquiv.conjRingEquiv (e : M₁ ≃ₛₗ[σ] M₂) : End R₁ M₁ ≃+* End R₂ M₂`** (Equiv/Basic.lean:571) が核 —
    semilinear equiv から End 環の ring iso。σ_u : F ≃+* F が直接得られる。
  - **`MonoidAlgebra.domCongr R A (c : T ≃* T) : A[T] ≃ₐ[R] A[T]`** (Basic.lean:304) で τ_u を c から構成。
  - **clean 抽象 formulation (U/Subgroup を回避)**: (a) の setup + `(u : MulAut E) (c : T ≃* T)
    (hc : ∀ t, ψ (c t) = u * ψ t * u⁻¹)` ["u が ψ(T) を c 経由で正規化"]。
    → φ(u)=`MulEquiv.toAdditive u` を `Additive E ≃ₛₗ[τ_u] Additive E` (τ_u=domCongr c) として構成
    → conjRingEquiv で σ_u : F ≃+* F (field auto)。U/T⊴U は c=conj-by-u の薄い wrapper。
  - **hard part = semilinear equiv の map_smul'** (∀ r∈k[T], `u(r•x)=τ_u(r)•u(x)`): of-t case は bridge key
    + hc で出るが、全 r へは MonoidAlgebra induction/generating-set 要。~100-150 行見込み, 1-2 session。
  - その後 C_U(s)≅Aut(F) → Appendix C へ (C の Prop2 が σ_y にこれを使う)。

### ✅✅✅ session 11 (2026-06-14): Prop 2(b) COMPLETE ⟹ Appendix I Prop 2 全形式化
`exists_field_semilinear` (SemilinearField.lean, commit b33c6efc, AxiomsCheck 登録済): (a) の体 F +
(b) semilinearity — g:MulAut E が T-action を正規化 (ψ(c t)=g·ψt·g⁻¹, c:T≃*T) ⟹ g は F 上 semilinear,
σ=conjugation by g on F=End_{𝔽_p[T]}(E)。`∀ g c hc, ∃ σ:F≃+*F, ∀ a x, g(a•x)=σ(a)•g(x)` (F 共有)。
- 核: (1) k[T]-semilinearity `uLin(r•x)=τ(r)•uLin x` (τ=`MonoidAlgebra.domCongr c`) を
  **`MonoidAlgebra.induction_on`** で (of-t case は `g·ψt=ψ(c t)·g` = hc + mulAutToEnd monoid-hom);
  (2) σ = **`LinearEquiv.conjRingEquiv`** of τ-semilinear equiv (**`RingHomInvPair.of_ringEquiv`** で InvPair);
  (3) F-semilinearity は `conjRingEquiv_apply`。
- 🔑 知見 (再調査不要): semilinear ≃ₛₗ[τRing] は `RingHomInvPair.of_ringEquiv τRing` ×2 で InvPair 供給;
  conclusion は `MulEquiv.toAdditive g` だが proof は uLin (両 coe defeq → `show uLin (a•x)=...` で橋渡し);
  `Module.End.mul_apply`/`Module.End.smul_def`/`conjRingEquiv_apply_apply`。
- full build 3807 jobs ~6.3s, axiom-clean。**Appendix I (Huppert) = Prop 1 ✅ + Prop 2(a)(b) ✅ + Lemma 1 sorry
  (Gorenstein 5.4.10, issue 2004 で defer)**。
- **▶ 次 = Appendix II (NearFields)**: Prop 2 が "Appendix I Prop 2" を引く (σ_y に exists_field_semilinear)。
  NearFields.lean は opaque scaffold (2 sorry) → faithful 化 + Prop 1 (FT+Brauer-Suzuki gate) / Prop 2 (体構成
  F_{r²,2} + exists_field_semilinear 接続) を精査。Prop 1 は重い infra gate ⟹ Prop 2 から着手が現実的。

### session 12 (2026-06-14): Appendix II (NearFields) 着手 — faithful 構造 + 基礎
- gate 確認: main は Lane G が BG §13 (13.6) 中。**BG §14/15/16 未到達** ⟹ H の §10-13 critical-path gate
  は firmly down, Appendices 継続が正。
- **faithful `NearField` class** (commit 786d7d72): `AddCommGroup + GroupWithZero + right_distrib`
  (opaque FiniteNearField を置換予定)。GroupWithZero で mult API (mul_inv_cancel₀ 等) 無料継承。
- **near-field basics** (commit 0bd60d48): `rightMul` (a≠0 で右乗 = 加法自己同型, right_distrib+可逆) /
  `addOrderOf_eq_of_ne_zero` (F^* が F^# に right-mult で推移 ⟹ 非零元の加法位数一定) /
  **`exists_prime_char`** (∃ prime f, ∀x, f•x=0 = (F,+) elem-ab; 共通位数の約数論で素数性)。全 proven, sorry 増無し。
- **▶ 次 = Prop 2 本体**: F near-field, A=Fˣ の cyclic index-2 部分群。
  (1) A は (F,+) に rightMul で作用; (2) `exists_prime_char` で (F,+) elem-ab → **exists_field_semilinear**
  適用準備 (E := Multiplicative F で IsElementaryAbelian f 化, A-action を MulAut (Multiplicative F) 化);
  (3) A irreducible (|F|=2|A|+1 counting 矛盾); (4) σ_y/Aut(K) 解析 → field or F_{r²,2}。複数 session 見込み。
  Prop 1 は FT+Brauer-Suzuki gate (重い, Gorenstein 5.4.10 類似なら issue 化 defer)。

### session 13-14 (2026-06-14): Appendix II — A-action 完成
- `isElementaryAbelian_multiplicative` (commit 331aae13): (F,+) を Multiplicative F で見て elem-ab
  (exists_field_semilinear が要する形)。
- **`rightMulAction`** (commit b24d2e76): 可換部分群 A⊆Fˣ の (F,+) への右乗作用を `A →* MulAut (Multiplicative F)`
  に。右乗は加法的 (rightMul) だが hom 性に A 可換要 (右乗は一般に anti-hom) → `hcomm` 引数で渡す。
  🔑 知見: `IsCyclic.commGroup` を haveI すると `*`-diamond で mul_comm の rw が壊れる → 可換性は `hcomm`
  仮説 (caller が A cyclic から供給) で回避。`rightMulAction_toAdd` (作用は加法座標で x*u)。
- **▶ 次 = "field structure" 中間結果**: exists_field_semilinear を `E:=Multiplicative F`, `T:=↥A`,
  `ψ:=rightMulAction A hcomm` で起動。要 irreducibility `hirr` = A-invariant subgroup は ⊥/⊤
  (Peterfalvi counting: F=F₁⊕F₂ なら A が各 Fᵢ に FPF → |Fᵢ|≥|A|+1, |F|=2|A|+1≥(|A|+1)² 矛盾)。
  ⟹ (F,+) は体 K 上 1 次元 + A は乗法で作用。これが Prop 2 の前半 (Appendix I work を使う部分)。
  後半 (σ_y/Aut(K) → field or F_{r²,2} 分類) + Prop 1 (Brauer-Suzuki gate) は重い remaining。

### session 15 (2026-06-14): Appendix II — Prop 2 field-structure 中間結果 (Appendix I 接続)
- **`nearField_field_structure`** (commit 7e787447): A⊆Fˣ 可換が (F,+) に right-mult で irreducible 作用
  ⟹ (F,+) は有限体 K 上 1 次元, |K|=|F|。near-field data (isElementaryAbelian_multiplicative + rightMulAction)
  を exists_field_semilinear に投入。**Appendix C Prop 2 の前半 (Appendix I を使う部分) 完成**。
  irreducibility は hyp (index-2 counting は別 lemma)。CommGroup ↥A は hcomm から構築 (IsCyclic.commGroup
  の *-diamond 回避)。NearFields が SemilinearField を import するように。
- **▶ 次 = irreducibility counting** (hirr 仮説を index-2 から discharge): A index-2 in Fˣ ⟹ A irreducible on (F,+)。
  要 (1) A FPF on F^# (x*a=x, x≠0 ⟹ a=1 by F^* 群 cancellation), (2) Maschke (|A| coprime |F|; A-inv U に
  complement), (3) counting: |F_i|≥|A|+1, |F|=2|A|+1≥(|A|+1)² 矛盾。substantial。
  - その後 σ_y/Aut(K) → field or F_{r²,2} 分類 (最重) + Prop 1 (Brauer-Suzuki gate)。

### session 16-19 (2026-06-14): Appendix II Prop 2 — irreducibility counting の補題群
counting (A index-2 ⊆ Fˣ ⟹ A irreducible on (F,+)) の部品を順次 (全 proven, sorry 増無し):
- `rightMulAction_eq_self_iff` (free action: 非自明元は非零固定点無し, GroupWithZero cancel)
- `card_coprime` (|A| ⊥ |F|: |A|∣|Fˣ|=|F|-1 Lagrange + 連続整数互素)
- `card_eq_of_index_two` (|F|=2|A|+1: card_mul_index + card_units)
- **`card_group_dvd_card_of_free`** (一般補題: free finite action ⟹ |G|∣|α|; selfEquivSigmaOrbits +
  orbit-stabilizer + index_bot; mathlib 昇格候補)。
- **▶ 残 (irreducibility 完成まで ~2 session)**: (1) ↥A の U^# (=↥U\{1}) への MulAction setup + free →
  card_group_dvd_card_of_free で |A|∣|U|-1 → |U|≥|A|+1; (2) Maschke (exists_aInvariant_complement_of_elementaryAbelian
  + card_coprime) で complement W; (3) IsComplement card で |F|=|U||W|; (4) arithmetic
  ((|A|+1)²>2|A|+1=|F| 矛盾)。⟹ nearField_field_structure を index-2 で unconditional 化。
  その後 σ_y/Aut(K) → field or F_{r²,2} 分類 (重い・F_{r²,2} 構成は loop 完遂困難の可能性)。

### ✅✅✅ session 20 (2026-06-14): Appendix II Prop 2 — irreducibility/counting COMPLETE (3 commits)
session 16-19 の残 4 ステップを 1 ループで完遂 (全 sorry-free・axiom-clean・AxiomsCheck 登録済):
- **`add_one_le_card_of_aInvariant_ne_bot`** (8a734e8a): A-不変 U≠⊥ ⟹ |A|+1≤|U|。`MulDistribMulAction.compHom`
  で ↥A を Multiplicative F に作用させ、`SubMulAction` carrier `{x|x∈U∧x≠1}` (=U∖{1}) 上で free
  (`rightMulAction_eq_self_iff`→stabilizer=⊥) → `card_group_dvd_card_of_free` で |A|∣|U∖{1}|。
  |U∖{1}|+1=|U| は `Equiv.optionSubtypeNe`+`Finite.card_option`。U≠⊥ で正値性 → `Nat.le_of_dvd`+omega。
  🔑 知見: 部分群-vs-SubMulAction の二重 coe で `OneMemClass.coe_eq_one` の SetLike 推論が誤爆 →
  `Subtype.ext`/`Subtype.ext_iff` を直接使い `(1:↥U).val ≡ 1` defeq に委ねる。
- **`exists_aInvariant_complement_of_elementaryAbelian`** (3df0d60d): elem-ab p-group E, φ:A→*MulAut E,
  (|A|,|E|) coprime, p∣|E| ⟹ A-不変 U に A-不変 complement W (IsCompl U W)。**BG の
  `exists_aInvariant_complement_in_omega1_quotient` を Ω₁/quotient 層抜きで E 直接に再構成**
  (`mulAutToEnd`/`neZero_natCast_zmod_of_coprime`/`ComplementedLattice.exists_isCompl`/toZModSubmodule
  /toSubgroup' を流用)。SemilinearField が OperatorMaschke を import 済 ⟹ NearFields closure に到達可。
- **`rightMulAction_irreducible_of_index_two`** (df2d5876): A index-2 ⟹ ∀ A-不変 U, U=⊥∨U=⊤。
  上 2 engine 組立: U proper nontrivial ⟹ |U|,|W|≥|A|+1 (W≠⊥ ∵ U≠⊤), |F|=|U|·|W| (`IsComplement'.card_mul`
  via `isComplement'_of_disjoint_and_mul_eq_univ`+`← Subgroup.mul_normal`+`coe_top`; Mult F abelian で
  W.Normal auto) ≥(|A|+1)²>2|A|+1=|F| を nlinarith。f∣|F| は非単位元の order=f (Nat.dvd_prime)。
- **`nearField_field_structure_of_index_two`** (df2d5876): 上で hirr を discharge → index-2 から
  **field structure 半 (F は K 上 1 次元, |K|=|F|) を unconditional 化**。
- full build 3807 jobs 〜6s, AxiomsCheck 4 件 OK (propext/choice/Quot)。NearFields 実 sorry は依然 2
  (opaque scaffold: rankOne_affine_nearField=Prop 1 / cyclic_index_two_nearField_classification=Prop 2 全体)。
- **▶ 次 = Prop 2 後半 (分類)**: σ_y/Aut(K) 解析で「field or 例外 near-field F_{r²,2}」を確定し
  scaffold `cyclic_index_two_nearField_classification` を faithful 化。F_{r²,2} の明示構成が最重
  (loop 完遂困難の可能性大 — ここは hub に重さを flag 済の領域)。代替で C/D/E/A の他 appendix audit も可。
  Prop 1 (`rankOne_affine_nearField`) は FT+Brauer-Suzuki gate (重い・後回し)。

### session 21 (2026-06-14): Appendix II Prop 2 分類 — F_{r²,2} を抽象「twisted near-field」で着手
分類後半 (σ_y/Aut(K) → field or F_{r²,2}) のうち **F_{r²,2} の構成**に着手。論文 (pp.137-138) を精読し
設計確定 (next session は再設計不要):
- **App C Prop 2 全体の道筋** (07.0_..._On_Near-Fields.mmd): (1) A irreducible【済 = rightMulAction_irreducible_of_index_two】
  → (2) Appendix I Prop2 で「∘ と両立する体構造 K」+ y∈A で x∘y=xy → (3) y∈F⋆ で x∘y=x^{σ_y}·y (σ_y∈Aut K 半線形)
  → (4) y↦σ_y は F⋆→Aut(K) hom, ker⊇A → (5) ker=F⋆ なら **F は体**; さもなくば y∈F⋆−A で σ_y 位数2
  → K=𝔽_{r²}, x^{σ_y}=x^r, **F≅F_{r²,2}**, |Z(F⋆)|=r−1。
- **F_{r²,2} 構成の抽象化 (commit d9f4d3fc)**: 論文の x∘y=(y平方?xy:x^r y) を **`TwistData K`** で抽象化
  = (σ:RingAut K, σ²=1, χ:Kˣ→*Mult(ZMod2) σ不変)。`x ∘ y = σ^{χ(y)}(x)·y`。**有限体/Frobenius/quadraticChar の
  plumbing 不要** (それは F_{r²,2} instantiation で後付け); near-field 公理は (σ²=1, χ hom, χ∘σ=χ) のみで出る。
  **逆元は明示**: y⁻¹_∘ = σ^{χ(y)}(y⁻¹) (χ(y⁻¹)=χ(y) in ZMod2, σ^k(y)σ^k(y⁻¹)=σ^k(1)=1) ⟹ 有限cancel→group 補題不要。
  twAut e := if e=0 then 1 else σ (`.val`/σ^n を避け twAut_add が綺麗)。
- **🔑 Lean 知見 (再調査不要)**: (1) twExp は `open scoped Classical in` で Decidable(y=0) 供給;
  (2) **ZMod 2 の if-条件は fin_cases だと `0=0` が eq_self で潰れない (リテラル不一致)** → `rcases (show e=0∨e=1 by decide)`
  + subst で literal 化し `show (1:ZMod2)+1=0 from by decide` で書換える; (3) RingEquiv の ≠0 保存は
  `rw [ne_eq, EmbeddingLike.map_eq_zero_iff]`; (4) `simp +decide` は reduceIte に効くが上記リテラル不一致は別問題。
- **▶ 残ステージ** (each 完全 lemma で commit, sorry 増やさない):
  - **Stage 2 (assoc)**: twExp_mul/twExp_σ/twExp_twAut/twExp_twMul (χ の乗法性 + χ∘σ=χ) → twMul_assoc
    (非零は twAut_twAut [= twAut a(twAut b x)=twAut(a+b)x, **RingAut mul の適用方向を要確認**] + add_comm; 零は absorb)。
  - **Stage 3 (instance)**: twInv 明示 + GroupWithZero + 右分配 ⟹ `NearField` instance on K (TwistData から)。
  - **Stage 4 (F_{r²,2})**: K=𝔽_{r²} (GaloisField/Finite 体で [K:𝔽_r]=2), σ=Frobenius^? (x↦x^r, σ²=1),
    χ=quadraticChar で TwistData を実体化 → 例外 near-field 確定。‖ classification skeleton (σ hom + field 方向)。
  - 注: scaffold `cyclic_index_two_nearField_classification` の faithful 化は Stage 4 + skeleton 後。

## 3. 攻略順 (LAUNCH 準拠)
B → (C/D 並行) → E → A (最難・最後)。各々 opaque→faithful 化 + citeable 部の完全証明。
C/D/E は citeable shortcut 無 ⟹ faithful-statement + 精密 gap 局所化が現実的着地点。
**司令塔への flag**: appendices は off-critical-path (Part II)。FT 本線進展ではない旨ユーザー認識済。
