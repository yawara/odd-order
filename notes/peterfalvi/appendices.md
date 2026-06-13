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

## 3. 攻略順 (LAUNCH 準拠)
B → (C/D 並行) → E → A (最難・最後)。各々 opaque→faithful 化 + citeable 部の完全証明。
C/D/E は citeable shortcut 無 ⟹ faithful-statement + 精密 gap 局所化が現実的着地点。
**司令塔への flag**: appendices は off-critical-path (Part II)。FT 本線進展ではない旨ユーザー認識済。
