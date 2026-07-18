/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.LayerRestriction
import OddOrder.Isaacs.Ch09_MoreSubnormality.SubnormalSocle
import OddOrder.Isaacs.Ch09_MoreSubnormality.PResidual
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroups

/-!
# Isaacs Ch. 9 — §9C: Thompson–Wielandt (Theorems 9.23/9.24), p. 283–284

まず `core_H(D)` (相対 normalCore = `D` に含まれ `H` に normal な最大部分群) の infra を
用意する. Theorem 9.24 の statement (`M = core_H(D)`, `N = core_K(D)`, `E = M∩N`,
`U = core_H(E)`, `V = core_K(E)`) と proof で使う.

- `relCore H D` (= `core_H(D)`): `((D.subgroupOf H).normalCore).map H.subtype`.
- `relCore_le` (`≤ D`), `relCore_le_left` (`≤ H`),
  `le_normalizer_relCore` (`H ≤ N_G(core_H(D))`, すなわち `core_H(D)` は `H` に normal),
  `le_relCore` (最大性: `N ≤ D`, `N ≤ H`, `H ≤ N_G(N)` ⇒ `N ≤ core_H(D)`).
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

variable {G : Type*} [Group G]

section /- 9C: relative core `core_H(D)` -/

/-- **`core_H(D)`** (相対 normalCore): `D` に含まれ `H` に normal な最大の部分群.
`↥H` 内の `normalCore` を `H.subtype` で押し出す. -/
def relCore (H D : Subgroup G) : Subgroup G :=
  ((D.subgroupOf H).normalCore).map H.subtype

theorem relCore_le_left (H D : Subgroup G) : relCore H D ≤ H :=
  Subgroup.map_subtype_le _

theorem relCore_le (H D : Subgroup G) : relCore H D ≤ D :=
  (Subgroup.map_mono (Subgroup.normalCore_le _)).trans
    (by rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left)

/-- `core_H(D)` は `H` に normal (`H ≤ N_G(core_H(D))`). -/
theorem le_normalizer_relCore (H D : Subgroup G) :
    H ≤ Subgroup.normalizer (relCore H D : Set G) :=
  le_normalizer_map_subtype_of_normal (Subgroup.normalCore_normal _)

/-- `core_H(D)` の元の特徴づけ: `x ∈ core_H(D) ⟺ x ∈ H` かつ `H` のすべての共役で `D` に入る.
(`core_H(D) = ⋂_{h ∈ H} D^h ⊓ H` の元レベル版; Thm 9.24 Case 2 で
「`P ⊆ D^k` がすべての `k ∈ K` で成り立つ ⇒ `P ⊆ core_K(D)`」に使う.) -/
theorem mem_relCore_iff {H D : Subgroup G} {x : G} :
    x ∈ relCore H D ↔ x ∈ H ∧ ∀ h ∈ H, h * x * h⁻¹ ∈ D := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun h hh => ?_⟩
    simpa [Subgroup.mem_subgroupOf] using hy ⟨h, hh⟩
  · rintro ⟨hxH, hconj⟩
    refine ⟨⟨x, hxH⟩, fun b => ?_, rfl⟩
    simpa [Subgroup.mem_subgroupOf] using hconj (b : G) b.2

/-- `core_H(D)` への包含判定: `P ≤ H` のとき `P ≤ core_H(D) ⟺ P` のすべての `H`-共役が `D` の中. -/
theorem le_relCore_iff {H D P : Subgroup G} (hPH : P ≤ H) :
    P ≤ relCore H D ↔ ∀ h ∈ H, ∀ x ∈ P, h * x * h⁻¹ ∈ D := by
  constructor
  · intro hle h hh x hx
    exact (mem_relCore_iff.mp (hle hx)).2 h hh
  · intro hconj x hx
    exact mem_relCore_iff.mpr ⟨hPH hx, fun h hh => hconj h hh x hx⟩

/-- `core_H(D)` の最大性: `N ≤ D`, `N ≤ H`, `N` が `H` に normal (`H ≤ N_G(N)`) なら
`N ≤ core_H(D)`. -/
theorem le_relCore {H D N : Subgroup G} (hND : N ≤ D) (hNH : N ≤ H)
    (hNnorm : H ≤ Subgroup.normalizer (N : Set G)) : N ≤ relCore H D := by
  haveI : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hNnorm
  have h1 : N.subgroupOf H ≤ (D.subgroupOf H).normalCore :=
    Subgroup.normal_le_normalCore.mpr (Subgroup.comap_mono hND)
  calc N = (N.subgroupOf H).map H.subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNH]
    _ ≤ relCore H D := Subgroup.map_mono h1

end

section /- 9C: Theorem 9.24 の仮説と N_G 補題 -/

/-- Thm 9.24 の仮説: `D` の非自明部分群は `H` または `K` を真に含むどの部分群にも
normal でない (`N ◁ L` を `L ≤ N_G(N)` で表す). -/
def NoNormalInSupergroup (H K D : Subgroup G) : Prop :=
  ∀ L : Subgroup G, H < L ∨ K < L →
    ∀ N : Subgroup G, N ≠ ⊥ → N ≤ D → ¬ (L ≤ Subgroup.normalizer (N : Set G))

/-- 仮説は `H`, `K` について対称. -/
theorem NoNormalInSupergroup.symm {H K D : Subgroup G} (hyp : NoNormalInSupergroup H K D) :
    NoNormalInSupergroup K H D :=
  fun L hL N hN hND => hyp L hL.symm N hN hND

/-- 仮説から: `N ≤ D` が nonidentity で `H` に normal (`H ≤ N_G(N)`) なら `N_G(N) = H`
(さもなくば `N_G(N) ⊋ H` が仮説に反する). -/
theorem normalizer_eq_left_of_noNormal {H K D : Subgroup G}
    (hyp : NoNormalInSupergroup H K D) {N : Subgroup G} (hN : N ≠ ⊥) (hND : N ≤ D)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup.normalizer (N : Set G) = H := by
  refine le_antisymm ?_ hHN
  by_contra hle
  exact hyp (Subgroup.normalizer (N : Set G))
    (Or.inl (lt_of_le_of_ne hHN fun heq => hle heq.ge)) N hN hND le_rfl

/-- 仮説から (K 版): `N ≤ D` が nonidentity で `K` に normal なら `N_G(N) = K`. -/
theorem normalizer_eq_right_of_noNormal {H K D : Subgroup G}
    (hyp : NoNormalInSupergroup H K D) {N : Subgroup G} (hN : N ≠ ⊥) (hND : N ≤ D)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup.normalizer (N : Set G) = K := by
  refine le_antisymm ?_ hKN
  by_contra hle
  exact hyp (Subgroup.normalizer (N : Set G))
    (Or.inr (lt_of_le_of_ne hKN fun heq => hle heq.ge)) N hN hND le_rfl

end

section /- 9C: Thm 9.24 の記号 (`E`, `U`, `V`) と subnormal chain -/

variable (H K : Subgroup G)

/-- **Thm 9.24 の `E`**: `E = core_H(D) ⊓ core_K(D)` (`D = H ⊓ K`).
書籍の `M = core_H(D)`, `N = core_K(D)` はそれぞれ `relCore H (H ⊓ K)`,
`relCore K (H ⊓ K)`; `U = relCore H (thompsonWielandtCore H K)`,
`V = relCore K (thompsonWielandtCore H K)`. -/
def thompsonWielandtCore : Subgroup G :=
  relCore H (H ⊓ K) ⊓ relCore K (H ⊓ K)

theorem thompsonWielandtCore_comm : thompsonWielandtCore H K = thompsonWielandtCore K H := by
  rw [thompsonWielandtCore, thompsonWielandtCore, inf_comm H K, inf_comm]

/-- `V = core_K(E) ≤ E ≤ M = core_H(D)`: Case 2 の subnormal chain `V ◁ M ◁ H` の包含部分. -/
theorem relCore_thompsonWielandtCore_le_relCore :
    relCore K (thompsonWielandtCore H K) ≤ relCore H (H ⊓ K) :=
  (relCore_le K (thompsonWielandtCore H K)).trans inf_le_left

/-- `M = core_H(D)` は `V = core_K(E)` を正規化する (`M ≤ D ≤ K ≤ N_G(V)`):
Case 2 の subnormal chain `V ◁ M ◁ H` の normality 部分.

⚠ ここが書籍 p. 284 の「`V ◁ M ◁ H`, so `V ◁ H`」の箇所. 実際に得られるのは
`V ◁ M ◁ H` (subnormal) までで `V ◁ H` ではないため, 下流では normal 版でなく
subnormal 版の Cor 9.27 (`le_normalizer_pResidualOf_of_subnormal_two_rel`) を使う. -/
theorem relCore_le_normalizer_relCore_thompsonWielandtCore :
    relCore H (H ⊓ K)
      ≤ Subgroup.normalizer ((relCore K (thompsonWielandtCore H K) : Subgroup G) : Set G) :=
  ((relCore_le H (H ⊓ K)).trans inf_le_right).trans
    (le_normalizer_relCore K (thompsonWielandtCore H K))

theorem thompsonWielandtCore_le : thompsonWielandtCore H K ≤ H ⊓ K :=
  inf_le_left.trans (relCore_le H (H ⊓ K))

/-- `U = core_H(E) ◁ H` ゆえ `X = O^p(U)` も `H` に normal (`O^p` は characteristic). -/
theorem le_normalizer_pResidualOf_relCore (p : ℕ) :
    H ≤ Subgroup.normalizer
        (pResidualOf p (relCore H (thompsonWielandtCore H K)) : Set G) :=
  (le_normalizer_relCore H _).trans (normalizer_le_normalizer_pResidualOf p _)

/-- `X = O^p(U) ≤ U ≤ E ≤ D`. -/
theorem pResidualOf_relCore_le_inf (p : ℕ) :
    pResidualOf p (relCore H (thompsonWielandtCore H K)) ≤ H ⊓ K :=
  (pResidualOf_le p _).trans
    ((relCore_le H (thompsonWielandtCore H K)).trans (thompsonWielandtCore_le H K))

/-- **Thm 9.24 Case 2 の Step B**: `X = O^p(U) ≠ 1` ならば `N_G(X) = H`
(仮説「`D` の非自明部分群は `H` を真に含む部分群に normal でない」から). -/
theorem normalizer_pResidualOf_relCore_eq (p : ℕ)
    (hyp : NoNormalInSupergroup H K (H ⊓ K))
    (hX : pResidualOf p (relCore H (thompsonWielandtCore H K)) ≠ ⊥) :
    Subgroup.normalizer
        (pResidualOf p (relCore H (thompsonWielandtCore H K)) : Set G) = H :=
  normalizer_eq_left_of_noNormal hyp hX (pResidualOf_relCore_le_inf H K p)
    (le_normalizer_pResidualOf_relCore H K p)

/-- **Thm 9.24 Case 2 の Step A** (書籍 p. 284): `P = O_p(H)` は `Y = O^p(V)` を正規化する.

書籍は「`V ◁ H` かつ `P ◁ H` ゆえ Cor 9.27」と述べるが, 実際には `V ◁ M ◁ H` (subnormal)
なので subnormal 版 Cor 9.27 の相対形を `H` を ambient として適用する. -/
theorem opiCoreInG_le_normalizer_pResidualOf_relCore [Finite G] {p : ℕ} [Fact p.Prime] :
    GroupTheory.opiCoreInG ({p} : Set ℕ) H
      ≤ Subgroup.normalizer
          (pResidualOf p (relCore K (thompsonWielandtCore H K)) : Set G) :=
  le_normalizer_pResidualOf_of_subnormal_two_rel
    (relCore_thompsonWielandtCore_le_relCore H K)
    (relCore_le_left H (H ⊓ K))
    (GroupTheory.opiCoreInG_le _ H)
    (le_normalizer_relCore H (H ⊓ K))
    (GroupTheory.le_normalizer_opiCoreInG _ H)
    (relCore_le_normalizer_relCore_thompsonWielandtCore H K)
    (GroupTheory.isPGroup_opiCoreInG_singleton H)

/-- Step B の `K` 版: `Y = O^p(V) ≠ 1` ならば `N_G(Y) = K`. -/
theorem normalizer_pResidualOf_relCore_eq_right (p : ℕ)
    (hyp : NoNormalInSupergroup H K (H ⊓ K))
    (hY : pResidualOf p (relCore K (thompsonWielandtCore H K)) ≠ ⊥) :
    Subgroup.normalizer
        (pResidualOf p (relCore K (thompsonWielandtCore H K)) : Set G) = K := by
  have h := normalizer_pResidualOf_relCore_eq K H p
    (by rw [inf_comm]; exact hyp.symm : NoNormalInSupergroup K H (K ⊓ H))
    (by rwa [thompsonWielandtCore_comm])
  rwa [thompsonWielandtCore_comm] at h

/-- **Thm 9.24 Case 2 の Step C** (書籍 p. 284): `Y = O^p(V) ≠ 1` ならば
`P = O_p(H) ≤ D = H ⊓ K`.

Step A で `P ≤ N_G(Y)`, Step B (K 版) で `N_G(Y) = K`, また `P ≤ H` は自明. -/
theorem opiCoreInG_le_inf [Finite G] {p : ℕ} [Fact p.Prime]
    (hyp : NoNormalInSupergroup H K (H ⊓ K))
    (hY : pResidualOf p (relCore K (thompsonWielandtCore H K)) ≠ ⊥) :
    GroupTheory.opiCoreInG ({p} : Set ℕ) H ≤ H ⊓ K :=
  le_inf (GroupTheory.opiCoreInG_le _ H)
    ((opiCoreInG_le_normalizer_pResidualOf_relCore H K).trans_eq
      (normalizer_pResidualOf_relCore_eq_right H K p hyp hY))

/-- **Thm 9.24 Case 2 の Step D** (書籍 p. 284): 各 `k ∈ K` で `P = O_p(H) ≤ H^k`.

書籍の議論: `U ◁ H` ゆえ `U ◁ N`, よって `U^k ◁ N^k = N ◁ D`. `D` を ambient として
subnormal 版 Cor 9.27 を適用すると `P` は `O^p(U^k) = X^k` を正規化し,
`P ≤ N_G(X^k) = N_G(X)^k = H^k`.

(ここでも `U^k ◁ N ◁ D` は subnormal であって `U^k ◁ D` ではないので, 書籍の
「`U^k ◁ D`」という記述は Step A と同じ jump を含む — subnormal 版で埋める.) -/
theorem opiCoreInG_le_map_conj [Finite G] {p : ℕ} [Fact p.Prime]
    (hyp : NoNormalInSupergroup H K (H ⊓ K))
    (hX : pResidualOf p (relCore H (thompsonWielandtCore H K)) ≠ ⊥)
    (hY : pResidualOf p (relCore K (thompsonWielandtCore H K)) ≠ ⊥)
    {k : G} (hk : k ∈ K) :
    GroupTheory.opiCoreInG ({p} : Set ℕ) H ≤ H.map (MulAut.conj k : G →* G) := by
  set U := relCore H (thompsonWielandtCore H K) with hU
  set N := relCore K (H ⊓ K) with hN
  set P := GroupTheory.opiCoreInG ({p} : Set ℕ) H with hP
  set c := (MulAut.conj k : G →* G) with hc
  -- `N` は `k ∈ K` の共役で不変
  have hNfix : N.map c = N :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_relCore K (H ⊓ K) hk)
  have hUN : U ≤ N := (relCore_le H (thompsonWielandtCore H K)).trans inf_le_right
  have hND : N ≤ H ⊓ K := relCore_le K (H ⊓ K)
  have hNnU : N ≤ Subgroup.normalizer (U : Set G) :=
    (hND.trans inf_le_left).trans (le_normalizer_relCore H (thompsonWielandtCore H K))
  -- `N ≤ N_G(U^k)` (共役で移して `N^k = N`)
  have hNnUk : N ≤ Subgroup.normalizer ((U.map c : Subgroup G) : Set G) :=
    calc N = N.map c := hNfix.symm
      _ ≤ (Subgroup.normalizer (U : Set G)).map c := Subgroup.map_mono hNnU
      _ = Subgroup.normalizer ((U.map c : Subgroup G) : Set G) :=
          map_normalizer_mulEquiv (MulAut.conj k) U
  -- `D` を ambient とする subnormal 版 Cor 9.27
  have key : P ≤ Subgroup.normalizer (pResidualOf p (U.map c) : Set G) :=
    le_normalizer_pResidualOf_of_subnormal_two_rel
      ((Subgroup.map_mono hUN).trans_eq hNfix) hND
      (opiCoreInG_le_inf H K hyp hY)
      (inf_le_right.trans (le_normalizer_relCore K (H ⊓ K)))
      (inf_le_left.trans (GroupTheory.le_normalizer_opiCoreInG _ H))
      hNnUk (GroupTheory.isPGroup_opiCoreInG_singleton H)
  -- `N_G(O^p(U^k)) = N_G(X^k) = N_G(X)^k = H^k`
  rw [← map_pResidualOf (MulAut.conj k) U,
    ← map_normalizer_mulEquiv (MulAut.conj k) (pResidualOf p U),
    normalizer_pResidualOf_relCore_eq H K p hyp hX] at key
  exact key

/-- **Thm 9.24 Case 2 の Step E** (書籍 p. 284): `P = O_p(H) ≤ core_K(D) = N`.

Step D の `P ≤ H^k` (∀ `k ∈ K`) と `P ≤ K` から `P ≤ D^k` (∀ `k`), これは
`le_relCore_iff` により `P ≤ core_K(D)` に他ならない. -/
theorem opiCoreInG_le_relCore_right [Finite G] {p : ℕ} [Fact p.Prime]
    (hyp : NoNormalInSupergroup H K (H ⊓ K))
    (hX : pResidualOf p (relCore H (thompsonWielandtCore H K)) ≠ ⊥)
    (hY : pResidualOf p (relCore K (thompsonWielandtCore H K)) ≠ ⊥) :
    GroupTheory.opiCoreInG ({p} : Set ℕ) H ≤ relCore K (H ⊓ K) := by
  have hPK : GroupTheory.opiCoreInG ({p} : Set ℕ) H ≤ K :=
    (opiCoreInG_le_inf H K hyp hY).trans inf_le_right
  rw [le_relCore_iff hPK]
  intro g hg x hx
  refine ⟨?_, K.mul_mem (K.mul_mem hg (hPK hx)) (K.inv_mem hg)⟩
  -- `H` 成分: Step D を `k := g⁻¹` で使うと `x ∈ H^{g⁻¹}`, すなわち `g * x * g⁻¹ ∈ H`
  obtain ⟨y, hy, hxy⟩ := opiCoreInG_le_map_conj H K hyp hX hY (K.inv_mem hg) hx
  have hxy' : g⁻¹ * y * g = x := by simpa using hxy
  have hgx : g * x * g⁻¹ = y := by rw [← hxy']; group
  rw [hgx]
  exact hy

/-- **Thm 9.24 Case 2 の Step F** (書籍 p. 284): `O_p(H) ≤ O_p(K)`.

Step E で `P = O_p(H) ≤ N = core_K(D)`; `N ≤ D ≤ H ≤ N_G(P)` ゆえ `P ◁ N`, よって
`P ≤ O_p(N)`. さらに `N ◁ K` ゆえ `O_p(N) ◁ K` で `O_p(N) ≤ O_p(K)`. -/
theorem opiCoreInG_le_opiCoreInG [Finite G] {p : ℕ} [Fact p.Prime]
    (hyp : NoNormalInSupergroup H K (H ⊓ K))
    (hX : pResidualOf p (relCore H (thompsonWielandtCore H K)) ≠ ⊥)
    (hY : pResidualOf p (relCore K (thompsonWielandtCore H K)) ≠ ⊥) :
    GroupTheory.opiCoreInG ({p} : Set ℕ) H ≤ GroupTheory.opiCoreInG ({p} : Set ℕ) K := by
  set P := GroupTheory.opiCoreInG ({p} : Set ℕ) H with hPdef
  set N := relCore K (H ⊓ K) with hNdef
  have hPN : P ≤ N := opiCoreInG_le_relCore_right H K hyp hX hY
  have hND : N ≤ H ⊓ K := relCore_le K (H ⊓ K)
  have hNnP : N ≤ Subgroup.normalizer (P : Set G) :=
    (hND.trans inf_le_left).trans (GroupTheory.le_normalizer_opiCoreInG _ H)
  -- `P ◁ N` ゆえ `P ≤ O_p(N)`
  have h1 : P ≤ GroupTheory.opiCoreInG ({p} : Set ℕ) N :=
    GroupTheory.le_opiCoreInG_of_normal_of_isPiSubgroup hPN
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hPN).mpr hNnP)
      (GroupTheory.isPiSubgroup_opiCoreInG _ H)
  -- `N ◁ K` ゆえ `O_p(N) ◁ K`, よって `O_p(N) ≤ O_p(K)`
  have hONK : GroupTheory.opiCoreInG ({p} : Set ℕ) N ≤ K :=
    (GroupTheory.opiCoreInG_le _ _).trans (hND.trans inf_le_right)
  have h2 : GroupTheory.opiCoreInG ({p} : Set ℕ) N
      ≤ GroupTheory.opiCoreInG ({p} : Set ℕ) K :=
    GroupTheory.le_opiCoreInG_of_normal_of_isPiSubgroup hONK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hONK).mpr
        (GroupTheory.le_normalizer_opiCoreInG_of_le_normalizer _
          (le_normalizer_relCore K (H ⊓ K))))
      (GroupTheory.isPiSubgroup_opiCoreInG _ _)
  exact h1.trans h2

/-- **Thm 9.24 の Case 2** (書籍 p. 284): ある素数 `p` で `O_p(H) ≠ 1` (すなわち `F(H) > 1`)
ならば `O^p(U) = 1` または `O^p(V) = 1`, つまり `U` または `V` が `p`-群.

証明: `X = O^p(U) ≠ 1` かつ `Y = O^p(V) ≠ 1` と仮定する. Step F とその `H`/`K` 対称版から
`O_p(H) ≤ O_p(K) ≤ O_p(H)` すなわち `P := O_p(H) = O_p(K)`. Step C より `P ≤ D` で,
`P` は `H` にも `K` にも normal, かつ `P ≠ 1` なので仮説から `H = N_G(P) = K` となり
`H ≠ K` に矛盾. -/
theorem pResidualOf_relCore_eq_bot_or [Finite G] {p : ℕ} [Fact p.Prime]
    (hHK : H ≠ K) (hyp : NoNormalInSupergroup H K (H ⊓ K))
    (hP : GroupTheory.opiCoreInG ({p} : Set ℕ) H ≠ ⊥) :
    pResidualOf p (relCore H (thompsonWielandtCore H K)) = ⊥ ∨
      pResidualOf p (relCore K (thompsonWielandtCore H K)) = ⊥ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hX, hY⟩ := hcon
  -- `H`/`K` を入れ替えた仮説
  have hyp' : NoNormalInSupergroup K H (K ⊓ H) := by rw [inf_comm]; exact hyp.symm
  have hX' : pResidualOf p (relCore K (thompsonWielandtCore K H)) ≠ ⊥ := by
    rw [thompsonWielandtCore_comm K H]; exact hY
  have hY' : pResidualOf p (relCore H (thompsonWielandtCore K H)) ≠ ⊥ := by
    rw [thompsonWielandtCore_comm K H]; exact hX
  -- Step F を両向きに使って `O_p(H) = O_p(K)`
  have heq : GroupTheory.opiCoreInG ({p} : Set ℕ) H
      = GroupTheory.opiCoreInG ({p} : Set ℕ) K :=
    le_antisymm (opiCoreInG_le_opiCoreInG H K hyp hX hY)
      (opiCoreInG_le_opiCoreInG K H hyp' hX' hY')
  -- `P ≤ D` かつ `H`, `K` の両方に normal ゆえ `H = N_G(P) = K`
  have hPD : GroupTheory.opiCoreInG ({p} : Set ℕ) H ≤ H ⊓ K := opiCoreInG_le_inf H K hyp hY
  have hKn : K ≤ Subgroup.normalizer
      ((GroupTheory.opiCoreInG ({p} : Set ℕ) H : Subgroup G) : Set G) := by
    rw [heq]; exact GroupTheory.le_normalizer_opiCoreInG _ K
  have hH := normalizer_eq_left_of_noNormal hyp hP hPD
    (GroupTheory.le_normalizer_opiCoreInG _ H)
  exact hHK (hH.symm.trans (normalizer_eq_right_of_noNormal hyp hP hPD hKn))

end

section /- 9C: Case 1 の道具 — Cor 9.18 の相対形 -/

/-- **Isaacs Corollary 9.18 の相対形 (subnormal defect 2)**: `S ≤ T ≤ H` で `T` が `H` に,
`S` が `T` に normal ならば `E(H) ≤ N_G(S^∞)`.

Thm 9.24 Case 1 で `H` を ambient, `T = core_H(D) = M`, `S = core_K(E) = V` として使う.
Case 2 の 9.27 と違い 9.18 は**元々 subnormal 版**なので, `V ◁ M ◁ H` から
`↥H` 内の subnormal 性を組めばそのまま通る (書籍の `V ◁ H` は不要). -/
theorem layerInG_le_normalizer_nilpotentResidual_of_subnormal_two [Finite G]
    {H S T : Subgroup G} (hST : S ≤ T) (hTH : T ≤ H)
    (hTn : H ≤ Subgroup.normalizer (T : Set G))
    (hSn : T ≤ Subgroup.normalizer (S : Set G)) :
    layerInG H ≤ Subgroup.normalizer (nilpotentResidual S : Set G) := by
  have hSH : S ≤ H := hST.trans hTH
  haveI hT' : (T.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTH).mpr hTn
  have hnorm : ((S.subgroupOf H).subgroupOf (T.subgroupOf H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.comap_mono hST)).mpr
      (subgroupOf_le_normalizer_subgroupOf hSn)
  have hsub : (S.subgroupOf H).IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ (Subgroup.comap_mono hST) hT'.isSubnormal hnorm
  have hlift := map_subtype_le_normalizer_map_subtype
    (layer_le_normalizer_nilpotentResidual (G := ↥H) hsub)
  rwa [map_subtype_nilpotentResidual_subgroupOf hSH] at hlift

/-- `F(H) = 1` のとき `H` に normal な非自明部分群 `U ≤ H` は nilpotent でない,
すなわち `U^∞ ≠ 1`.

(`U` が nilpotent なら `U ◁ H` より `U ≤ F(H) = 1` で矛盾.) -/
theorem nilpotentResidual_ne_bot_of_fitting_eq_bot [Finite G] {H U : Subgroup G}
    (hF : Ch01.fitting ↥H = ⊥) (hUH : U ≤ H)
    (hUn : H ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    nilpotentResidual U ≠ ⊥ := by
  intro hres
  haveI : (U.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr hUn
  haveI : Group.IsNilpotent ↥U := nilpotentResidual_eq_bot_iff.mp hres
  have hnil : Group.IsNilpotent ↥(U.subgroupOf H) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hUH).symm
  have hle : U.subgroupOf H ≤ Ch01.fitting ↥H :=
    (Ch02.le_fitting_iff_isNilpotent_and_isSubnormal _).mpr
      ⟨hnil, ‹(U.subgroupOf H).Normal›.isSubnormal⟩
  rw [hF, le_bot_iff, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hUH] at hle
  exact hU hle

end

section /- 9C: Thm 9.24 の Case 1 (`F(H) = F(K) = 1`) -/

variable (H K : Subgroup G)

/-- Case 1 の片側ステップ: `F(H)=1` で `V ≠ 1` ならば `E(H) ≤ D`.

`V ◁ M ◁ H` に 9.18 の相対形を当てて `E(H) ≤ N_G(V^∞)`; 仮説から `N_G(V^∞) = K` なので
`E(H) ≤ K`, さらに `E(H) ≤ H` と合わせて `E(H) ≤ D`. -/
theorem layerInG_le_inf_of_fitting_eq_bot [Finite G]
    (hyp : NoNormalInSupergroup H K (H ⊓ K))
    (hFK : Ch01.fitting ↥K = ⊥)
    (hV : relCore K (thompsonWielandtCore H K) ≠ ⊥) :
    layerInG H ≤ H ⊓ K := by
  set V := relCore K (thompsonWielandtCore H K) with hVdef
  have hVK : V ≤ K := relCore_le_left K _
  have hVn : K ≤ Subgroup.normalizer (V : Set G) := le_normalizer_relCore K _
  have hVres : nilpotentResidual V ≠ ⊥ :=
    nilpotentResidual_ne_bot_of_fitting_eq_bot hFK hVK hVn hV
  have hVresD : nilpotentResidual V ≤ H ⊓ K :=
    (nilpotentResidual_le V).trans
      ((relCore_le K (thompsonWielandtCore H K)).trans (thompsonWielandtCore_le H K))
  have hKres : Subgroup.normalizer (nilpotentResidual V : Set G) = K :=
    normalizer_eq_right_of_noNormal hyp hVres hVresD
      (hVn.trans (normalizer_le_normalizer_nilpotentResidual V))
  refine le_inf (layerInG_le H) ?_
  -- 9.18 の相対形 (`V ◁ M ◁ H`)
  exact (layerInG_le_normalizer_nilpotentResidual_of_subnormal_two
    (relCore_thompsonWielandtCore_le_relCore H K)
    (relCore_le_left H (H ⊓ K))
    (le_normalizer_relCore H (H ⊓ K))
    (relCore_le_normalizer_relCore_thompsonWielandtCore H K)).trans_eq hKres

/-- **Thm 9.24 の Case 1** (書籍 p. 284): `F(H) = F(K) = 1` ならば `U = 1` または `V = 1`
(特に `U` または `V` は任意の素数について `p`-群).

証明: `U ≠ 1` かつ `V ≠ 1` と仮定する. `F(H)=F(K)=1` より `U`, `V` は nilpotent でなく
`U^∞`, `V^∞` は `D` の非自明部分群で `H`, `K` にそれぞれ normal, よって
`N_G(U^∞) = H`, `N_G(V^∞) = K`. 9.18 (相対形) から `E(H) ≤ N_G(V^∞) = K`, つまり
`E(H) ≤ D`; 9.25 (ambient 版) で `E(D) = E(H)`. 同様に `E(D) = E(K)`. よって
`E(H) = E(K)` は `D` の非自明部分群で `H` にも `K` にも normal となり,
仮説から `H = N_G(E(H)) = K` で `H ≠ K` に矛盾. -/
theorem relCore_eq_bot_or_of_fitting_eq_bot [Finite G]
    (hHK : H ≠ K) (hyp : NoNormalInSupergroup H K (H ⊓ K))
    (hFH : Ch01.fitting ↥H = ⊥) (hFK : Ch01.fitting ↥K = ⊥) :
    relCore H (thompsonWielandtCore H K) = ⊥ ∨
      relCore K (thompsonWielandtCore H K) = ⊥ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hU, hV⟩ := hcon
  -- `H`/`K` を入れ替えた仮説
  have hyp' : NoNormalInSupergroup K H (K ⊓ H) := by rw [inf_comm]; exact hyp.symm
  have hU' : relCore H (thompsonWielandtCore K H) ≠ ⊥ := by
    rw [thompsonWielandtCore_comm K H]; exact hU
  -- `E(H) ≤ D` と `E(K) ≤ D`
  have hEH : layerInG H ≤ H ⊓ K := layerInG_le_inf_of_fitting_eq_bot H K hyp hFK hV
  have hEK : layerInG K ≤ H ⊓ K := by
    have := layerInG_le_inf_of_fitting_eq_bot K H hyp' hFH hU'
    rwa [inf_comm] at this
  -- 9.25 (ambient 版) で `E(D) = E(H)` かつ `E(D) = E(K)`
  have hDH : layerInG (H ⊓ K) = layerInG H :=
    layerInG_eq_of_fitting_eq_bot hFH inf_le_left hEH
  have hDK : layerInG (H ⊓ K) = layerInG K :=
    layerInG_eq_of_fitting_eq_bot hFK inf_le_right hEK
  have hEeq : layerInG H = layerInG K := hDH.symm.trans hDK
  -- `E(H) ≠ 1`
  haveI : Nontrivial ↥H := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hHbot
    exact hU (le_bot_iff.mp ((relCore_le_left H _).trans hHbot.le))
  have hLne : layerInG H ≠ ⊥ := by
    rw [layerInG, Ne, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective]
    exact layer_ne_bot_of_fitting_eq_bot hFH
  -- `E(H)` は `H` にも `K` にも normal ゆえ `H = N_G(E(H)) = K`
  have hHn : H ≤ Subgroup.normalizer (layerInG H : Set G) :=
    le_normalizer_map_subtype_of_normal (inferInstance : (layer ↥H).Normal)
  have hKn : K ≤ Subgroup.normalizer (layerInG H : Set G) := by
    rw [hEeq]
    exact le_normalizer_map_subtype_of_normal (inferInstance : (layer ↥K).Normal)
  exact hHK ((normalizer_eq_left_of_noNormal hyp hLne hEH hHn).symm.trans
    (normalizer_eq_right_of_noNormal hyp hLne hEH hKn))

end

section /- 9C: Thm 9.23 準備 — n!-定理の相対形 -/

/-- **n!-定理の相対形**: `D ≤ H` のとき `|H : core_H(D)|` は `|H : D|!` を割る.

`Ch01.normalCore_index_dvd_factorial` を `↥H` の中の `D.subgroupOf H` に適用しただけ.
Thm 9.23 の index bound (`|H:M| ≤ a!`, `|H:U| ≤ (a!b!)!`) で使う. -/
theorem relCore_relIndex_dvd_factorial [Finite G] (H D : Subgroup G) :
    (relCore H D).relIndex H ∣ Nat.factorial (D.relIndex H) := by
  have hsub : (relCore H D).subgroupOf H = (D.subgroupOf H).normalCore :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have h := (Ch01.normalCore_index_dvd_factorial (D.subgroupOf H)).2.2
  rwa [← hsub] at h

/-- 相対 index 版の不等式形 (`|H : core_H(D)| ≤ |H : D|!`). -/
theorem relCore_relIndex_le_factorial [Finite G] (H D : Subgroup G) :
    (relCore H D).relIndex H ≤ Nat.factorial (D.relIndex H) :=
  Nat.le_of_dvd (Nat.factorial_pos _) (relCore_relIndex_dvd_factorial H D)

end

section /- 9C: Theorem 9.24 本体 -/

variable (H K : Subgroup G)

/-- `F(H) ≠ 1` ならばある素数 `p` で `O_p(H) ≠ 1`
(`F = ⨆_{p ∈ pf} O_p` ゆえ, すべての `O_p` が自明なら `F` も自明). -/
theorem exists_prime_opiCoreInG_ne_bot [Finite G] {H : Subgroup G}
    (hF : Ch01.fitting ↥H ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ GroupTheory.opiCoreInG ({p} : Set ℕ) H ≠ ⊥ := by
  by_contra hcon
  push_neg at hcon
  refine hF ?_
  rw [Ch01.fitting_eq_iSup_primeFactors]
  refine iSup_eq_bot.mpr fun p => ?_
  haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  have h := hcon (p : ℕ) (Nat.prime_of_mem_primeFactors p.2)
  rw [GroupTheory.opiCoreInG, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at h
  rwa [← Ch04.oPiCore_singleton_eq_opCore]

/-- **Isaacs Theorem 9.24** (Thompson–Wielandt の一般形; p. 283).

相異なる部分群 `H`, `K` について `D = H ⊓ K` とし,「`D` の非自明部分群は `H` または `K` を
真に含むどの部分群にも normal でない」(`NoNormalInSupergroup`) を仮定する.
`E = core_H(D) ⊓ core_K(D)` (`thompsonWielandtCore`), `U = core_H(E)`, `V = core_K(E)`
とおくと, **ある素数 `p` で `U` または `V` が `p`-群**.

証明は書籍 p. 284 の 2 ケース:
* `F(H) = F(K) = 1` (`relCore_eq_bot_or_of_fitting_eq_bot`): `U` または `V` が自明.
* さもなくば (対称性より `F(H) > 1` として) ある `p` で `O_p(H) > 1`
  (`pResidualOf_relCore_eq_bot_or`): `O^p(U) = 1` または `O^p(V) = 1`, すなわち
  `U` または `V` が `p`-群. -/
theorem thompsonWielandt [Finite G] (hHK : H ≠ K)
    (hyp : NoNormalInSupergroup H K (H ⊓ K)) :
    ∃ p : ℕ, p.Prime ∧
      (IsPGroup p ↥(relCore H (thompsonWielandtCore H K)) ∨
        IsPGroup p ↥(relCore K (thompsonWielandtCore H K))) := by
  by_cases hFH : Ch01.fitting ↥H = ⊥
  · by_cases hFK : Ch01.fitting ↥K = ⊥
    · -- Case 1: `F(H) = F(K) = 1` — `U` か `V` が自明 (任意の素数で `p`-群)
      refine ⟨2, Nat.prime_two, ?_⟩
      rcases relCore_eq_bot_or_of_fitting_eq_bot H K hHK hyp hFH hFK with h | h
      · exact Or.inl (by rw [h]; exact IsPGroup.of_bot)
      · exact Or.inr (by rw [h]; exact IsPGroup.of_bot)
    · -- Case 2 (`F(K) > 1`): `H`, `K` を入れ替えて適用
      obtain ⟨p, hp, hPK⟩ := exists_prime_opiCoreInG_ne_bot hFK
      haveI : Fact p.Prime := ⟨hp⟩
      have hyp' : NoNormalInSupergroup K H (K ⊓ H) := by rw [inf_comm]; exact hyp.symm
      rcases pResidualOf_relCore_eq_bot_or K H (Ne.symm hHK) hyp' hPK with h | h
      · exact ⟨p, hp, Or.inr (by
          rw [thompsonWielandtCore_comm H K]; exact (pResidualOf_eq_bot_iff_isPGroup _).mp h)⟩
      · exact ⟨p, hp, Or.inl (by
          rw [thompsonWielandtCore_comm H K]; exact (pResidualOf_eq_bot_iff_isPGroup _).mp h)⟩
  · -- Case 2 (`F(H) > 1`)
    obtain ⟨p, hp, hPH⟩ := exists_prime_opiCoreInG_ne_bot hFH
    haveI : Fact p.Prime := ⟨hp⟩
    rcases pResidualOf_relCore_eq_bot_or H K hHK hyp hPH with h | h
    · exact ⟨p, hp, Or.inl ((pResidualOf_eq_bot_iff_isPGroup _).mp h)⟩
    · exact ⟨p, hp, Or.inr ((pResidualOf_eq_bot_iff_isPGroup _).mp h)⟩

end

end OddOrder.Isaacs.Ch09
