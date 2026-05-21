/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Sylow

/-!
# OddOrder.Isaacs.Ch01 — Sylow Theory

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 1
"Sylow Theory" (pp. 1-44) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 1A | 群作用と Fundamental Counting Principle | 1.1 – 1.6 | 着手中 |
| 1B | Sylow の存在定理 (Sylow E), Cauchy | 1.7 – 1.10 | TODO |
| 1C | Sylow の共役 (Sylow C / D), Frattini argument | 1.11 – 1.18 | TODO |
| 1D | 冪零群, Fitting 部分群 `F(G)` | 1.19 – 1.29 | TODO |
| 1E | 位数 \|G\|=2n (n 奇) の指数 2 正規部分群 など | 1.30 – 1.36 | TODO |
| 1F | Brodkey の定理 (Sylow が abelian の場合) | 1.37 – 1.40 | TODO |
| 1G | Chermak–Delgado | 1.41 – 1.46 | TODO |

## 方針

mathlib 既存資産 (`Sylow`, `MulAction.orbitEquivQuotientStabilizer`,
`Subgroup.normalCore`, `Subgroup.normalCore_eq_ker`) を最大限再利用し、
Isaacs の流儀で主張を再述する薄いラッパーを与える。

主要な新規実装ターゲット (mathlib 未収載):

* **§1D Thm 1.28**: Fitting 部分群 `Fit(G)` の定義 + 「最大冪零正規部分群である」
  ことの証明 (Phase 1 の最初の本格的な新規実装)

ノート: [notes/isaacs/ch01_sylow.md](../../notes/isaacs/ch01_sylow.md)
-/

namespace OddOrder.Isaacs.Ch01

section /- 1A: Group actions and the Fundamental Counting Principle (pp. 1-10) -/

variable {G : Type*} [Group G]

/-- **Isaacs Thm 1.1**.  部分群 `H ≤ G` の coset 集合 `G ⧸ H` への右乗法作用の
permutation 表現 `G → Sym(G ⧸ H)` の核は `core_G(H) = H.normalCore` に一致する。
従って `G / core_G(H)` は `Sym(G ⧸ H)` の部分群と同型 (第一同型定理).

mathlib `Subgroup.normalCore_eq_ker` の再述. -/
theorem normalCore_eq_perm_ker (H : Subgroup G) :
    H.normalCore = (MulAction.toPermHom G (G ⧸ H)).ker :=
  H.normalCore_eq_ker

/-- **Isaacs Thm 1.4** (Fundamental Counting Principle).  `G` が `Ω` に作用し
`α ∈ Ω` の軌道 `O` と固定部分群 `H = G_α` を取ると, `O ≃ G ⧸ H`
(orbit-stabilizer theorem の "全単射" 部分).

mathlib `MulAction.orbitEquivQuotientStabilizer` の Isaacs 流再述. -/
noncomputable def fundamentalCountingEquiv
    {Ω : Type*} [MulAction G Ω] (α : Ω) :
    MulAction.orbit G α ≃ G ⧸ MulAction.stabilizer G α :=
  MulAction.orbitEquivQuotientStabilizer G α

-- TODO Cor 1.2  指数 [G:H]=n の H は正規部分群 N≤H で [G:N] ∣ n! を含む.
--   N := H.normalCore を取って perm action 経由で示す.
-- TODO Cor 1.3  G simple ∧ ∃ H, [G:H]=n>1  ⇒  |G| ∣ n!.   (Cor 1.2 の系)
-- TODO Cor 1.5  有限 G, x ∈ G の共役類サイズ = [G : C_G(x)].
--   mathlib `ConjClasses.card_carrier` + ConjAct.
-- TODO Cor 1.6  有限 G の部分群 H の共役の総数 = [G : N_G(H)].
--   ConjAct G の H への作用で stabilizer = normalizer から FCP.

end -- 1A

section /- 1B: Sylow's existence theorem and Cauchy (pp. 10–?) -/

-- TODO Thm 1.7  (Sylow E)   : mathlib `Sylow.nonempty` のラッパー.
-- TODO Lemma 1.8            : 二項係数の p 進的補題  (Sylow E の証明用).
-- TODO Cor 1.9   (Cauchy)   : `exists_prime_orderOf_dvd_card` 等のラッパー.
-- TODO Lemma 1.10           : N ◁ G の特性部分群は G 正規.

end -- 1B

section /- 1C: Sylow C / D, Frattini argument (pp. ?–?) -/

-- TODO Thm 1.11  : 任意 p-部分群は Sylow p-部分群の共役に含まれる.
-- TODO Thm 1.12  (Sylow C)  : Sylow p-部分群は互いに共役  (`Sylow.orbit_eq_top`).
-- TODO Lemma 1.13 (Frattini): N ◁ G, P ∈ Syl_p(N) ⇒ G = N_G(P) N.
-- TODO Thm 1.14  (Sylow D)  : 任意 p-部分群は Sylow p-部分群に含まれる.
-- TODO Cor 1.15            : n_p(G) = [G : N_G(S)]  (S ∈ Syl_p).
-- TODO Thm 1.16            : n_p ≡ 1 (mod |S:S∩T|), S,T で |S∩T| 最大.
-- TODO Cor 1.17            : n_p(G) ≡ 1 (mod p).   `card_sylow_modEq_one`.
-- TODO Lemma 1.18          : P ∈ Syl_p, Q ≤ N_G(P) p-部分群 ⇒ Q ⊆ P.

end -- 1C

section /- 1D: Nilpotent groups, Fitting subgroup F(G) (pp. ?–?) -/

-- TODO Thm 1.19    : N ◁ P (P p-群) 非自明 ⇒ N ∩ Z(P) > 1.
-- TODO Lemma 1.20  : 有限 G が冪零であることの諸特性化.
-- TODO Thm 1.21    : 冪零群の中心列の存在/性質.   `Group.IsNilpotent`.
-- TODO Thm 1.22    : 冪零で H < G ⇒ N_G(H) > H.
-- TODO Lemma 1.23  : p-群 P, N < M ◁ P ⇒ ∃ L ◁ P, N ⊆ L ⊆ M, |L:N|=p.
-- TODO Cor 1.24    : 位数 p^a の p-群は各 b ≤ a で正規部分群 |L|=p^b を持つ.
-- TODO Cor 1.25    : 有限 G, p^b ∣ |G| ⇒ 位数 p^b の部分群存在.
-- TODO Thm 1.26    : G 冪零 ⇔ すべての Sylow が正規.
-- TODO Lemma 1.27  : 互いに素な位数を持つ有限正規部分群族の積は直積.
-- TODO **Def F(G)**: Fitting 部分群 — 全冪零正規部分群の積として定義  (新規実装).
-- TODO Cor 1.28    : F(G) 正規かつ冪零, 最大の正規冪零部分群.  (新規実装主結果)
-- TODO Cor 1.29    : 冪零正規部分群 K, L ⇒ KL も冪零.

end -- 1D

section /- 1E: Small-order groups, normal subgroup of index 2 (pp. ?–?) -/

-- TODO Thm 1.30  : |G|=pq (q<p 素) ⇒ Sylow p 正規; q ∤ p−1 なら G 巡回.
-- TODO Thm 1.31  : |G|=p²q ⇒ Sylow p または q が正規.
-- TODO Thm 1.32  : |G|=p³q ⇒ 同上 (例外 |G|=24).
-- TODO Thm 1.33  : |G|=24 ∧ n_2,n_3>1 ⇒ G ≅ S_4.
-- TODO Lemma 1.34: G が有限集合に作用, "奇に作用" 元 ⇒ 指数 2 正規部分群存在.
-- TODO **Thm 1.35**: |G|=2n (n 奇) ⇒ 指数 2 正規部分群存在.
--   (Feit-Thompson の最易特殊 case.)
-- TODO Thm 1.36  : |G|=p^a q ⇒ 単純でない.

end -- 1E

section /- 1F: Brodkey's theorem on abelian Sylow (pp. ?–?) -/

-- TODO Thm 1.37 (Brodkey): G の Sylow p abelian ⇒ ∃ S, T ∈ Syl_p, S∩T = O_p(G).
-- TODO Thm 1.38  : 任意有限 G で S∩T 最小化を取ると O_p(G) 最大.
-- TODO Cor 1.39  : abelian Sylow ⇒ [G : O_p(G)] ≤ [G : P]².
-- TODO Cor 1.40  : abelian Sylow, |P| > |G|^{1/2} ⇒ O_p(G)>1.

end -- 1F

section /- 1G: Chermak–Delgado (pp. ?–?) -/

-- TODO Thm 1.41 (Chermak–Delgado):
--   G 有限 ⇒ 特性的 abelian N, [G:N] ≤ [G:A]² for all abelian A.
-- TODO Lemma 1.42 : m_G(H) ≤ m_G(C_G(H)); 等号 ⇔ H = C_G(C_G(H)).
-- TODO Lemma 1.43 : H, K ⊆ G, D = H∩K, J = ⟨H,K⟩ で m の不等式.
-- TODO Thm 1.44   : Chermak-Delgado measure 最大の部分群族 L(G) の格子構造.
-- TODO Cor 1.45   : L(G) には最小元 M (abelian, M ⊇ Z(G)).
-- TODO Cor 1.46   : |H|·|C_G(H)| > |G| ⇒ G は非可換単純群でない.

end -- 1G

end OddOrder.Isaacs.Ch01
