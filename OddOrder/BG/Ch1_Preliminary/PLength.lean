/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Main

/-!
# `p`-length one

Bender–Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
§5 (mmd L1943): *"a group `G` has `p`-length one if `G = O_{p',p,p'}(G)`."*

This predicate is a shared BG hypothesis used in §5 (Thm 5.6), §6 (Lem 6.6 / Thm 6.7) and
§10. It is placed in a `BG/Ch1_Preliminary` helper file (not the low-level `GroupTheory`
namespace) because it is defined through `OddOrder.Isaacs.Ch03.oPiPrimePiCore` (`O_{π',π}`),
and the `GroupTheory` layer sits *below* `Isaacs`.

## Encoding

`G = O_{p',p,p'}(G)` is equivalent to *`G / O_{p',p}(G)` is a `p'`-group*: since
`O_{p',p,p'}(G)/O_{p',p}(G) = O_{p'}(G/O_{p',p}(G))` and a group equals its own `O_{p'}` iff
it is a `p'`-group. So we encode it directly as `p ∤ |G / O_{p',p}(G)|`.
-/

namespace OddOrder.BG.Ch1

open OddOrder.Isaacs

/-- **BG "`G` has `p`-length one"** (§5, mmd L1943): `G = O_{p',p,p'}(G)`, encoded as the
quotient `G / O_{p',p}(G)` being a `p'`-group (`p ∤ |G / O_{p',p}(G)|`). -/
def hasPLengthOne (p : ℕ) (G : Type*) [Group G] : Prop :=
  ¬ p ∣ Nat.card (G ⧸ Ch03.oPiPrimePiCore {p} G)

/-- `G` has `p`-length one iff `G / O_{p',p}(G)` is a `p'`-group (definitional unfolding). -/
theorem hasPLengthOne_iff (p : ℕ) (G : Type*) [Group G] :
    hasPLengthOne p G ↔ ¬ p ∣ Nat.card (G ⧸ Ch03.oPiPrimePiCore {p} G) :=
  Iff.rfl

end OddOrder.BG.Ch1
