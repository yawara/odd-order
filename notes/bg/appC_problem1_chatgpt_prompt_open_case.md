# ChatGPT Work (GPT-5.6 Sol / ウルトラ) 投入プロンプト — 残る未解決ケース専用 (2026-08-10)

前回 (`appC_problem1_chatgpt_prompt.md`) の投入後にこちらで大きく前進したので、**残った 1 ケースだけ**に
絞って再投入する。以下が本文 (backtick / ドル波括弧 / バックスラッシュを含めない)。

---

OPEN PROBLEM (Glauberman-Norton 1993, "Problem (Peterfalvi)"; Bender-Glauberman, Local Analysis for
the Odd Order Theorem, Appendix C, p.152, Problem 1). I have already reduced it to ONE remaining
case and I want that case settled. Everything below marked PROVED has been verified by me and
formalized in Lean 4 (axiom-clean), so you may use it freely as an input.

SETTING.
Let q be an odd prime, F = GF(3^q), Q0 = 3^q, n = (Q0 - 1)/2.
Let P = (F, +), elementary abelian of order 3^q.
Let U = {u in F^x : u^n = 1} = the group of nonzero squares of F = the norm-one subgroup of F over
GF(3); U is cyclic of order n and acts on P by multiplication, fixed-point-freely.
Let H = P semidirect U, a Frobenius group of order 3^q times n, with kernel P and complement U.
Let P0 = GF(3).1, the prime-field line inside P, of order 3, and let x = 1 in P be a generator of P0.

HYPOTHESIS (B) (the hypothesis of Proposition 9 of Glauberman-Norton, for p = 3):
there exist a group G, an injective homomorphism sigma from H into G, a FINITE abelian 3-prime
subgroup Q of G (3-prime means 3 does not divide |Q|), and an element y of Q, such that
sigma(P0) normalizes Q, and sigma(P0)^y normalizes sigma(U).
IMPORTANT: G is NOT assumed finite. Only Q is required to be finite. So completions of infinite
amalgams are legitimate candidates.

QUESTION (the 1993 problem): can (B) be satisfied for p = 3?
For p = 2 it can: SL(2, 2^q) and Sz(2^q) are witnesses (Examples 10, 11 of the paper).

NOTATION. Write x for sigma(1) (an element of order 3), g = y^{-1} x y (so that the subgroup
sigma(P0)^y = <g>), and c = x^{-1} g = [x, y], which lies in Q. Conjugation is a^b = b^{-1} a b.
I identify H with sigma(H) and write P, U for sigma(P), sigma(U).

WHAT IS ALREADY PROVED (by me; all of this is formalized and machine-checked):

(1) c = [x, y] lies in Q, hence c is a 3-prime element; Q is abelian and x normalizes Q, so
    c and c^x commute.

(2) Word identity: if x^3 = g^3 = 1 and c = x^{-1} g, then [c, c^x] = (g x)^3. With (1) this gives
    (g x)^3 = 1, equivalently x^{g^2} . x^g . x = 1. This is the ONLY nontrivial relation that (B)
    yields, and everything below is built from it.

(3) Since g normalizes U (cyclic of order n) and g^3 = 1, there is an integer e with e^3 = 1 mod n
    and g u g^{-1} = u^e for every u in U.

(4) Conjugating (2) by v in U gives the relation family, for every v in U:
        R(v):    (x^{v^{e^2}})^{g^2} . (x^{v^e})^g . x^v = 1.
    Under the identification of P with (F, +), the U-orbit of x is exactly U (the set of squares),
    and x^v corresponds to the field element v^{-1}.

(5) THEOREM 1 (PROVED, no computer, valid for every q and every G, finite or not).
    If e lies in <3> modulo n (that is, u -> u^e is a power of the Frobenius on U), then (B) fails.
    Proof sketch: for e = 3^j the map s -> s^e is GF(3)-linear, so the three relations R(s), R(t),
    R(s+t) have the same layer structure and cancel to give [x, (s^e)^g] = 1 whenever s, s+1 are
    both squares; the set T = {s in F : s and s+1 are both nonzero squares} spans F over GF(3)
    (elementary: T is disjoint from -T because -1 is a non-square, and |T| = (3^q - 3)/4, so the
    span has more than |F|/3 elements); hence [x, x^g] = 1, which forces c^3 = 1, hence c = 1
    because c is a 3-prime element, hence g = x; but x does not normalize U since H is Frobenius
    with N_H(U) = U. Contradiction.
    Consequences: q = 3 is completely settled (the cube roots of 1 mod 13 are 1, 3, 9, all in <3>),
    and every q with 3 not dividing phi(n) is settled (then e = 1 is forced).

(6) THEOREM 2 (PROVED). If e is not in <3> modulo n, then
        N := <P, P^g, P^{g^2}>
    is a nontrivial perfect group ([N, N] = N, N not 1). Hence G is NOT solvable; and by the odd
    order theorem no finite group of odd order is a witness.
    Proof sketch: in the abelianization of N, R(v) reads pi0(v) + pi1(v^e) + pi2(v^{e^2}) = 0 for
    all v in U. The relation lattice L_e = span over GF(3) of {(v, v^e, v^{e^2}) : v in U} is all of
    F^3 exactly when e is not in <3> (LEMMA D: replace e by an odd representative modulo n, which is
    then a unit modulo 3^q - 1 with cube 1; expanding the trace form Tr(l a + m a^e + n a^{e^2})
    gives exponents lying in the three cosets <3>, e<3>, e^2<3> modulo 3^q - 1, which are pairwise
    disjoint precisely when e is not in <3>; Dedekind independence of the power monomials then kills
    l, m, n). Hence all three layer maps die in the abelianization, i.e. N is perfect.

(7) PROVED (new): the third layer is redundant, that is
        N = <P, P^g>.
    Indeed R(v) expresses the g^2-conjugate of x^{v^{e^2}} as a product of one element of the layer
    P^g and one of P; the map v -> v^{e^2} is onto U; and the U-orbit of x generates P.
    So N is a perfect group generated by TWO elementary abelian 3-subgroups of order 3^q each,
    permuted cyclically (together with the third layer) by the order-3 automorphism induced by g,
    and normalized by U, which acts fixed-point-freely on each layer (on the i-th layer through the
    character v -> v^{e^{-i}} times multiplication).

(8) MORE STRUCTURE THAT IS UNUSED SO FAR: D = <x, g> = <x, c> is contained in Q<x>, hence D is
    FINITE and metabelian (abelian-by-C3), and c is a 3-prime element. One may replace Q by [Q, x]
    (coprime action), so that C_Q(x) = 1 and K = Q<x> is a finite Frobenius group with kernel Q and
    complement <x> of order 3.

(9) COMPUTATIONALLY SETTLED: q = 7. For both exponents e of order 3 modulo n = 1093, coset
    enumeration (GAP) in the universal completion
        Gamma_e = < H, z | [z, z^x] = 1, (x z)^3 = 1, (x z) u (x z)^{-1} = u^e for u in U >
    (where z plays the role of c = x^{-1} g; every witness is a quotient of Gamma_e by z -> c)
    gives [Gamma_e : image of H] = 3. That means g normalizes H, so N is contained in H, which is
    metabelian; a perfect subgroup of a solvable group is trivial, so N = 1, contradicting the
    injectivity of sigma. Hence q = 7 admits no witness.

(10) NEGATIVE CHECKS (small cases, q = 3): PSL(2,27), PGL(2,27) contain H as a Borel subgroup but
     |N_G(U)| = 26, 52 is not divisible by 3; the affine type A Gamma L(1,27) fails because the only
     order-3 elements normalizing U reduce to the Frobenius, which commutes with x. Primitive groups
     of degree at most 21 do not contain H. (These are all subsumed by Theorem 1 now.)

(11) Gersten-Stallings non-sphericity for the triangle of groups (H, D, L = U<g>, edge groups <x>,
     U, <g>) does NOT apply: the link of the vertex U<g> has a closed path of length 4, so the
     angle condition sum of 1/m_v <= 1 fails. So no automatic infinite development.

THE ONE REMAINING CASE (this is what I want settled):
     q >= 13 prime with 3 dividing phi((3^q - 1)/2), an exponent e of order 3 modulo n with e NOT in
     <3>, and G non-solvable (G may be infinite; only Q must be finite).
     The smallest open case is q = 13, n = 797161, which has exactly two exponents e of order 3
     outside <3>. (Coset enumeration for q = 13 did not terminate under my limits: the relator u^n
     has length about 8 times 10^5.)

WARNING about what will NOT work. In the p = 2 world the witness SL(2, 2^q) is exactly a perfect
group generated by two abelian subgroups, namely <U, U-minus>, with a torus normalizing both and an
order 3 element cycling three root subgroups. So the conclusion of Theorem 2 plus (7) is NOT by
itself contradictory: the argument that closes the remaining case must use characteristic 3 in an
essential way (in characteristic 3 the relevant norm set satisfies E = E inverse automatically, so
the obstruction is not combinatorial; it is the realizability of (B)).

WHAT I WANT FROM YOU, in priority order:

A. Settle the remaining case. Either
   (A1) prove that no witness exists when q >= 13 and e is not in <3> (for arbitrary G, finite or
        infinite), for instance by proving that Gamma_e always collapses (z^3 = 1 in Gamma_e, or
        [Gamma_e : H] = 3, or N contained in H), or
   (A2) construct a witness, i.e. an explicit group G (possibly infinite), an embedding of H, a
        finite abelian 3-prime subgroup Q and an element y with the two normalizer properties.

B. If A is out of reach, settle q = 13 decisively (a proof, or a computation you can actually carry
   out and whose method I can reproduce: a shorter presentation, a Reidemeister-Schreier or
   low-index approach, a Todd-Coxeter strategy that avoids the length 8 times 10^5 relator, or a
   representation-theoretic obstruction).

C. Alternatively, identify the general mechanism behind the collapse observed for q = 7, e.g. by
   analysing the group N = <A, B> generated by two elementary abelian 3-groups A = P, B = P^g of
   order 3^q, admitting the cyclic group U of order (3^q - 1)/2 acting fixed-point-freely on each
   with twisted characters, an order 3 automorphism cycling A, B, C with C contained in <A, B>, and
   the relations R(v). Is such a configuration possible at all in characteristic 3?

FORMAT REQUIREMENTS.
- Separate clearly (a) what you have PROVED, (b) what you COMPUTED (state the computation and its
  parameters so I can rerun it), (c) what is a HEURISTIC guess or a plausibility argument.
- Complete arguments, not sketches, for anything you claim to have proved: I verify every step and
  then formalize it in Lean 4 with mathlib, so hand-waving is worse than an honest gap.
- If you cannot finish, still produce a PARTIAL REPORT: the reductions you established, the cases
  you eliminated, and the most promising line.
