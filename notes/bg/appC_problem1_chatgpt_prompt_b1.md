# ChatGPT (Chat surface / GPT-5.6 Sol / 推論レベル Pro) 投入プロンプト — (B1)+(B2) 一般証明 (2026-08-12)

2026-08-12 の部分解決 (issue 0180) の後、残っているのは (B1)+(B2) の一般証明だけ。
Work サーフェスが使えないのでユーザー指示により **Chat** サーフェスへ投入する。
本文は backtick / ドル波括弧 / バックスラッシュを含めない (合成 paste 用)。

---

OPEN PROBLEM (Glauberman-Norton 1993, "Problem (Peterfalvi)"; Bender-Glauberman, Local Analysis for
the Odd Order Theorem, Appendix C, p.152, Problem 1). The problem is untouched since 1993 (0 citations
in OpenAlex and in Semantic Scholar). I have reduced it to a purely arithmetic statement about power
maps on GF(3^q), and THAT is what I want settled. Everything marked PROVED below has been verified by
me and formalized in Lean 4 with mathlib (axiom-clean, machine-checked), so you may use all of it
freely as input. I verify every step of your answer and then formalize it, so hand-waving is worse
than an honest gap.

PART 0. THE ORIGINAL QUESTION (context only; the arithmetic problem in PART 2 is the real target)

Let q be an odd prime, F = GF(3^q), Q = 3^q, n = (Q - 1)/2.
P = (F, +), elementary abelian of order Q.
U = the group of nonzero squares of F = the norm-one subgroup of F over GF(3); cyclic of order n,
acting on P by multiplication, fixed-point-freely.
H = P semidirect U, a Frobenius group with kernel P and complement U; N_H(U) = U.
P0 = GF(3).1, the prime-field line in P, of order 3; x = 1 generates P0.

HYPOTHESIS (B) (the hypothesis of Proposition 9 of Glauberman-Norton, specialized to p = 3):
there exist a group G, an injective homomorphism sigma from H into G, a FINITE abelian subgroup
Qgrp of G of order prime to 3, and an element y of Qgrp, such that sigma(P0) normalizes Qgrp and
sigma(P0)^y normalizes sigma(U).
IMPORTANT: G is NOT assumed finite; only Qgrp is required to be finite. Completions of infinite
amalgams are legitimate candidates.

QUESTION (the 1993 problem): can (B) be satisfied for p = 3?
For p = 2 it can: SL(2, 2^q) and Sz(2^q) are witnesses (Examples 10 and 11 of the paper).

PART 1. WHAT IS ALREADY PROVED (all of it machine-checked in Lean 4)

I identify H with sigma(H) and write P, U for sigma(P), sigma(U). Put x = sigma(1) (order 3),
g = x^y (so sigma(P0)^y = <g>), c = x^{-1} g = [x, y] in Qgrp. Conjugation is a^b = b^{-1} a b.

(P1) c and c^x commute (Qgrp is abelian and x normalizes it), and the word identity
     [c, c^x] = (g x)^3, valid whenever x^3 = g^3 = 1 and c = x^{-1} g, therefore gives
     (g x)^3 = 1, that is x^{g^2} . x^g . x = 1.
     This is the ONLY nontrivial relation that (B) yields; everything below is built from it.

(P2) g normalizes U, which is cyclic of order n, and g^3 = 1, so there is an integer e with
     e^3 = 1 mod n and g u g^{-1} = u^e for all u in U. Conjugating (P1) by v in U gives the
     relation family
         R(v):   (x^{v^{e^2}})^{g^2} . (x^{v^e})^g . x^v = 1     for all v in U.
     Under the identification of P with (F, +), the U-orbit of x is exactly U (the nonzero squares).

(P3) THEOREM 1 (PROVED, no computer, all q, G arbitrary). If e lies in <3> modulo n, that is if
     u -> u^e is a power of the Frobenius on U, then (B) fails.
     Key input: the Paley-type set {s in F : s and s + 1 are both nonzero squares} spans F over
     GF(3); elementary proof, since -1 is a non-square (q odd).
     Consequences: q = 3 is settled, and so is every q with 3 not dividing phi(n), that is
     q = 5, 11, 17, 23, 37, 43 and so on, because then e = 1 is forced.

(P4) THEOREM 2 (PROVED). If e is not in <3> modulo n, then N = <P, P^g> is a nontrivial PERFECT
     group. Hence a witness G is never solvable; by the odd order theorem no finite group of odd
     order is a witness. (Proof: in the abelianization R(v) reads pi0(v) + pi1(v^e) + pi2(v^{e^2})
     = 0; the relation lattice spanned by the triples (v, v^e, v^{e^2}), v in U, is all of F^3
     exactly when e is not in <3>, by trace duality plus Dedekind independence of power monomials.)

(P5) THE TRACE OBSTRUCTION (the criterion that matters). Replace e by its ODD representative E
     modulo Q - 1; then E is a unit modulo Q - 1 with E^3 = 1, hence E^2 = E^{-1}, and E is not a
     power of 3 exactly when e is not in <3>. Call such an E EXOTIC. Define

         T    = {p in F : p and p - 1 are both nonzero squares},   |T| = (Q - 3)/4
         D(p) = p^E - (p-1)^E
         K(p) = (p-1)^{E^2} - p^{E^2}

     THEOREM (PROVED, Lean). Suppose there are p, r in T with p not equal to r such that
         D(p) = D(r),    delta := r^E - p^E is a nonzero square,
         and    Tr(K(p) . delta^{-E}) is not 0,     where Tr is the trace from F to GF(3).
     Then (B) fails (for arbitrary G, finite or infinite).

     Mechanism, for orientation: writing a(t), b(t) for the parameterizations of the layers
     P and P^g, the relations R(v) plus additivity give b(S)^{a(-1)} = b(S') with
     S = K(p) delta^{-E} and S' = K(r) delta^{-E}. In characteristic 3 one has p^3 - 1 = (p-1)^3,
     so S(p^3, r^3) = S(p, r)^3: the collision data is Frobenius equivariant. Multiplying the q
     Frobenius conjugates inside the abelian layer gives x . b(Tr S) . x^{-1} = b(Tr S'), and both
     traces lie in GF(3); since Aut(C3) = C2 has no element of order 3, x centralizes x^g, whence
     c^3 = 1, so c = 1 (c has order prime to 3), so g = x, contradicting N_H(U) = U.

     So ONE collision with nonzero trace kills the case. Explicit certificates (my own C and GAP
     code) have settled every odd prime q up to 43, and 4 of the 8 exotic exponents for q = 47.
     But there are infinitely many q, so certificates can never finish the problem.

PART 2. THE ARITHMETIC PROBLEM I WANT SETTLED

Let q be an odd prime, Q = 3^q, F = GF(Q), and let E be EXOTIC: E odd, E^3 = 1 mod (Q - 1), and E
not a power of 3 mod (Q - 1). With T, D, K as in (P5), prove for ALL such pairs (q, E):

   (B1) there exist p, r in T, p not equal to r, with D(p) = D(r) and r^E - p^E a nonzero square;
   (B2) at least one such collision satisfies Tr(K(p) (r^E - p^E)^{-E}) not equal to 0.

(B1) is the main point; (B2) is presumably easier but is also unproved in general.

EQUIVALENT FORMS AND STRUCTURE (all PROVED and formalized).

(a) D is the derivative in direction 1 of the power map x -> x^E, so the fiber sizes of D are the
    differential spectrum of x^E. In particular (B1) fails for a given E if x^E is APN (differential
    uniformity 2).

(b) FREE INVOLUTION. E is odd, so D(1 - p) = D(p) identically on F. Hence D is at least 2-to-1
    everywhere, and (B1) asks for an EXTRA collision. Moreover -1 is a non-square, so p -> 1 - p
    maps T bijectively onto Tpp = {p : p and p - 1 are both non-squares}. Therefore the free
    involution NEVER produces a collision inside T; it is exactly avoided.

(c) So: (B1) holds iff x^E is not APN AND some extra fiber contains two elements of T. Note the
    involution pairs off T with Tpp, so a fiber of size 4 whose two involution-pairs both meet
    T union Tpp automatically contains two elements of T. Heuristically T union Tpp has density 1/2.

(d) EVEN-FUNCTION FORM. Put z = p + 1 (characteristic 3), so p = z - 1 and p - 1 = z + 1. Then
    D(p) = -H(z) with H(z) = (z+1)^E - (z-1)^E, which is an EVEN function (H(-z) = H(z), again
    because E is odd), and T corresponds to Z = {z : z - 1 and z + 1 are both nonzero squares}.
    So (B1) says: the even function H is not injective on Z.

(e) TRIVIAL FIBERS. H is constant on GF(3) (H(0) = H(1) = H(-1) = -1, since E is odd), but the
    three points 0, 1, -1 all lie outside Z. More generally, if Fix = {t : t^{E-1} = 1} is the fixed
    subgroup of the order-3 automorphism omega: t -> t^E of F^x, then z + 1 and z - 1 both in
    Fix union {0} forces H(z) = -1. This gives a CONSTRUCTIVE certificate: if h in Fix and 1 - h in
    Fix, then f = (1 - h)^{-1} lies in Fix and f + 2 = h f lies in Fix, so p = f has p and p - 1
    both in Fix, and D(p) = f - h f = f(1 - h) = 1; all such f collide with each other. The expected
    number of such h is |Fix|^2 / Q, so this works only when |Fix| > sqrt(Q). It settles 4 of the 8
    exotic exponents for q = 47 with no search at all, but for q = 7 and q = 13 the number n is
    PRIME, so |Fix| = 2 and the method is vacuous. It does not touch the general case.

(f) FROBENIUS EQUIVARIANCE. S(p^3, r^3) = S(p, r)^3, so collisions come in Frobenius orbits and the
    span of the S-values is a Frobenius-stable GF(3)-subspace. I have also proved that ker Tr is the
    UNIQUE Frobenius-stable hyperplane of F; hence (B2) fails only if the whole span of the
    collision values sits inside that single hyperplane. Also Tr(S^3) = Tr(S), so one Frobenius
    orbit gives only ONE independent trial for (B2).

WHY THE OBVIOUS ATTACKS FAIL (please do not spend time re-deriving these).

(i) SIDON / PLANAR is vacuous here. The set A_E = {(u, u^E)} satisfies A_E = -A_E because E is odd,
    so it is never a Sidon set; equivalently x -> x^E is never planar for odd E. All known planar
    monomials in characteristic 3 (x^2, Dembowski-Ostrom x^{3^k+1}, Coulter-Matthews
    x^{(3^k+1)/2}) have EVEN exponent, so the planar classification cannot reach our E.

(ii) APN CLASSIFICATION would decide (B1) only conditionally. The conjecturally complete list of APN
     power exponents in odd characteristic (Helleseth-Rong-Sandberg and successors) has, for p = 3
     and odd degree, the candidates (3^q - 1)/2 - 1, (3^q + 1)/4 + (3^q - 1)/2, and 3^q - 3; I
     checked for q = 7, 13, 19 that none of them has multiplicative order 3 modulo 3^q - 1. So under
     that OPEN conjecture our x^E is never APN and extra collisions exist. I want something
     unconditional, or at least an unconditional proof for exponents of multiplicative order 3.

(iii) NAIVE COUNTING FAILS. With N = #{(p, r) in T^2 : D(p) = D(r)} and additive characters psi,
      N = |T|^2 / Q + (1/Q) sum over nontrivial psi of |S_psi|^2, where S_psi = sum over p in T of
      psi(D(p)). The main term |T|^2 / Q is about Q/16, which is SMALLER than the diagonal
      |T| = about Q/4. So proving N > |T| needs a LOWER bound on the character-sum energy
      sum |S_psi|^2. Weil-type upper bounds point the wrong way and are anyway trivial, since the
      degree E is of size about Q.

(iv) The group-theoretic routes are exhausted: coset enumeration of the universal completion
     (the relator u^n has length about 8 times 10^5 already for q = 13), abelianization (it is the
     same for all cases), and Gersten-Stallings non-sphericity for the triangle of groups (the angle
     condition fails, the link of the vertex U<g> has a closed path of length 4).

(v) An alternative route through Ito's theorem (if BA is inside AB with A, B abelian then <A,B> is
    metabelian, contradicting perfectness) reduces to a covering lemma whose core is the nonvacuity
    of {z : z, z - 1, z^E - 1 all squares}, i.e. to a nontrivial estimate for
    sum over z of chi((z-1)(z^E - 1)) with chi the quadratic character. Multiplicative Fourier
    expansion turns this into a correlation of normalized Jacobi sums, sum over characters phi of
    c_{phi^{-E}} c_phi, for which I only get the trivial bound. Same wall as (iii).

EMPIRICAL DATA (COMPUTED by me, reproducible).

For q = 13 I enumerated T exhaustively (|T| = 398580) for both exotic exponents. The fiber-size
distribution of D restricted to T is 2 : 38779, 3 : 3471, 4 : 234, 5 : 13, matching the Poisson
model with lambda = |T|/Q = 1/4 to within 0.06 percent for k = 2, with slightly fatter tails
(+1.8 percent overall). The two exotic exponents e and e^2 give IDENTICAL distributions (all four
numbers), which cannot be an accident and suggests a bijection between the collisions of D_E and
those of D_{E^2}. Non-harmonic substitutions (the six maps of the cross-ratio group) explain 26 of
50726 collision pairs for one exponent and 0 for the other. Frobenius-conjugate collisions never
occur. Among usable collisions the value Tr S is equidistributed over GF(3) to within one percent
(34.5 percent zeros against the predicted one third). So there is no structural mechanism producing
the extra collisions: (B1) really is an equidistribution statement.

WHAT I WANT FROM YOU, in priority order.

A. A PROOF of (B1) for all exotic E, or for all but finitely many q, or for an explicitly described
   infinite family of (q, E). A conditional proof is acceptable only if the hypothesis is something
   I can verify per q by a feasible computation. The natural analytic tools I am aware of are the
   power-moment identities for Weil sums of binomials (Katz, arXiv 1805.10452, where the differential
   spectrum of a power map is expressed through moments of Weil sums) and estimates for Weil sums
   over small subgroups (arXiv 2211.07739). The special structure to exploit is that omega: t -> t^E
   is an automorphism of F^x of ORDER 3 commuting with the Frobenius, so E^2 = E^{-1}, and that the
   ambient characteristic is 3 as well, so that omega and the Frobenius generate a small group acting
   on everything in sight.

B. A PROOF of (B2), or a reformulation of the obstruction in (P5) that avoids (B2) altogether
   (for instance, deducing a contradiction from the mere existence of one collision, by exploiting
   that the span of the collision values is a Frobenius-stable, hence GF(3)[Frobenius]-submodule of
   F, and that ker Tr is the unique invariant hyperplane).

C. A DIFFERENT general obstruction to (B) itself, not going through collisions. Concretely: by (P4)
   and a further reduction, a witness yields a nontrivial PERFECT group N = <A, B> generated by two
   elementary abelian 3-subgroups A, B of order 3^q, cyclically permuted (together with a third
   conjugate contained in <A, B>) by an automorphism of order 3, and normalized by a cyclic group U
   of order (3^q - 1)/2 acting fixed-point-freely on each layer through twisted characters
   v -> v^{e^{-i}}. Is such a configuration possible in characteristic 3?
   WARNING: in the p = 2 world the witness SL(2, 2^q) is exactly a perfect group generated by two
   abelian subgroups, so perfectness alone is NOT contradictory; any argument here must use
   characteristic 3 essentially.

D. Failing all of that, CONSTRUCT a witness: an explicit group G (infinite allowed), an embedding of
   H, a finite abelian subgroup Qgrp of order prime to 3, and an element y with the two normalizer
   properties.

FORMAT REQUIREMENTS.
- Separate clearly (a) what you have PROVED, (b) what you COMPUTED (give the parameters so I can
  rerun it), and (c) what is HEURISTIC.
- Give complete arguments, not sketches, for anything claimed as proved.
- If you cannot finish, still give a PARTIAL REPORT: the reductions established, the cases
  eliminated, the most promising line, and precisely where it breaks.
