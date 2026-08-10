# ChatGPT (Work / GPT-5.6 Sol, 思考レベル ウルトラ) prompt — BG App.C Problem 1

(2026-08-10, issue 0180. **未解決問題**。backtick / バックスラッシュ / ドル波括弧を含めない
= Chrome MCP の JS 注入にそのまま流せる形で書くこと。回答は鵜呑みにせず全 step 検証する。)

---

OPEN PROBLEM (1993, still open as far as I can tell): can the hypothesis of Glauberman-Norton
Proposition 9 be satisfied for p = 3?

I am formalizing the Feit-Thompson odd order theorem and its three source books in Lean 4.
Everything around this problem is already formalized and machine-checked (in particular
Glauberman-Norton Proposition 7: E = E^{-1} if and only if p <= 3). This problem is the one
remaining item, and it is genuine open mathematics, not a textbook exercise. I want either a
resolution or genuinely new, rigorously verified partial progress. Sections 1-3 below are input
that I have already verified; please check them but do not spend your effort re-deriving them.

SECTION 1. Notation and the exact statement.

Source: G. Glauberman and S. P. Norton, On a combinatorial problem associated with the odd order
theorem, Proc. Amer. Math. Soc. 119 (1993), 1089-1094, section 3 (DOI 10.1090/S0002-9939-1993-1160299-X).
Restated as Problem 1 on p.152 of Bender-Glauberman, Local Analysis for the Odd Order Theorem
(LMS Lecture Notes 188, 1994).

Notation (1) of that paper: p, q are primes; F_p = GF(p); F = GF(p^q); U is the set of
(p-1)-th powers in the multiplicative group of F, equivalently the kernel of the norm map
N : F^* -> F_p^*, cyclic of order (p^q - 1)/(p - 1); and E = {b in U : 2 - b in U}.
P is the additive group of F, U acts on P by multiplication, H = P U is the semidirect product
(a Frobenius group with kernel P and complement U), and P_0 is the image of the additive group
of F_p, a subgroup of P of order p.

Proposition 9 (= Peterfalvi, Lemma 3). Let p and q be arbitrary primes and assume the notation
above. Assume
 (A) q does not divide p - 1; and
 (B) there exist a monomorphism sigma of H into a group G, a finite abelian p'-subgroup Q of G,
     and an element y of Q such that sigma(P_0) normalizes Q and sigma(P_0)^y normalizes sigma(U).
Then E = E^{-1}.

By Proposition 7 of the same paper, E = E^{-1} forces p <= 3. The case p = 2 is realized:
Example 10 takes G = SL(2, 2^q), Example 11 takes G = Sz(2^q) with q odd. Hence:

PROBLEM (Peterfalvi). Can the hypothesis of Proposition 9 be satisfied for p = 3?

Two remarks from the paper itself: condition (A) forces q to be odd; and if 3 does not divide
|Aut U| then sigma(P_0)^y must centralize sigma(U) (their example: q = 5, where
|U| = (3^5 - 1)/2 = 121 = 11^2 and |Aut U| = 110).

IMPORTANT reading of the statement: G is NOT assumed to be finite. Finiteness is imposed only on
Q. So infinite completions are legitimate witnesses.

Literature status: Glauberman-Norton 1993 has 0 citations in OpenAlex (record W2059497267) and 0
in Semantic Scholar (both checked 2026-08-09), so there is probably no published follow-up. If
you find one, that by itself is valuable.

SECTION 2. Reductions I have already established (paper proofs; please verify, then build on them).

Fix p = 3. So F = GF(3^q), |P| = 3^q, U is cyclic of order (3^q - 1)/2, and H = P U is Frobenius.
Identify H with sigma(H) and let x be a generator of sigma(P_0), an element of order 3.

R1. y does not centralize x. Indeed H is Frobenius with complement U, so N_H(U) = U, and x is a
nontrivial element of P, so x does not normalize U. Whether x normalizes sigma(U) is decided
inside sigma(H) and therefore does not change when G grows. If y centralized x we would get
sigma(P_0)^y = sigma(P_0), contradicting (B).

R2. One may replace Q by [Q, x]. Q is a 3'-group and x has order 3, so coprime action on the
abelian group Q gives Q = C_Q(x) times [Q, x]. Writing y = y_1 y_2 with y_1 in C_Q(x) and y_2 in
[Q, x] we get x^y = x^{y_2}. After the replacement C_Q(x) = 1, so K = Q<x> is a finite Frobenius
group with abelian 3'-kernel Q and complement of order 3.

R3. Equivalent form of (B) for p = 3. Condition (B) holds if and only if there is a group G
containing H and an element g of N_G(U) with g of order 3 such that D = <x, g> is a finite
Frobenius group with abelian 3'-kernel A and complement of order 3. Forward direction: take
g = x^y and A = D intersect Q. Backward direction: in D = A<x> with A abelian all complements are
A-conjugate, so <g> = <x>^a for some a in A; take Q = A and y = a. In particular g is conjugate
to x inside D, and one may assume G = <H, g>.

R4. The paper's remark, made explicit: if 3 does not divide |Aut U| then g centralizes U, so
<U, g> = U times <g>; since C_H(U) = U this forces g to lie outside H.

SECTION 3. The completion reduction, and what the computer says for q = 3.

By R3, G = <H, g> is a completion of the triangle of groups with vertex groups H = P U,
D = A<x>, L = U<g> and edge groups <x> = H intersect D, U = H intersect L, <g> = D intersect L.
Concretely: fix D and fix the action of g on U (an automorphism of order dividing 3) and let
Gamma be the finitely presented group obtained by gluing the presentations of H and D along x and
adding the relations g u g^{-1} = u^{action}. A witness for that data exists if and only if H
embeds in Gamma (the image of <x, g> is then automatically of the required form, because a
quotient of A<x> by an x-invariant subgroup of A is again abelian-3'-by-C_3 with fixed point free
action, so the search over D is sound).

For q = 3: F = GF(27), P = C_3 x C_3 x C_3, U cyclic of order 13, H = 3^3 : 13 of order 351.
Aut(U) is cyclic of order 12, so the order-dividing-3 actions of g on U are u -> u, u -> u^3,
u -> u^9. The choice of x is irrelevant up to conjugacy, since U permutes the 13 lines of P
transitively. The candidates D = A<x> with A abelian 3' and x acting fixed point freely and
|D| <= 60 are: A_4, C_7 : C_3, C_13 : C_3, (C_4 x C_4) : C_3, C_19 : C_3.

GAP 4.16 coset enumeration (Todd-Coxeter, 300 s timeout per case; 24 cases = the 5 groups D,
times 1 or 2 Aut(D)-orbit representatives of generating pairs (x, g), times the 3 actions):
 - 9 cases collapse, so H does not embed: A_4, one of the two generating pairs of C_7 : C_3, and
   (C_4 x C_4) : C_3, each for all three actions. The collapsed orders are |Gamma| = 13 for the
   trivial action and |Gamma| = 1 for u -> u^3 and u -> u^9.
 - 15 cases time out and are UNDECIDED: the other generating pair of C_7 : C_3, both pairs of
   C_13 : C_3, and both pairs of C_19 : C_3, each with all three actions. A timeout does not mean
   impossible; I cannot tell whether Gamma is infinite or the enumeration is merely hard.

Those collapsed orders are exactly the abelianization, which I can compute by hand and which is
independent of D: in the abelianization P dies (U acts fixed point freely on P, so for the matrix
M of a generator of U the map M - I is invertible over F_3, and killing the action forces the
image of P to be trivial); D^ab = C_3 with x mapping onto a generator, and g is D-conjugate to x
so has the same image, whence both die; the surviving relation on u is u^{action - 1} = 1
together with u^13 = 1. So Gamma^ab is C_13 for the trivial action and trivial otherwise.
Consequence: abelian invariants give no information whatsoever about the 15 undecided cases.

Concrete finite groups ruled out for q = 3:
 - PSL(2,27) and PGL(2,27): H sits inside as the Borel subgroup, but |N_G(U)| is 26 resp. 52,
   not divisible by 3, so there is no g of order 3 at all.
 - The AGammaL(1,27) pattern, that is P normal in G: every element of order 3 in N_G(U) is
   U-conjugate to the Frobenius map phi : a -> a^3, and phi fixes 1, hence commutes with the
   translation x by 1, so <x, phi> = C_3 x C_3 is not Frobenius; and <x, phi^u> contains P, whose
   kernel would then be a 3-group.
 - No primitive permutation group of degree at most 21 contains H. (This is not evidence of much:
   A_27 contains H, so sweeping by degree is not an exhaustive method.)

The Gersten-Stallings non-sphericity criterion for triangles of groups does not apply here: at
the vertex L = U<g> the link contains a closed path of length 4, because u_1 g^a u_2 g^{-a} = 1
has nontrivial solutions, so the relevant girth parameter is 2 and the condition that the sum of
the reciprocals is at most 1 fails. So I cannot conclude developability (hence embedding of H)
for free.

SECTION 4. What I am asking for, in priority order.

(1) Decide the 15 undecided cases for q = 3. Concretely: for D in {C_7 : C_3, C_13 : C_3,
    C_19 : C_3} with the relevant generating pair (x, g) and the action u -> u, u -> u^3,
    u -> u^9, does H = 3^3 : 13 embed in Gamma? Methods worth trying, and please report
    reproducible code (GAP or Magma) together with its actual output:
     - coset enumeration over the subgroup H, or over U, or over D, rather than over the trivial
       subgroup, with several strategies (ACE, Felsch, HLT, lookahead and workspace settings);
     - low index subgroups of Gamma; p-quotient for several p; nilpotent and solvable quotient
       algorithms; simple quotient searches (L2-quotient, LnQ), and searches for homomorphisms of
       Gamma onto finite groups. Any finite quotient in which H embeds faithfully and the image
       of <x, g> is Frobenius of the required form IS a witness, since G need not be simple or
       even finite;
     - automatic structure or Knuth-Bendix (KBMAG), or an explicit action of Gamma on a tree or a
       CAT(0) triangle complex, to prove that H embeds;
     - or, in the other direction, an explicit proof of collapse, for instance a derivation
       showing that the relations force P into the kernel.
(2) A complete answer for q = 3: either an explicit witness (G, sigma, Q, y), possibly with G
    infinite, or a proof that no such G exists.
(3) The general case p = 3, arbitrary odd q. Note the special sub-case singled out by the paper,
    where 3 does not divide the order of Aut U, so that g must centralize U.
(4) A literature check: anything after 1993 touching this problem, in Peterfalvi's book Character
    Theory for the Odd Order Theorem (LMS 272, 2000), in Bender-Glauberman p.152, or anything
    citing Glauberman-Norton 1993. Report exact citations if you find any.

SECTION 5. Ground rules.

 - Separate clearly (a) statements you have proved, with the complete proof, (b) computations you
   actually ran, with the code and its output, and (c) heuristics, analogies and conjectures.
   Never present (b) or (c) in the voice of (a). I will re-verify everything and formalize the
   parts I keep in Lean 4, so state the hypotheses of every claim explicitly.
 - Do not re-derive sections 1 to 3; they are already verified. Correct them if you find an error.
 - A previous very long run on this problem returned nothing at all because it never terminated.
   A partial but complete and correct report is far more valuable to me than an unfinished search.
   So please budget your effort and, whatever happens, deliver a written report stating: which
   cases you settled and how, which methods you tried and why they failed, and the single most
   promising next step.
