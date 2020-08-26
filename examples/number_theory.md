---
layout: page
title: Number theory
---


Ivy is based on the idea that the automated parts of a proof should
be expressed in a decidable logical fragment so that the automated
prover will behave in a more predictable and stable way.  Ivy's
fragment checker provides feedback when a proof goal falls outside
the decidable fragment to help in fixing the problem. Typically, to
stay within the decidable realm, we break the proof into lemmas, or
we manually instantiate quantifiers.

There are cases, however, where this becomes difficult. Ivy checks
that proof obligations fall into the FAU fragment, which is
decidable *if* the theories used are decidable for formulas without
quantifiers.  This holds true for the theory of linear integer
arithmetic (LIA). A formula is on LIA if in every term of the form
`X*Y`, either `X` or `Y` is a numeric constant. If, however, we
allow non-linear terms, then validity of even quantifier-free
formulas is undecidable.

The fragment checker does not reject non-linear formulas in
FAU. This is because Z3 can sometimes provide proofs about
non-linear arithmetic and manually reducing proofs about arithmetic
to linear subgoals using axioms is very tedious. This mean is that,
for non-linear proof goals, we have to accept the fact the Z3 will
be unpredictable and unstable. We will frequently get timeouts or
incorrect counter-examples. We can mitigate this problem by pushing
the arithmetic reasoning into simple generic theorems that don't
need frequent revisions.

In this file, we develop some theorems of elementary number theory,
to illustrate how Z3 can be used to help prove simple arithmetic
facts. We will cover some facts about divisibility, greatest common
divisors and prime numbers and end with a proof that the square root
of two is irrational.  We will still use the normal strategy of
manually instantiating quantifiers that the fragment check complains
about. However, in some cases we will also have to provide some
"hints" to help Z3 prove simple arithmetic facts.

The theorems developed here are based on the presentation in the
online textbook [Logic and
Proof](https://leanprover.github.io/logic_and_proof/index.html) by
Leonardo DeMoura.

First, we instantiate a type `nat` corresponding to the natural numbers.

```
include arith_nat
instance nat : arith_nat

```
The `arith_nat` module comes with some basic facts about arithmetic,
including induction principles.

As an example of a very simple arithmetic fact that Z3 cannot prove
(at the time of this writing) consider the following:


```
theorem [triv1] {
    property B:nat > 0
    property A:nat * B = C
    property A:nat = C / B
}

```
You can wait quite a while for Z3 to try to prove this triviality.
Try commenting out the proof below to test this out.  The problem is
that, since it doesn't produce a result, we get no help in figuring
out how to make the proof easier. Our approach is simply to go in
small steps. First we divide through by `B`, then we regroup terms:

```
proof {
    property (A:nat * B) / B = C / B proof {}
    property A:nat * (B/B) = C / B proof {}
}    

```
Each of these two steps can be proved by Z3, as can the conclusion.
However, the first step alone is not sufficient.  Having finished
the proof, we can try deleting some steps to see if Z3 can do
without them. In fact, the first step is not necessary (for the
version of Z3 used at this writing). Try commenting it out to see.
In the proofs below, we've deleted the unnecessary hints, on the
theory that they might make the proofs more fragile and less
re-usable. However, when developing proofs with non-linear
arithmetic, it's better to go in small steps to reduce confusion.
Fortunately, although Z3 can't handle the above very trivial proof,
it can often handle substantially more complex proof goals. The
point is that, with undecidable theories, we sometimes fail on even
very small problems and we need some strategy to recover from these
failures.

Quotients and remainders
------------------------

We prove some useful properties of quotients and remainders of
division. First we need a couple of lemmas about multiplication
and division to use later.

**Lemma (Multiplication expanding).**

If `X` is positive, then `MX >= M`.

Luckily, Z3 gets this by itself.

```
theorem [mul_expand] {
    property X:nat > 0
    property M:nat * X >= M
}

```
**Lemma (Division by subtraction).**

If `M` positive and `N >= M` then `N:nat/M = (N - M) / M + 1`

Proof. Z3 can't prove this directly. We have to tell it to
distribute the division over the subtraction (note, integer division
does not always distribute, but it does in this case). This is another
example of proceeding in small steps to help out the non-linear arithmetic
procedure in Z3. 

```
theorem [div_rec] {
    property M:nat > 0 & N:nat >= M
    property N:nat/M = (N - M) / M + 1
}
 proof {
    property (N:nat - M) / M = N/M - M/M proof {}
}

```
Now we define the notion of quotient and remainder. It is convenient
to create a macro `quot_rem` for this, so we don't have to keep
writing this formula.

**Definition (Quotient/Remainder).**

A quotient/remainder pair (Q,R) for division of N by M is such that
`R < M` and `N = Q*M + R`.

```
relation quot_rem(N:nat,M:nat,Q:nat,R:nat)
explicit definition quot_rem(N,M,Q,R) = R < M & N = Q * M + R

```
**Theorem (Quotient/Remainder existence).**

Let `N,M` be natural numbers with `M > 0`. There exists a quotient/remainder
pair `(Q,R)` for division of N by M.

Proof by general induction on `N`. If `N` is less than `M`, then
`Q=0` and `R=N`. Else let `_Q,_R` be the quotient and remainder for
`N-M`, by the inductive hypothesis. Then `Q=_Q+1` and `R=_R`.

To convince the prover of this, we start by unfolding the definition
of `quot_rem`, then apply the induction schema with `N` substituted for
the induction variable `X` in the schema. This is sufficient to match
the conclusion `p(X)` in the schema to our proof goal. We must now
prove our property for arbitrary `x`, assuming the it holds for all
numbers less than `x` (the induction hypothesis). We then split
cases on whether `x < M`. This is easy because the quotient must be
0 and the remainder must be `x`. We 'forget' the induction
hypothesis, since it isn't needed and it has a quantifier. Z3 does
the rest.

In the remaining case, `x >= M`, we subtract `M` from `x`. The
inductive hypothesis gives us a quotient/remainder pair `(_Q,_R)`
for `x-M`. Adding one to the quotient, we get a quotient/remainder
pair for `x`.


```
explicit property [quot_rem_ex] M:nat > 0 -> exists Q,R. quot_rem(N,M,Q,R)
proof {
    unfold with quot_rem
    apply nat.gen_ind with X=N
    apply exmid with q = (x < M)
    proof [pos] {
        instantiate with Q=0:nat,R=x
        forget ind_hyp
    }
    proof [neg] {
        instantiate ind_hyp with Y = x - M
        tactic skolemize
        instantiate with Q = _Q + 1, R = _R
    }
}

```
**Theorem (Quotient/Remainder uniqueness).**

Let `N,M` be natural numbers with `M > 0` and let `Q,R,Q1,R1` be such that
`quot_rem(N,M,Q,R)` and `quot_rem(N,M,Q1,R1)`. Then `Q1=Q` and `R1=R`.

Proof. Assume `Q1~=Q` and consider the case `Q < Q1`. We have `R
= M:nat * (Q1-Q) + R1` and, since `Q1-Q` is positive, we have `M * (Q:nat -Q1) >= M`.
Thus, `R1 >= M`, a contradiction. The case `Q > Q1` is symmetric. Thus
by contradiction `Q1=Q` and hence `R1=R`.

Notice in the proof, the cases `Q < Q1` and `Q > Q1` are not
quite symmetric. This is because in the latter case, Z3 doesn't
get the fact that `M * (Q:nat -Q1) >= M` and we have to prove it
manually. This is characteristic of non-linear arithmetic using
Z3: sometimes there are very simple facts that is doesn't get,
and there is some guesswork involved in finding the missing fact
that it needs. Although the proof below looks simple, it was
quite time-consuming to produce because Z3 diverged or produced
an "unknown" result without giving good feedback as to the
source of the problem.

```
explicit property [quot_rem_uniq]
M:nat > 0 & quot_rem(N,M,Q,R) & quot_rem(N,M,Q1,R1) -> Q1=Q & R1=R
proof {
    unfold with quot_rem
    apply introImp
    apply exmid with q = (Q=Q1)
    proof [neg] {
        apply exmid with q = (Q < Q1)
        proof [pos] {
            property R = M:nat * (Q1-Q) + R1 proof {}
        }
        proof [neg] {
            property R1 = M:nat * (Q-Q1) + R proof {}
            property M * (Q:nat -Q1) >= M proof {apply mul_expand}
        }
    }
}

```
**Lemma (Division).**

If `M > 0` then for some `R`, `quot_rem(N,M,N/M,R)`.

Since `R` is unique, this could be seen as a definition of the
division operator. However, we can't define `/` because it is
already interpreted in the natural number theory. Instead, we
prove it from the theory. Unfortunately, Z3 can't prove it
because of the existential quantifier. The proof follows very
closely the proof of `quote_rem_ex` above, where the unknown
quotient `Q` is replaced by the term `N/M`.


```
theorem [div_lem] {
    property M:nat > 0
    property exists R. quot_rem(N,M,N/M,R)
}

proof {
    unfold with quot_rem
    apply nat.gen_ind with X=N
    apply exmid with q = (x < M)
    proof [pos] {
        instantiate with R = x
        forget ind_hyp
    }
    proof [neg] {
        instantiate ind_hyp with Y = x - M
        tactic skolemize
        property x/M = (x - M) / M + 1 proof {apply div_rec}
        instantiate with R = _R
    }
}

```

Greatest Common Divisors and Prime numbers
------------------------------------------

We start by defining some elementary concepts from number
theory, including 'divisor' and 'common divisor'.

**Definition (Divisor).**

Relation `dvds(X,Y)` is true if X is a divisor of Y. We define it
here in terms of the integer division operator instead of saying the
there exists a number `N` such that `N * Y = Y`. This is convenient
because it lets Z3's non-linear arithmetic capability do some work
for us. Later, though, we'll need to introduce the more traditional
definition as an alternative.

Because this definition uses arithmetic and the variables `X` and
`Y` are implicitly universally quantified, it might lead to proof
goals that are outside the decidable fragment. For this reason, we
make it an 'explicit' definition, meaning that it is not used by the
default tactic and we have to instantiate it explicitly.

```
relation dvds(X:nat,Y:nat)
explicit definition dvds(X,Y) = (X > 0 & (Y/X) * X = Y)

```
**Definition (Common Divisor).**

Relation `commdiv(Z,X,Y)` is true if Z is a common divisor of X and
of Y.

```
function commdiv(Z,X,Y) = dvds(Z,X) & dvds(Z,Y) 

```

**Definition (GCD).**

Definition of greatest common divisor. Z is a GCD of X,Y if Z
is a common divisor of X and Y and if no lesser number is so.

Notice that this is also an explicit definition. There are two
reasons that using it by default might lead to
undecidability. First, it has a quantified symbol under
arithmetic. Second, it has a quantifier alternation from type nat to
type nat.


```
relation is_gcd(Z:nat,X:nat,Y:nat)
definition {is_gcd(Z,X,Y) =
    commdiv(Z,X,Y) & forall W. commdiv(W,X,Y) -> Z >= W}

```

**Definition (GCD function).**

We can now define a function `gcd(X,Y)` that returns the GCD when X
and Y are positive and is otherwise undefined. We first prove a
lemma [lem] that, under the assumption, that `X` and `Y` are
positive, a GCD exists. This is done by unfolding the definition of
GCD and matching the greatest element principle provided by
`arith_nat`. This says that any non-empty, upper-bounded set of
natural numbers has a maximum element.  As the upper bound `n`, we
use X, since a divisor of X cannot be greater than X.

This generates two subgoals: that there exists a common divisor
[prem1] and that there is no common divisor greater than `X`
[prem2].  The first premise we witness with 1, which is always a
common divisor.  The second Z3 can prove by itself. From the lemma,
Z3 can prove the goal.  This amounts to just moving the condition 'X
and Y are positive' inside the existential quantifier.

By showing the existence of Z, we can define a function `gcd(X,Y)`
that yields some Z satisfying the property. This gives us the
property `X > 0 & Y > 0 -> is_gcd(gcd(X,Y),X,Y)`. When X or Y is
zero, `gcd(X,Y)` can be any natural number.


```
explicit property [gcd_prop]
exists Z. X > 0 & Y > 0 -> is_gcd(Z,X,Y)
named gcd(X,Y)

proof {
    theorem [lem] {
        property X:nat>0 & Y:nat>0
        property exists Z. is_gcd(Z,X,Y)
    }
    proof {
        unfold with is_gcd,commdiv,dvds
        apply nat.gep with n=X
        proof [prem1] {
            instantiate with Z=1:nat
        }
    }
}

```
We prove some useful properties of GCD.

**Theorem (GCD with self)**

If X is positive, the GCD of X and itself is X.

Since `X` is a common divisor, the GCD must be greater than or equal
to `X`. Since no divisor of `X` is greater that `X`, `X` must be the
GCD. To get Z3 to prove this, we instantiate the defining property
of GCD. Unfolding the definitions of `is_gcd`, `commdiv` and
`dvds`, we get a formula of arithmetic saying that every divisor `W`
of `X` is <= the GCD. In particular, by plugging in `X` for `W`, we
get that the CGD is <= X. Now the proof goal is
quantifier-free. Amazingly, Z3 can prove it with no further help.
However, notice that it was necessary to instantiate `W` manually,
to avoid applying interpreted arithmetic operators to a quantified
variable.

```
explicit property [gcd_self] X > 0 -> gcd(X,X) = X
proof {
    instantiate [g] gcd_prop with X=X, Y=X
    unfold g with is_gcd,commdiv,dvds
    instantiate g with W=X
}

```
**Theorem (GCD symmetric).**

If X and Y are positive, then `gcd(X,Y) = gcd(Y,X)`.

This follows from commutativity of the 'and' operator in
the definition of `is_gcd`. We don't have to unfold the
definition of `dvds`.

```
explicit property [gcd_symm]
forall X,Y. X>0 & Y>0 -> gcd(X,Y) = gcd(Y,X)
proof {
    tactic skolemize
    instantiate [g1] gcd_prop with X=_X, Y=_Y
    instantiate [g2] gcd_prop with X=_Y, Y=_X
    unfold g1 with is_gcd,commdiv
    unfold g2 with is_gcd,commdiv
}

```
**Definition (prime number).**

A natural number `X > 1`  is *prime* if its divisors are only one and
itself.


```
relation prime(X:nat)
explicit definition prime(X) = X > 1 & forall Y. dvds(Y,X) -> Y=1 | Y=X

```
Two positive numbers are 'co-prime' if their GCD is one.

**Lemma (Prime/Coprime).**

If `N>0` is a natural number and `P` is a prime number, then either
`N` and `P` are coprime or `P` divides `N`.

To prove this, we instantiate the GCD property, the definition
`is_gcd`, the definition of prime number and the definition of
common divisor. The idea is that since `gcd(N,P)` divides `P` and
`P` is prime, it must equal `1` or `P`. In the first case we have
our conclusion directly.  in the second case, we have the
`dvds(P,N)` by the definition of common divisor.

```
theorem [lemma_prime_coprime] {
    property N:nat > 0
    property [prem] prime(P)
    property gcd(N,P) = 1 | dvds(P,N)
}
proof {
    unfold prem with prime
    instantiate prem with Y=gcd(N,P)
    instantiate [gp] gcd_prop with X=N,Y=P
    unfold gp with is_gcd
    instantiate gp with W = N
    instantiate commdiv with Z=gcd(N,P),X=N,Y=P
}


```
**Lemma (Divisor, alternate definition).**

Natural number `X` is a divisor of `Y` iff `X` is positive and
there exists a `Z` such that `X * Z = Y`.

This could be considered the definition of `dvds`. Here, we prove it as a lemma.

For the forward implication, we give `Y/X` as the witness for `Z`, and unfold
the definition of divides. Z3 can do the rest.

In the reverse case, we have to prove `(Y / X) * X = Y` from `Z * X
= Y`. Sadly, Z3 can't do this. As a first step, we divide through by `X` and
regroup to get `_Z * (_X/_X) = _Y/_X`. Z3 can do the rest (i.e., substituting
`Y/X` for `Z` to get the conclusion).

```
explicit property [dvds_alt] forall X,Y. dvds(X,Y) <-> (X > 0 & exists Z. Z * X = Y)
proof {
    tactic skolemize
    apply introIff
    proof [fwd] {
        instantiate with Z = _Y/_X
        unfold prem with dvds
    }
    proof [rev] {
        tactic skolemize
        unfold with dvds
        property _Z * (_X/_X) = _Y/_X proof {}
    }
}

```
The next lemma is the basis for Euclid's algorithm for computing the
GCD. That is, provided `N > M`, `gcd(N,M)` is preserved by
subtracting `M` from `N`. 

**Lemma (GCD/Euclid).**

If `N>M>0` then `gcd(M,N) = gcd(M,N-M)`

We start by proving that the common divisors of `M` and `N` are exactly
the common divisors of `M` and `M-N`. The forward and reverse directions of this
bi-implication are similar, but not quite identical. In the forward case, suppose
`M = A * Z` and `N = B * Z`. Then `N-M = Z * (B-A)`. Thus, Z is a common divisor of
`M` and `N-M`.

Notice that in the formal proof, something funny is happening at line
`[*]`.  That is, we take the premise `commdiv(Z,M,N)` and unfold
`commdiv` to get `dvds(Z,M) & dvds(A,N)`. Then we unfold with
`dvds_alt` which is `dvds(X,Y) <-> (X > 0 & exists Z. Z * X =
Y)`. Since there are two instances of `dvds` in our formula, we
would get two quantified subformulas, `exists Z_a. Z_a * Z = M` and
`exists Z_b. Z_b * Z = N` where the bound variable `Z` in `dvds_alt`
has been renamed respectively to `Z_a` and `Z_b` to avoid capturing
the existing variable `Z`. There is nothing logically wrong with
this, but the two generated names `Z_a` and `Z_b` (corresponding to
`A` and `B` above) might be hard to predict and might later change
if the proof context changes. For this reason, it's best to avoid
generated names. In the `unfold` command, we give two
alpha-renamings `<A/Z>` and `<B/Z>`. The first is used for the first
(left-most) unfolding of `dvds_alt` and the second is used for the
second unfolding. This eliminates the variable name clash and gives
us two distinct names we can refer to later. In particular, after Skolemization,
these become `_A` and `_B`, which we can use to instantiate the existentials in
the conclusion, at line `[**]`.

For the reverse direction of the proof, suppose `M = A * Z` and `N-M
= B * Z`. Then `N = Z * (B+A)`. Thus, Z is a common divisor of `M`
and `N-M`.

Once we know the common divisors are the same, we can just unfold
the definition of GCD in terms of common divisors and let Z3 do the
rest of the proof, which is purely first-order reasoning.

```
explicit property [gcd_euclid] N > M & M > 0 -> gcd(M,N) = gcd(M,N-M)

proof {
    apply introImp
    property [lem] forall Z. (commdiv(Z,M,N) <-> commdiv(Z,M,N-M))
    proof {
        tactic skolemize
        apply introIff
        proof [fwd] {
            unfold prem with commdiv,dvds_alt<A/Z><B/Z>  # [*]
            unfold with commdiv,dvds_alt<A1/Z><B1/Z>
            tactic skolemize
            instantiate with B1 = (_B - _A), A1 = _A  # [**]
        }
        proof [rev] {
            unfold prem with commdiv,dvds_alt<A/Z><B/Z>
            unfold with commdiv,dvds_alt<A1/Z><B1/Z>
            tactic skolemize
            instantiate with B1 = (_B + _A), A1 = _A
        }
    }
    instantiate [g1] gcd_prop with X=M,Y=N
    instantiate [g2] gcd_prop with X=M,Y=N-M
    unfold g1 with is_gcd
    unfold g2 with is_gcd
}

```
We can use the above to prove Bezout's lemma, an important fact
about GCD's that we will apply to help us prove facts about prime
factorizations.  

**Theorem (Bezout's lemma).**

If `S,T` are positive, then there exist `A,B` such that `A*S-B*T =
gcd(S,T)`.

Proof. By induction over `max(S,T)` using the GCD/Euclid lemma.

To prove this, we first restate the theorem with an additional
premise `M = max(S,T)`. We can then match the general induction
schema with the induction variable `X=M`. We then, in effect,
Skolemize the quantifiers on `S,T` using the `introA` rule and we
split cases on whether `S > T`, `S=T` or `S<T`. In the first case,
we take the inductive hypothesis for `gcd(S-T,T)`. That is, since
`S>T` we know that `max(S-T,T) < max(S,T)`, so the theorem holds by
induction on `max(S,T)`. There is a bit of a technicality here, as
we have to plug in `max(S,S-T)` as the induction parameter `Y` of
the induction hypothesis.  Now by the GCD/Euclid result, we get the
theorem by plugging in `A+B` for `B`.

In the case `S=T`, the assignment `A=1,B=0` proves the theorem and
we can forget the induction hypothesis (this is essentially the
termination case for Euclid's algorithm). Finally, the case `S > T`
is symmetric to `S < T`.

Having proved the lemma for all values of `max(S,T)`, we eliminate
the induction variable `M` by instantiating our lemma with
`M=max(S,T)` (i.e., witnessing the fact that every pair `M,T` has a
max).

```
explicit property [bezout_lemma]
S:nat > 0 & T:nat > 0 -> exists A,B. A*S - B*T = gcd(S,T)

proof {
    property [bezout_lemma_pre]
    forall S:nat,T. S > 0 & T > 0 & M = (S if S > T else T)
       -> exists A,B. A*S - B*T = gcd(S,T)
    proof {
        apply nat.gen_ind with X=M
        apply introA<_S/x>
        apply introA<_T/x>
        apply exmid with q = (_S >= _T)
        assume gcd_symm
        proof [pos] {
            apply exmid with q = _S > _T
            proof [pos] {
                instantiate ind_hyp with S=_S-_T, T=_T, Y = _S-_T if _S-_T > _T else _T
                instantiate gcd_euclid with M=_T, N=_S
                tactic skolemize
                instantiate with A = _A, B = _A+_B
            }
            proof [neg] {
                instantiate gcd_self with X=_S
                instantiate with A = 1:nat , B = 0:nat
                forget ind_hyp
            }
        }
        proof [neg] {
            instantiate ind_hyp with S=_S, T=_T-_S, Y = _T-_S if _T-_S > _S else _S
            instantiate gcd_euclid with M=_S, N=_T
            tactic skolemize
            instantiate with A = _A+_B, B = _B
        }
    }
    instantiate bezout_lemma_pre with S=S,T=T,M = (S if S > T else T)
    tactic skolemize
    instantiate with A=_A,B=_B
}

```
Here is a useful consequence of Bezout's lemma.

**Lemma (Coprime/Product).**

For any positive `P`, `N` and `M`, if `N` and `P` are co-prime and `P`
divides `N * M` then `P` divides `M`.

Proof. By Bezout's lemma, we have `gcd(T,P) = A*T - B*P`. Now assume
that `P*_Z=N*M`. It follows that `P*(A*_Z-B*M) = M`.

```
theorem [coprime_product] {
    property N:nat > 0 & P:nat > 0 & M:nat > 0
    property gcd(N,P) = 1
    property [prem] dvds(P,N*M)
    property dvds(P,M)
}
proof {
    instantiate bezout_lemma with S=N, T=P
    tactic skolemize
    unfold prem with dvds_alt
    unfold with dvds_alt
    tactic skolemize
    instantiate with Z = _A * _Z - _B * M
}

```
Also, using Bezout's lemma, we can show the following.

**Lemma (Divisor/GCD).**

If `a` and `b` are positive, and if `c` is a common divisor of
`a,b`, then `c` is a divisor of `gcd(a,b)`.

Proof. By Bezout's lemma, we have `gcd(a,b) = A*a - B*b`. Moreover,
we have `C * c = a` and `D * c = b`.  It follows that `c * (_A * _Z
- _B * _Z_a) = gcd(a,b)`.

```
theorem [dvds_gcd] {
    individual a : nat
    individual b : nat
    individual c : nat
    property a > 0 & b > 0
    property [prem1] dvds(c,a)
    property [prem2] dvds(c,b)
    property dvds(c,gcd(a,b))
}

proof {
    instantiate bezout_lemma with S=a, T=b
    unfold prem1 with dvds_alt<C/Z>
    unfold prem2 with dvds_alt<D/Z>
    unfold with dvds_alt
    tactic skolemize
    instantiate with Z = _A * _C - _B * _D
}

```
A consequence the Coprime/Product lemma is that if a prime divides a
product, it divides one of the factors.

**Lemma (Prime/Product).**

For any prime `P` and `N` and `M`, if `P` divides `N * M` then `P`
divides `N` or `M`.

Proof. Use the Prime/Coprime lemma, the Coprime/Product theorem and
the definition of prime.

Something subtle happens here in the instantiation of
`lemma_prime_coprime`.  That is, we use premise `prem1` of our
theorem to supply premise `prem` of `lemma_prime_coprime`, saying
that `P` is prime. As an alternative to this, we could have unfolded the
definition of prime in `lemma_prime_coprime`. This way can sometimes work out
better, however, if the definition contains a quantifier.

Generally speaking, if you want to use a premise you already have to
supply a premise of a schema you are instantiating, you should state
this in the substitution.

```
theorem [prime_dvds_product] {
    property N:nat > 0
    property M:nat > 0
    property [prem1] prime(P)
    property [prem2] dvds(P,M*N)
    property dvds(P,M) | dvds(P,N)
}
proof {
    instantiate lemma_prime_coprime with P=P,N=N,prem=prem1
    instantiate coprime_product with P=P,M=M,N=N
    unfold prem1 with prime
}

```

Squares and square roots
------------------------

Now we will use our properties of primes and GCD to prove a fact
known to the Pythagorean School of ancient Greece: no rational
number is a square root of two. 

First, for convenience, we define the squaring function:

**Definition (Squaring).**

```
function squared(X:nat) : nat
explicit definition squared(X) = X * X

```

This is a useful special case of the Prime/Product lemma that we'll
use twice in the proof:

**Lemma (Prime/Square).**

If a prime divides `squared(A)` then it divides `A`.

Proof. Unfold `squared` and apply the Prime/Product lemma.

```
theorem [prime_square] {
    individual a : nat
    individual b : nat
    property [prem1] dvds(b,squared(a))
    property prime(b)
    property dvds(b,a)
}

proof {
    unfold prem1 with squared
    instantiate prime_dvds_product with P = b, N=a, M=a
}

```
Now we're ready to prove that there is no rational square root of 2.
Actually, we prove the closet thing we can in integer arithmetic,
that is, there is no reduced fraction `a/b` such that `squared(a/b)
= 2`.  We state this as follows:

**Theorem (Square root of 2 irrational).**

Given positive natural numbers `a,b` such that `gcd(a,b) = 1`, it is not the
case that `squared(a) = 2 * squared(b)`.

Proof. 2 is prime. Moreover, 2 is a divisor of `a`, witnessed by `squared(b)`.
By the Prime/Square lemma, it follows that 2 is a divisor of `a`, thus there is a `_Z`
such that `_Z * 2 = a`. Thus, `squared(a) = 4 * squared(_Z) = 2 * squared(b)`.
By the Prime/Squared lemma, 2 is a divisor of `b`. This contradicts `gcd(a,b) = 1`.

In the formal proof, we took three steps in the above argument as
lemmas: 2 is prime, `squared(a)` is even, and `squared(a) = 4 *
squared(_Z)`. The proof of these lemmas and the final result was
done by instantiating properties and definitions. This still left a
fair amount of reasoning to do. For example, to get the conclusion
from `squared(a) = 4 * squared(_Z)` we need to apply transitivity of
equality, divide through by two and apply the definition of
`dvds`. This was done automatically by Z3. Finding the needed steps in the proof
can be a process of trial and error. If we failed to prove a lemma, we break it into
smaller steps.

Also, notice that we used an 'isolate' to help structure the proof.
This allowed us to say in the 'with' clause that the proof of all
the subgoals should apply the full definition of `dvds`. This is
safe in terms of decidability because the definition has no
quantifiers, and we only apply `dvds` to ground terms.



```
isolate sqrt2irrat_iso = {
    theorem [sqrt2irrat] {
        individual a : nat
        individual b : nat
        property a > 0 & b > 0
        property [co] gcd(a,b) = 1
        property squared(a) = 2 * squared(b)
        property false
    }
    proof {
        property [prime2] prime(2) proof {
            unfold with prime,commdiv,dvds
        }
        property [a2_even] dvds(2,squared(a)) proof {
            unfold with dvds_alt
            instantiate with Z=squared(b)
        } 
        instantiate [dp1] prime_square with a=a,b=2:nat,prem1=a2_even
        unfold dp1 with dvds_alt
        tactic skolemize
        property squared(a) = 4 * squared(_Z) proof {unfold with squared}
        instantiate [dp2] prime_square with a=b,b=2:nat
        instantiate dvds_gcd with a=a,b=b,c=2:nat
    }
} with nat,dvds

```
