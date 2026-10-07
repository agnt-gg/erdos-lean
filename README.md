# Erdős problems in Lean 4

Kernel-checked Lean 4 proofs of results about [Erdős problems](https://www.erdosproblems.com).

## Erdős Problem 552: $R(C_4, K_{1,n+1}) \le R(C_4, K_{1,n}) + 2$

[Erdős Problem 552](https://www.erdosproblems.com/552) concerns the Ramsey number
$f(n) = R(C_4, K_{1,n})$. Burr, Erdős, Faudree, Rousseau and Schelp asked whether
$f(n+1) \le f(n) + 2$ for all $n$. Chen Guantao proved this
(*A result on $C_4$-star Ramsey numbers*, Discrete Math. 163 (1997), 243–246).

[`Erdos/Erdos552.lean`](Erdos/Erdos552.lean) proves it for every $n \ge 1$:

```lean
theorem erdos_552.variants.succ_le_add_two (n : ℕ) (hn : 1 ≤ n) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (completeBipartiteGraph (Fin 1) (Fin (n + 1))) ≤
      SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (completeBipartiteGraph (Fin 1) (Fin n)) + 2
```

`SimpleGraph.graphRamsey` is copied verbatim from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean`), so the statement is the one
used there. The bound fails for $n = 0$: $R(C_4, K_{1,1}) = 4$ and $R(C_4, K_{1,0}) = 1$.

### Proof

Let $N = f(n)$ and let $H$ be a $C_4$-free graph on $N + 2$ vertices. Two distinct vertices of $H$
have at most one common neighbour.

- If some pair $x \ne y$ has no common neighbour, delete it. The remaining $N$ vertices contain a
  vertex $w$ with at least $n$ non-neighbours, and $w$ is not adjacent to both $x$ and $y$. So $w$
  has at least $n + 1$ non-neighbours in $H$.
- Otherwise every pair has exactly one common neighbour. By the friendship theorem
  (Mathlib, `Archive/Wiedijk100Theorems/FriendshipGraphs.lean`) some vertex $p$ is adjacent to all
  others. Every other vertex has degree at most $2$, so it has at least $N - 1 \ge n + 1$
  non-neighbours, using $N \ge n + 2$.

The file also proves that the defining set is nonempty ($2n + 2$ vertices suffice) and that
$f(n) \ge n + 2$ for $n \ge 1$ (a star has no $C_4$ and its complement has degrees below $n$).

## Check it

```bash
lake exe cache get   # prebuilt Mathlib
lake build
```

The build prints `[propext, Classical.choice, Quot.sound]` for the axioms of the theorem. There is
no `sorry` and no custom axiom. Tested with Lean `v4.33.1` and Mathlib `v4.33.1`
(commit `0df444a360eaa60ab8c11dca51a86af692955474`, the version used by formal-conjectures), with
warnings treated as errors. Removing the hypothesis `1 ≤ n` makes the proof fail, as it must.

## Authors

Nathan Wilbanks and Annie (AGNT Labs). The theorem is due to Chen Guantao (1997); this repository
gives a formal proof.

## License

Apache License 2.0. See [LICENSE](LICENSE).
