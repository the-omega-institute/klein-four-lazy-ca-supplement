# Exact enumeration for the binary Klein four-group

These programs and tables reproduce Section 6 and Table 1 of
*Generation by lazy and invertible cellular automata over the Klein four-group*,
v5. They operate on the finite universe of 65,536 cellular automata with exact
integer operations. The BFS and independent checker do not invoke Lean or Lake.

## Files

| File | Purpose |
| --- | --- |
| `compute_klein_closures.cpp` | C++17 BFS from the identity using all 54 lazy maps, then all 54 lazy maps and all 512 units; replays every emitted word. |
| `verify_klein_closures.py` | Independent NumPy reconstruction and exhaustive certificate, closure, distance, and Section 6 checks. |
| `lazy-membership.csv` | All 65,536 rules, membership in the lazy-only monoid, shortest lengths, parent links, and complete shortest words. |
| `units-lazy-membership.csv` | The same information for the mixed monoid. |
| `lazy-generators.csv` | The 54 neighborhood/pattern pairs and their rule numbers, independently checked by Python. |
| `closure-summary.json` | BFS counts, including the historical weaker invariant and the nonempty-product identity check. |
| `closure-independent-verification.json` | Current independent check results, distributions, edge counts, and comparison with v5 Table 1. |
| `table-1.csv` | Table 1 derived from the independently verified membership rows. |
| `SHA256SUMS` | SHA-256 hashes of the six deterministic data/report files. |
| `generate_lazy_certificate.py` | Recovered generator for the existing Lean candidate data; use `--check` from the repository root. |
| `requirements.txt` | NumPy dependency for the independent checker. |

## Reproduction

Use a C++17 compiler, Python 3, and NumPy. The checked environment was macOS arm64,
Apple Clang 21.0.0, Python 3.14.4, and NumPy 2.5.2. To install the Python dependency
in an isolated environment, run from the repository root:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r experiments/requirements.txt
```

Then run, still from the repository root:

```sh
mkdir -p experiments/build
c++ -std=c++17 -O2 -Wall -Wextra -pedantic experiments/compute_klein_closures.cpp -o experiments/build/compute_klein_closures
(cd experiments && ./build/compute_klein_closures)
python3 experiments/verify_klein_closures.py
(cd experiments && shasum -a 256 -c SHA256SUMS)
python3 experiments/generate_lazy_certificate.py --check
```

The BFS writes to its current working directory; the `cd experiments` is required.
The Python checker reads and writes beside its own source file, so the command
above works from the repository root. The programs use assertions for validation:
keep them enabled. The C++ program rejects `-DNDEBUG`; the checker rejects Python
`-O` and `-OO`. A failed assertion or file error makes the command fail.

The BFS prints:

```text
lazy: size=4007, max_shortest_length=6
lazy: length_distribution=1 54 678 1894 1218 156 6
units-lazy: size=59712, max_shortest_length=6
units-lazy: length_distribution=1 565 8806 27424 19004 3870 42
Invariant: 61440; missing=1728; violations=0; identity nonempty=0
```

The checker prints a JSON report with `failures: 0` and
`paper_v5_table_1_matches: true`, followed by:

```text
Table 1. Numbers of elements at each shortest-word length.
Length k | l_L(T)=k | l_(U union L)(T)=k
0 | 1 | 1
1 | 54 | 565
2 | 678 | 8,806
3 | 1,894 | 27,424
4 | 1,218 | 19,004
5 | 156 | 3,870
6 | 6 | 42
Total | 4,007 | 59,712
```

These are exactly the v5 Table 1 entries. The mixed generator set contains 566
maps, including the identity, so it has 565 elements of shortest length one.
The lengths refer to the full generator sets, as in Remark 6.4.

## Encoding and table conventions

Cells `(e, a, b, ab)` are numbered `0, 1, 2, 3`; multiplication is bitwise XOR.
A configuration `x` is a four-bit integer with bit `g` equal to `x(g)`.
Rule `r` is a sixteen-bit integer whose bit `x` is the output at `e` on `x`.
For a translated configuration `shift(x, g)`,

```text
shift(x, g) has bit h equal to bit (h XOR g) of x
T_r(x)(g) = bit shift(x, g) of r
```

This is equation (8) in v5. The identity rule is `43690`.

Both membership CSV files have the columns:

```text
rule_id,member,shortest_length,predecessor_rule,generator_rule,application_order_generator_word
```

There is one row per rule, in increasing rule order from `0` to `65535`, including
nonmembers. `member` is `1` or `0`. Nonmembers have shortest length `-1`, predecessor
`-2`, generator `-1`, and an empty word. The identity is a member of length zero
with predecessor and generator `-1` and an empty word. Every other member has a
parent of length one less and a last generator satisfying
`T_rule = T_generator composed with T_predecessor`.

The word is a quoted, space-separated list of decimal rule numbers **in application
order**: apply the first rule first, then the second, and so on. Thus a word
`g1 g2 ... gk` represents `T_gk composed with ... composed with T_g1`.

In `lazy-generators.csv`, `neighborhood_mask` contains bit zero (the identity
cell), and `active_pattern_bits` is supported on that neighborhood. A match
flips the central bit; every other local pattern keeps it.

## Independent verification and Section 6

The Python checker regenerates all global maps from equation (8), identifies
units by distinct global images, and independently regenerates all lazy local
rules. It neither imports the BFS implementation nor uses its summary as evidence.
For each membership table it checks:

1. Every rule occurs once, the identity has distance zero and the empty word,
   and every other member has a valid parent equation with distance one less.
2. Every saved word is the parent's word followed by the saved generator and
   has the reported length. Strictly decreasing parent distances terminate at
   the empty identity word, certifying the complete word by induction.
3. Every member is closed under every left generator, and every resulting edge
   satisfies `d(generator * rule) <= d(rule) + 1`.

The word certificates prove reachability. Closure proves that no reachable rule
is missing. The distance inequalities along any word, starting at zero, prove
the reported distances are minimal. Together these establish exact membership,
nonmembership, and shortest lengths throughout the finite universe. The checker
examines 216,378 lazy edges and 33,796,992 mixed edges.

It also checks Lemma 6.1's 54 distinct noninvertible lazy maps, verifies that the
nonempty lazy products are exactly the 4,006 members other than the identity,
and checks Proposition 6.2's no-swap conditions on every lazy member and their
count of 19,360 inside the mixed monoid. All Table 1 entries, totals, and maxima
are checked against v5. The historical weaker invariant in the C++ summary has
61,440 satisfying rules and 1,728 rules outside the mixed monoid; it is a separate
calculation from the no-swap count.

## Lean certificate and recovery provenance

The certificate generator is copied unchanged from the original Lean workspace.
From the repository root:

```sh
python3 experiments/generate_lazy_certificate.py --check
```

Expected output:

```text
Candidate certificate: 4007 members, 54 generators; 467105 bytes
```

This compares with the committed `KleinFour/LazyData.lean` and leaves it untouched.
Running the script without `--check` writes that file; no rewrite is needed to
reproduce the supplement. The Lean sources, pinned dependencies, and build
procedure are unchanged. The word-length distributions are independently
checked computations and are not part of the Lean formalization.

The BFS, independent checker, and three original CSV tables were recovered from
the computational bundle dated 2026-10-03, `klein-four-closure-data.zip`, SHA-256
`4e3d84f90801bb67707c935264ee4360f67463c8987fbdea92dd12d6538d2c85`.
Regeneration reproduces all three original CSV files and `closure-summary.json`
byte for byte. The restored programs add explicit root/word checks, Section 6
checks, distribution reporting, and validation guards; the BFS search order and
certificate encoding are preserved.
