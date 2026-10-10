This standalone Lean 4 project formalizes the binary Klein-four membership
criterion in Theorem 1.1 of `klein_four_generation_v4.tex`. Its primary statements
are `KleinFour.membership_iff`, `KleinFour.membership_iff_orbits`,
`KleinFour.membership_card`, and `KleinFour.lazy_membership_card`. The generated
monoid has 59,712 elements; the lazy-only monoid has 4,007 elements.

The project pins Lean to `leanprover/lean4:v4.33.0` and Mathlib to `v4.33.0`
(commit `db584cd6d46c92f209a44c0f1c829460d327499d`), matching the versions requested
in `TASK.md`. `lake-manifest.json` pins all transitive dependencies.

Build and inspect the proof dependencies with:

```sh
lake exe cache get
python3 scripts/check_lazy_blocks.py
lake build
lake env lean Audit.lean
```

The block script builds the finite certificate modules one at a time and records
their PIDs. A fresh certificate verification takes about a minute per block on
the task machine; there are 63 blocks. Subsequent builds reuse Lake's checked
artifacts. Running the block script before `lake build` keeps the large finite
checks sequential on a fresh checkout.

The group is `G = Bool × Bool`, with exclusive-or multiplication `gm` and identity
`e = (false, false)`. Its associativity, identity, commutativity, and self-inverse
laws are proved. `Bits = G → Bool` is the actual binary configuration space. The
inductive type `X` has the two constants, three two-point orbits, and two free
orbits. `configurations : X ≃ Bits` is an explicit, proved equivalence, and
`encode_act` identifies the action on `X` with `(g • x)(h) = x(hg)`.

In `X.f b g`, `b = false` describes the singleton with its one at `g`, and
`b = true` its complement. `weight_free` verifies weights one and three;
`weight_pairs` verifies weight two. In `X.p s b`, the orbit indices `0, 1, 2`
correspond to the subgroup generators `(false, true)`, `(true, false)`, and
`(true, true)`, respectively. The second parameter distinguishes the two
complementary configurations in that orbit.

`CA` is the full monoid of equivariant functions `X → X`, with right-to-left
composition. It is not a restricted family of prescribed generators.
`tables : CA ≃ Table` proves that arbitrary equivariant maps are exactly the
independent choices on the seven orbit representatives. `localRules` also gives
the equivalence with all binary local rules `X → Bool`. The inverse is `ofRule`;
the theorem `rule_reconstruction` proves the local-rule reconstruction.

`ICA` consists of the equivariant bijections. `L` consists precisely of
`lazyMap S p` for neighborhoods containing `e`. Its coordinate formula is proved
in `global_lazy`: a pattern match flips the central binary symbol, and all other
central symbols are retained. This is Definition 2.1 of the note. Symbols in
`p` outside `S` are ignored, so use of full configurations to represent patterns
does not constrain the definition. `M` is literally
`Submonoid.closure (ICA ∪ L)`; it includes the empty product.
The lazy-only monoid `D` is `Submonoid.closure L`, also including the identity.

The following statements are fully proved:

| Lean statement | Mathematical content | Note reference |
| --- | --- | --- |
| `decode_encode`, `encode_decode`, `encode_act` | Concrete configuration equivalence and translation action | §2 |
| `ca_tableOf`, `tableOf_ca`, `ca_card` | All equivariant maps are represented; there are 65,536 | Lemma 2.2 |
| `global_lazy` | Exact coordinate definition of lazy maps | Definition 2.1 |
| `constantCollapse_mem`, `pairCollapse_mem`, `freeCollapse_mem` | Every allowed elementary collapse into a lower orbit is generated | Lemma 2.4 |
| `lowerMap_mem`, `nonmerge_mem` | Every nonmerging automaton is generated | Proposition 2.5, reverse inclusion |
| `lazy_criterion_check`, `criterion_mul` | All lazy generators satisfy the criterion; the criterion is closed under composition | Lemmas 3.1–3.2 |
| `merge_factor` | Explicit merging factorization `T = R * B_s * α` | Proposition 3.3 |
| `membership_iff`, `generated_eq_criterion` | Membership is equivalent to the criterion | Theorem 1.1 |
| `membership_iff_orbits` | The same equivalence in literal orbit-image language | Theorem 1.1 |
| `membership_card` | `Nat.card M = 59712` | Theorem 1.1, Proposition 4.1 |
| `lazy_membership_card` | `Nat.card D = 4007` | Proposition 6.3, cardinality part |

The main membership proof follows the structural argument. For the forward
direction, `criterionSubmonoid` contains the generators and is closed under
composition. The reverse direction uses an explicit partial-permutation
normalizer and elementary collapses for nonmerging maps, and the note's
three-factor construction for merging maps. It does not enumerate 59,712
generator words.

Small finite identities are proved with kernel-checkable `decide`: the group
and configuration identities, the neighborhood/pattern family, elementary
conjugations, and identities involving the two free representative images.
The count splits the choices into 256 lower restrictions and 256 free
restrictions. There are 224 nonmerging free restrictions, 32 merging ones,
and 74 lower restrictions supplying a witness. A proved equivalence partitions
the satisfying maps, giving `256 * 224 + 74 * 32 = 59712`. Each computed counting
factor has at most 256 cases.

`Audit.lean` runs `#print axioms` on the main results and supporting definitions.
No project theorem uses `sorry` or `native_decide`, and no additional axiom is
declared. The exact printed dependencies are preserved in `axioms.log` after
validation.

The lazy-only cardinality uses a parent DAG: one preceding member and one lazy
generator for every nonidentity candidate. The validator checks the parent
equations, strict descent of parent indices, a left inverse for the candidate
enumeration, and closure under every lazy generator. A separate proved check
identifies the 54-entry generator family with the full definition of `L`.
The structural reflection argument proves reachability, completeness, and
distinctness, yielding an equivalence with `Fin 4007`. All 63 Boolean certificate
blocks are proved using ordinary kernel-checkable `decide`.
`lazy_membership_card` instantiates the reflection theorem with these checked
proofs and has no certificate hypotheses.

Candidate data is reproducible from the repository root with the restored
[certificate generator](experiments/generate_lazy_certificate.py):

```sh
python3 experiments/generate_lazy_certificate.py --check
```

This command checks that the untrusted enumeration regenerates the committed
`KleinFour/LazyData.lean` byte for byte. In `--check` mode it does not write that
file or run Lean; the Lean proofs establish its mathematical validity.
The separate BFS programs, independent checker, and instructions for reproducing
Section 6 and Table 1 are in [experiments/README.md](experiments/README.md).

The shortest-word distributions and maximal lengths, the size of the semigroup
of nonempty lazy compositions, the weaker invariant's counts, the relative-rank
theorem, and the maximal-submonoid theorem are not formalized. These separate
results of the note are not assumed by the membership proof or either count.

Build PIDs and exits are recorded in `jobs.txt`. The wrapper
`scripts/job.py` keeps the launched process attached and records its exit;
validation logs are retained locally. All project edits are in this directory.
