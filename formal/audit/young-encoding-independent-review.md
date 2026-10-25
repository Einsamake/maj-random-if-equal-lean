# Independent semantic review: finite Young diagrams and actual adjacent particle moves

2026-10-25. Reviewer: `/root/sync_profile_review`. I authored none of the five reviewed Lean modules. I read their source and the actual imported row-filter, mixed-boundary and corner-update definitions. This is independent AI review, not a human expert certification.

**Semantic conclusion: PASS for the stated deterministic scope.** The sources give a genuine two-sided encoding between coordinate-monotone Boolean squares and ordered M-particle positions in 2M slots, exact white-diagonal/right-half tests, actual single-corner particle swaps, and converse coverage of every admissible adjacent empty-slot hop by a real mixed-boundary corner. They do not yet give a full clock/exclusion law, an exact rate-summed generator identity, actual moment evolution, or a quadratic upper bound.

## Reviewed source snapshots

- `YoungParticles.lean`: SHA256 `ec769948d2d03100d2337b1c4c2cf44aaeeec7d8f4525cb370def055c793a85b`; 16 theorems and 5 definitions, 21 named declarations.
- `YoungRowUpdates.lean`: SHA256 `558e07bb40a9b8b11a5b6d880a2836c265baa102656dad41836b61f8facbad80`; 13 theorems.
- `YoungParticleInverse.lean`: SHA256 `4ba832b67dad4313943db3c9199e3134e56100dbb978db00fd25a7b4eada51d9`; 14 theorems and 4 definitions, 18 named declarations.
- `YoungParticleMoves.lean`: SHA256 `65f5b6efd9f9799fd2d342d9245bab366cb5da9b022af5b895dc7acbbadf953d`; 16 theorems.
- `YoungParticleHops.lean`: SHA256 `cbb75e17575148b7e9fdd2bfb844c50094b78f48badd796d661eeaac25423666`; 8 theorems.

These total 67 theorems and 76 named declarations. Actual named/global compilation and standard-kernel outputs are checked separately in `young-encoding-independent-final-binding-evidence.json`. This review does not restart Lean, infer a completed global build from a pending process, or certify the subsequent `FiniteExclusionGenerator` draft.

## 1. Actual rows encode actual finite occupied slots

For a side-M Boolean square, false means white. The existing `rowLength f y` counts a genuine finite filter, not an assumed partition. The particle labelled r is placed at

    p_r = r.val + rowLength f r.rev

in `Fin(2*M)`. The row-length bound proves p_r<2M, including a full white row. With coordinate-monotone f, reversing rows makes their lengths nondecreasing in the label, so p is strictly increasing and therefore injective. Consequently the actual occupied-slot image has exactly M members. The encoding-injectivity theorem recovers all actual row lengths, then uses their already proved unique reconstruction.

All-true gives exactly the left M slots; all-false gives exactly the right M slots. Both include the correct endpoints. No equality between particle occupation and the original spin value is assumed: particles encode vertical path steps/row offsets, while white cells are original false spins.

`rightCount` initially counts LABELS satisfying p_r>=M. This is correctly described as a labelled count, not silently treated as a slot-filter cardinality for an arbitrary nonmonotone input. The final `YoungParticleMoves.rightCount_eq_rightSlotCard` closes that interface explicitly under Monotone f, using a true cardinality bijection from labels to occupied right-half slots and the proved particle injectivity. Thus the J observable is now the number of genuinely occupied right slots for every valid encoded shape.

## 2. Diagonal and side-N thresholds are exact

The right-half condition p_r>=M is equivalent to the actual diagonal cell `(r.rev,r.rev)` being false, using `Fin.val_rev` and the proved initial-segment row characterization. Reversing row labels is a genuine bijection, so rightCount equals the actual false-diagonal cardinality.

The diagonal is itself monotone. Therefore the zero-based test is exactly

    f(d,d)=false <-> d.val < rightCount f.

The human side-N test uses the actual cell `(N−1,N−1)` and is exactly `N<=rightCount`; it explicitly assumes `1<=N<=M`. This avoids treating Nat subtraction at N=0 as a physical cell. No probabilistic estimate is substituted for this deterministic threshold.

For M=0 all row/particle/cell indices are empty. The image and filtered counts are empty, and statements with indexed cells/particles are vacuous. The construction does not manufacture a nonempty empty-square row or divide by M.

## 3. The inverse has proved bounds, not extra reconstruction hypotheses

For an arbitrary strictly increasing p:Fin M→Fin(2M), interval-image injections prove

    r<=p_r<=r+M

and monotonicity of p_r−r. These facts are derived from strict order and the true finite slot bounds; they are not additional partition assumptions. The decoded row length is `(p y.rev).val−y.rev.val`. The lower bound ensures that the subtraction is never silently truncated, and the upper bound gives the actual side-M row bound.

`fromRows` sets a cell true exactly after its row threshold. Antitone thresholds give a spatially monotone square. The source proves its exact row cardinality both for lengths<M and lengths=M. It then proves both compositions: decoding the actual particle positions returns f for every monotone f, and encoding a decoded strictly increasing p returns the very same p. `encodingEquiv` is consequently a genuine equivalence of the explicitly stated subtypes, including M=0.

This equivalence is between monotone spin fields and ordered labelled positions. It is not a claim of a random-process law or a completed finite-state Markov equivalence.

## 4. Actual mixed corner updates change exactly the correct row

The generic row-write lemmas prove actual insertion/erasure of the selected column in the zero filter. Writing false over an old true increases its cardinality by one. Writing true over an old false gives `newLength+1=oldLength`; this plus-one form handles empty/full row boundaries without an invalid Nat predecessor.

The mixed-corner instances use the actual rule and supplied false/true marks, rather than assuming the requested updated value. All other rows are unchanged even for a general single write. Combining old and newly proved monotone row characterizations yields the exact selected column: x=old white length for a removable true corner, and x+1=old white length for an addable false corner. Since the argument uses actual mixed shape preservation, exterior corners are not omitted by a false interior-neighbour assumption.

## 5. A real corner flip moves one particle into a genuinely vacant adjacent slot

The changed label is the reversed selected row, r=v.2.rev. Every other label remains in its original slot. A false-mark removable update moves its position right by one; a true-mark addable update moves it left by one, expressed as `newPosition+1=oldPosition` to avoid Nat underflow.

Destination vacancy is a conclusion: if the new slot had an old labelled particle, the unchanged-other-label identities and injectivity of the NEW monotone shape would force that other label to equal r. The remaining case contradicts the proved nonzero displacement. Thus neither vacancy nor a geometric/probability bound is smuggled into these forward transition theorems.

The actual occupied set is exactly insert-new after erase-old. With old membership and new vacancy, the finite-set swap lemma then proves it is precisely the image under `Equiv.swap old new`. The previously proved position equations make these two swapped slots adjacent. Both reverse directions of tie motion remain present; no accelerated permanent deletion is used.

## 6. Every admissible finite-path hop has an actual mixed corner

For a right hop, the hypotheses are the real finite target bound p_r+1<2M and absence of ANY labelled particle there. When a southern row exists, vacancy excludes equality of the two row lengths and forces a strict southern gap. At the southern boundary the finite path endpoint instead rules out a full selected row. Hence x=the row length is a valid column; the old cell is true and its actual south/west inputs are false, using real SW boundary values where necessary.

For a left hop, the real condition p_r>0 and `forall s, p_s+1 != p_r` express the vacant predecessor without truncated subtraction. A northern row, when present, has a strictly smaller white length; at the top boundary the finite path endpoint forces positive selected-row length. Choosing x=length−1 gives a valid old false cell with actual north/east inputs true, including the real NE boundary cases.

The final existence theorems return the required reversed row, exact column endpoint and genuine corner predicate. Together with the forward move identities this gives both directions of deterministic local transition coverage. The explicitly returned row and column determine the vertex; a future rate-sum reindexing must still prove and use its needed injectivity/uniqueness and any slot/label membership conversions.

## Remaining boundary

These results do not prove that actual clocks attached to changing grid corner locations can simply be renamed independent fixed path-edge clocks. They do not supply a rate-1/2 generator identity or actual Dynkin/moment equations. A valid next step may use the existing actual-grid compensation and a proved exact finite generator reindexing, avoiding a stronger full path-clock law, but that connection is still future work. Cross-size clock restriction, heat/covariance estimates and the final original synchronous quadratic upper bound also remain unproved.

The separate final-binding artifact verifies the frozen source sets/SHA, actual printed names/order, all named stage records and the unchanged earlier lower/mixed/YoungRows/core sources. This report leaves all earlier bindings untouched. It does not certify human-expert agreement, novelty or the complete Theta theorem.
