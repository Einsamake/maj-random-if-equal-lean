# Independent semantic review: mixed-boundary square foundations

2026-10-25. Reviewer: `/root/sync_profile_review`. I authored none of the three reviewed Lean modules. I read their final source text and the actual imported zero-boundary update, event execution, clock-word, identity-mark and endpoint definitions. This is an independent AI review, not a human expert certification.

**Semantic conclusion: PASS for the stated foundation scope.** These modules construct the intended mixed-boundary finite process, prove its corner/shape properties, and connect its endpoints to the genuine same-dimension clock/mark law. They do not prove cross-size clock restriction, a full exclusion-process correspondence, exclusion exchange rates or any quadratic recovery upper bound. The complete Theta theorem remains unproved.

## Frozen sources

- `MixedSquareModel.lean`: SHA256 `87da30c23bd77f46cd52f015921e3d8fbca31dda1ca9b82cc855958286800cd1`; 25 theorems, 5 definitions and 2 abbreviations (32 named declarations).
- `MixedSquareCorners.lean`: SHA256 `33e9dc264a68af0c6aca98e9181439e4cf5e6a0be99db9b1b7a928c81d699980`; 16 theorems and 2 definitions (18 named declarations).
- `MixedSquareClockLaw.lean`: SHA256 `43d38694baab3043d3f4962e4dffec0d5fc58f7f6f4662e1203f796181c85bd9`; 11 theorems and 2 definitions (13 named declarations).

The total is 52 new theorems and 63 named declarations. Compilation and complete axiom-output verification are recorded separately by the actual named-stage/global audit logs and `mixed-square-independent-final-binding-evidence.json`; this semantic review does not launch duplicate builds or infer success from a pending process.

## 1. Four sides, exterior corners and actual finite side

The finite vertices are `Fin(n+2) × Fin(n+2)`, so the SIDE is n+2, not n. `MixedSquareModel.extend` reads the finite state on the exact half-open integer square. Outside it, any negative x or negative y takes value false; all other exterior points take value true. Thus west/south are false, and east/north are true at the nonnegative coordinates adjacent to interior cells.

South/west priority at exterior diagonal intersections is explicit: (-1,n+2) and (n+2,-1) are false; (n+2,n+2) is true. This is consistent with monotonicity in the coordinatewise product order. An interior cell's four nearest-neighbour inputs never read one of those diagonal intersections. Consequently that priority does not change the intended local mixed boundary. The source actually proves the low/high and all four side formulas, rather than assuming a geometric boundary condition.

The rule reads north, east, south and west through this extension and calls the original `majority4`; it does not read the center or replace fair ties by strict majority. `cellUpdate` writes exactly the selected vertex. Its extension identity proves that the exterior boundary remains fixed after each finite write.

## 2. Two different monotonicities are correctly separated

State-order statements such as `extend_mono`, `rule_mono_common_mark`, `cellUpdate_mono_common_mark`, `execute_mono` and clock `endpoint_mono` compare two spin configurations pointwise, using the SAME tie mark or identity-indexed mark field.

Spatial `Monotone f` uses the componentwise order on the two finite coordinates and the Boolean order false<true. It means the false/zero cells form a southwest downset and true/one cells form a northeast upset. `extend_monotone` proves this for the full integer-grid extension, with every exterior case considered; it does not assume the extension has the desired shape.

The zero-boundary extension and every actual same-site/same-mark zero-boundary update are below the mixed ones when the initial states are ordered. Both dimensions in these statements are the SAME n. No N-to-M inclusion, probability law, censoring theorem or accelerated deletion process is hidden in this comparison.

## 3. The corner classification retains both directions of tie flips

For a spatially monotone infinite-grid state, an old true cell necessarily has true north/east inputs. It can change to false exactly when south and west are both false AND the supplied tie mark is false. An old false cell necessarily has false south/west inputs; it can change to true exactly when north and east are both true AND the tie mark is true. These are exact equivalences, not just sufficient conditions.

The source discharges the finite Boolean cases with ordinary kernel-checkable `decide`. The finite versions use the proved monotone actual mixed extension, so the same equivalences hold on boundary cells. `removable` and `addable` are actual neighbour predicates. Neither reverse tie flip is discarded; there is no deterministic majority cleanup.

`grid_update_monotone` handles a pair of comparable integer-grid points after a single write. Its strict-above/below step lemmas use the discreteness of Z² correctly. The finite result transports through the actual embedded write, with explicit Fin-to-Int coordinate casts. Induction then proves preservation for every finite identity-mark word from any monotone initial state, including the all-true and all-false finite states.

These statements identify which supplied marks cause a change. They do not yet prove a path encoding or a rate-1/2 exclusion generator from the clock/mark distribution.

## 4. The new endpoint uses the original clock/mark sample without alteration

`MixedSquareClockLaw.endpoint n t initial z` executes precisely `(ClockEventWord.word z.1 t).reverse` using `z.2`. The original word is newest-first, so the reverse is the chronological list required by `EventTrace.execute`. Every event retains its (site, arrival-index) identity, and repeated rings at one site keep their distinct marks. No mark is resampled by this definition.

The same total `ClockEventWord.word` is used by the original zero-boundary endpoint. In particular the exceptional empty-word fallback is identical, so the pathwise same-word comparison even covers exceptional samples. The construction is not replaced by a different convenient process on a null set.

`freshRun_fixedVector` reconstructs the used identity marks. It is valid even for a word with a repeated identity because reconstruction uses that identity's original mark. This lemma is used to prove measurability by a finite-vector function; it does not assert that repeated identities acquire independent marks. The actual clock word separately has proved distinct identities in the imported foundation.

The fixed-word measurable function is composed with the measurable actual clock word and mark projection. This establishes the endpoint's measurability under the existing `ClockWordMarks.Sample/measure n`. It does not by itself prove original-history adaptedness, a strong Markov property, a new word-fiber law or cross-time conditional independence; none is claimed.

## 5. Genuine same-dimension endpoint and probability comparison

`original_execute_le_mixed` inducts over the SAME event word and uses the true zero-boundary single-update comparison, so every original update is included. `original_endpoint_le_mixed` instantiates it at the actual chronological clock word for every t and sample. If the mixed endpoint is all false, that domination forces the original endpoint to be all false. Thus the original nonzero event is a subset of the mixed nonzero event, in the correct direction.

`original_nonzero_probability_le_mixed` uses this actual event inclusion under the SAME `ClockWordMarks.measure n`, with finite event mass supplied by `measure_ne_top`. There is no external probability comparison premise. It is a same-dimension, same-time probability inequality only.

`endpoint_monotone_shape` transports the already proved finite-word shape preservation. `all_times_top_shape` gives every real t on every sample because every total word preserves shape from top; this deterministic all-time property does not assert that the old globally guarded word is history-adapted.

## 6. Limits needed for the next stage

The mixed chain's all-false finite state is not absorbing: its northeast cell has true north/east boundary inputs and can return to true at a true tie. The current nonzero comparison must therefore not be sold as a mixed-chain extinction CDF or an O(n²) upper-tail theorem. The candidate route uses a smaller target sub-square in a larger mixed domain and an interior corner event; those cross-size/target-event interfaces remain to be proved.

Specifically still missing are the finite staircase/path bijection, exact local adjacent-swap correspondence, the genuine generator/moment equations under this law, cross-size restriction of clock streams and identity marks, finite heat/covariance estimates under the actual process, and the final synchronous upper-bound/restart/expectation connection. Existing lower-bound proofs and this foundation do not supply those probability estimates.

The final independent binding file checks the actual completed audit records, exact source sets/SHA, every actual global printed name/order (including apostrophe names), all three named-stage tables/logs and the core's reused source hashes. The old 221-source lower-bound review/binding remains untouched. No human-expert or novelty certification is implied.
