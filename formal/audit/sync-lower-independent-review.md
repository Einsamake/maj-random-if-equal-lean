# Independent semantic review: original synchronous quadratic lower bound

2026-10-25. Reviewer: `/root/sync_profile_review`. I authored none of the four modules reviewed below. I read all four frozen sources, the actual physical-bound and clock/grid comparison definitions, the original perturbation-distance and homogeneous-recovery definitions, and the current complete validation record. This is an independent AI review, not a human expert certification or a new full-theorem proof.

**Conclusion: PASS for the stated lower-bound scope.** No mathematical/model/quantifier defect was found in these four sources. The original synchronous quadratic upper bound and complete Theta theorem remain unproved.

## Frozen sources and exact scope

- `SyncLowerScale.lean`: SHA256 `d4ea9c03054c76c0bf00b2756b2acc0002f97fee430376f0316c7ed65d59e6ad`; 9 theorems and 2 definitions.
- `ExtendedTailLower.lean`: SHA256 `69d9f37c4ab4e1c5eefaade5ac5d43332aba4891708957ef31a9da19944a9ccb`; 3 theorems.
- `SynchronousQuadraticTail.lean`: SHA256 `f72c764b9663455b26b4e87640a45d806ee85d564c1d88fb6af21e015c5c2331`; 3 theorems.
- `OriginalQuadraticLower.lean`: SHA256 `b5ab0c112b66d5b5f3afd17ded75dbc28e884d123e51eadafaf0f71ab9068752`; 11 theorems and 1 definition.

The 26 new theorems and 29 named declarations prove an eventual original exact-N worst extended-expectation lower bound. They do not assert a finite expected recovery time, an upper bound, or exact asymptotic constants.

## 1. Deterministic scales are actually discharged

K=12288000, D=196608000=16K. For L>=D, quotient=floor(L²/D) and rounds=quotient−1 are genuine natural numbers. The source proves quotient>=L and rounds+1=quotient before eliminating subtraction; no floor or positivity assumption is smuggled into the final probability theorem. The estimate rounds>=L²/393216000=L²/(32K) retains the actual round count.

The scheduling horizon is exactly `8*log(2)*(rounds+1)`. The source uses log(2)<=1 and quotient*D<=L² to prove it is no later than the previously proved physical horizon L²/K. It does not identify physical clock time with synchronous rounds. The exponential scheduling estimate is proved via induction from `64*L²<=2^L` and the actual finite side `parameter L+2=2L+1`; its final error is <=1/4, with no error-bound parameter.

## 2. The clock-to-synchronous direction and law are correct

`PhysicalAreaTail.law L` is `ClockWordMarks.measure (parameter L)`. `SquarePWMeasure.topConfig` is definitionally `fun _=>true`. Consequently the physical extinction endpoint and `ClockRecoveryComparison.clockProbability` refer to the same rate-one clock/fair identity-mark product law, not merely similar models.

`clockProbability_eq_one_sub_extinction` uses the actual measurable endpoint singleton and probability complement theorem. `original_clock_survival_ge_half` does not assume CDF monotonicity: it instantiates the already proved actual linear-time extinction bound at the earlier requested time, then bounds its nonnegative linear numerator by the proved half-threshold. This retains first-loss freezing and all weighted cleanup corrections through the imported proved bound.

The final synchronous tail uses `SquareGridLaw.two_way_clock_tail(...).1`, which states clock survival <= synchronous tail + actual scheduling error. Together with clock survival>=1/2 and error<=1/4 this gives synchronous survival>=1/4. The opposite comparison conjunct is not used. The law is the original infinite-grid synchronous mark field, and its time is the real natural `rounds L`.

## 3. The extended expectation preserves infinity

`tail_mul_le_expectation` integrates a measurable constant indicator directly against `T.toENNReal`; on the survival event k<T it uses k<=T and the monotone ENat-to-ENNReal conversion. Outside the event the integrand is zero. No `toNat`, finite-time representative, Bochner recovery expectation, integrability premise, or almost-sure finiteness appears.

The quarter-probability step requires only finite event mass so `ofReal(measure.real event)=measure event` is legitimate. It does not infer finiteness of the recovery expectation. Infinite T contributes infinity, as required.

## 4. Both parities and the original exact-N quantity are connected

For every N>=786432000=64K, `halfSide N=(N−1)/2` is at least 16K; the odd side 2*halfSide+1 is <=N, and N/6<=halfSide is proved. `inside_mono` and `square_supported_mono` compare the actual half-open squares with integer coordinates. `extend_top_eq_square` identifies the finite top square with `squareConfig(n+2)` without changing its side.

The smaller odd square's tail is transported to the N-square with the existing `supported_tail_le_top`; no unproved monotonicity of the exact-size supremum is used. The half-open square side is the original minimum translated axis-parallel containing-square size, not black-cell count or half-width.

The source proves homogeneous recovery equals zero-background recovery on this supported square via the existing samplewise theorem. Thus the tail-to-mean theorem applies to the genuine first hit of either homogeneous state, with infinity retained. Since rounds/4>=N²/56623104000, the conclusion is

    ofReal(N²/56623104000) <= expectedRecovery(squareConfig N).

The last step is `square_expectedRecovery_le_tau N`, whose witness is the already proved `distance_square N`: the optimization uses size EXACTLY N. The existential theorem supplies c=1/56623104000>0 and finite threshold 786432000, with only N>=threshold as its final premise. It is the lower half of the intended Theta theorem.

## 5. Actual validation and evidence boundary

The current unified record is `analysis-validation.json`, validated at 2026-10-25T15:11:55.361456+08:00: real analysis build exit0 and standard Lean `--trust=0` axiom audit exit0, 2826 analysis theorems and 213 analysis sources. Three named stage audits separately cover all 29 new named declarations (11+6+12). The core's old 125 theorems plus one model definition are reused only after rechecking all eight core source hashes; the core was NOT rebuilt in this phase.

A separate independent binding script verifies the complete 221-source set/SHA, every actual global axiom-output name and order (2952 outputs, including apostrophe-containing names), source-derived theorem names, all stage tables/output names and source hashes, standard axiom sets and real zero exits. Its result is `sync-lower-independent-final-binding-evidence.json`. This report does not replace those actual logs, and neither report establishes independent novelty or human expert acceptance.

The remaining main mathematical task is a self-contained original synchronous quadratic upper bound. Existing restart only propagates a genuine one-block success bound; it cannot supply that bound. The candidate finite mixed-boundary exclusion route in `formal/drafts/UpperFiniteSEPRoute.md` is separate, unproved future work.
