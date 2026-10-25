# Independent semantic review: exact finite exclusion generator and path Poincare bound

2026-10-25. Reviewer: `/root/sync_profile_review`. I authored none of the three reviewed Lean modules. I reread the final source snapshots below, including every relevant finite-sum parenthesis and the real mixed-square/particle definitions. This is independent AI review, not human expert certification.

**Semantic conclusion: PASS for the stated algebraic scope.** The actual finite mixed-square fair update operator is exactly reindexed into a once-listed adjacent-swap path generator. The one/two-point product defect and an explicit finite-path Poincare inequality are proved algebraically. No actual time-dependent moment equation, covariance sign, stochastic heat estimate or recovery upper bound is proved by these sources.

## Frozen source snapshots and counts

- `FiniteExclusionGenerator.lean`: SHA256 `dc32258b39e706e52b3c239d0ca55df6e79c4599dd7938aa853bb7b985a6302f`; 12 theorems and 7 definitions/abbreviations, 19 named declarations.
- `FinitePathPoincare.lean`: SHA256 `d535b6583f18566e9b9bd15a5bdd11eec26e56e0e43911589e58df41606e375b`; 9 theorems and 2 definitions, 11 named declarations.
- `MixedExclusionGenerator.lean`: SHA256 `38ad02176c9bcb8a3daa6112e96198c6c085b1de35bac2e6ba36a8a1727cc931`; 16 theorems, 6 definitions, 1 abbreviation and 1 named Decidable instance, 24 named declarations.

Total: 37 theorems and 54 named declarations. The named/global build, standard `--trust=0` outputs, exact source sets/SHA and printed-name orders are independently bound in `exclusion-independent-final-binding-evidence.json` after the actual root validation completes. This review launches no duplicate Lean build and does not convert a pending process into a completed validation claim.

## 1. The generic finite operator counts exactly what its edge set lists

`FiniteExclusionGenerator.generator E F eta` is literally the sum, over each listed ordered tuple (a,b) once, of `(F(eta composed with swap(a,b))−F(eta))/2`. The subtraction is inside a parenthesized summand before division. E is an arbitrary finite tuple set; adjacency is imposed only by the later actual path specialization. Including both orientations doubles that bond's rate, and a self-loop acts identically and contributes zero. Nothing silently turns a directed set into an undirected set or divides by the volume.

The Boolean density is the actual real 0/1 occupation. Permuting its finite indices preserves the literal total count, so the total-density generator is zero. Linearity and the one-point observable identity follow from finite sums. The two-point identity uses ONE AND THE SAME edge swap on both coordinates, retaining their interaction. It does not assume independent motions of the two indices.

The `twoParticle` operator is defined even on a nonsymmetric two-index real field, where an edge connecting i,j exchanges (i,j) with (j,i). That is its explicit simultaneous-swap definition; it is not an assertion that labelled particles can pass independently through one another. Actual density products are symmetric, and the algebraic observable identity is correct.

## 2. The product source has the correct sign and distinct-index condition

For i!=j, each connecting tuple contributes `(rho_i−rho_j)^2/2` to

    (Q rho)_i*rho_j + rho_i*(Q rho)_j − Q2(rho tensor rho)_(i,j).

Other tuples contribute zero. Summing gives exactly that square divided by two times the actual cardinality of the connecting-tuple filter. Both orientations, if supplied, are counted by that cardinality; self-loops cannot connect distinct indices. The final nonnegativity theorem is an algebraic sign only.

If genuine first/second moment equations are subsequently proved, covariance c=m−rho tensor rho would have source MINUS this nonnegative defect. The current sources do not prove those moment equations or c<=0. A later maximum-principle argument must restrict to distinct pairs: diagonal covariance is generally rho_i(1−rho_i)>=0. Simultaneous swaps preserve distinctness, so such a restriction is available but still needs its actual formal connection.

## 3. Actual mixed corners and unequal path bonds are in bijection

Let M=n+2 be the actual mixed-square side. Its slot type has exactly 2M positions. `pathEdges` consists precisely of ordered tuples with left.val+1=right.val. Thus every nearest-neighbour bond is listed only left-to-right once, with no self-loop or wrap-around bond. The underlying mixed rule remains southwest boundary false and northeast boundary true.

`slotState` is the literal Boolean characteristic of the actual encoded occupied-slot set. A removable old-true corner maps from its old particle slot to its new right neighbour. An addable old-false corner maps from its new left neighbour to its old particle slot. `bond` therefore orients BOTH cases left-to-right. Proved adjacency and actual old vacancy show that each active corner maps to an existing unequal bond.

Injectivity is discharged rather than assumed. For two corners of the same kind, equality of their old occupied slots forces the same label, hence the same row; the already proved exact row endpoint then gives the same column. The two cross-kind cases would identify an old occupied slot with the other's proved vacant destination and are impossible.

Surjectivity handles both Boolean orientations of an unequal adjacent bond. If its left slot is occupied, that true old membership supplies a particle label and the right false slot gives the exact target vacancy and endpoint bound required by `right_hop_has_removable`. If its right slot is occupied, the symmetric predecessor-vacancy conditions give `left_hop_has_addable`. The actual old/new particle values then identify BOTH finite bond endpoints. There is no appeal to an assumed particle law or to a geometric counting hypothesis.

## 4. The final site-sum formula has the required parentheses and coefficient

For a monotone state, supplying the current spin as the tie mark leaves the cell unchanged. At an active corner the opposite mark gives the actual swap; at an inactive site both marks leave the state unchanged. Therefore the literal local average is zero or `(F(swap eta)−F(eta))/2`. This retains both directions of fair tie motion and does not introduce deterministic cleanup.

The FINAL source explicitly writes the complete per-vertex body in parentheses in BOTH `actual_generator_eq_exclusion` and its internal `hc` identity:

    (sum v, ((F(false-update v)+F(true-update v))/2 − F(old))).

I checked that the old-value subtraction is inside EACH vertex's summand. A preliminary draft without these full parentheses was corrected during the actual Lean check; the mathematical pre-read of that draft is not used as certification. This report binds only the final hash above. The remaining edge/corner sums also parenthesize the old/new difference before dividing by two.

A genuine `sum_bij` reindexes active corners into unequal bonds using the proved injection and surjection. Equal-occupation bonds have zero contribution because swapping equal Boolean entries leaves the whole slotState unchanged; F is an arbitrary function of occupation, not a hidden function of labels. Hence including all actual path bonds gives the exact finite generator equality with coefficient one half per bond and no extra area/time normalization.

The `active_decidable` instance only unfolds finite Boolean equalities and logical combinations, then infers their ordinary Decidable instances. It is not a mathematical axiom or a rate/probability premise.

## 5. The path Poincare inequality uses the true endpoints

`FinitePathPoincare.energy n u` sums `(u(k+1)−u(k))^2` for k in `range(n−1)`, exactly the n-vertex path edges from (0,1) through (n−2,n−1). It does not read an exterior vertex or a periodic wrap-around edge. `squareMass` sums the actual n vertex squares.

Finite Cauchy–Schwarz and telescoping bound each squared difference by n times the path energy. Under the explicit zero-sum condition, another finite Cauchy–Schwarz bound gives each vertex square <=n*energy, and summing gives

    squareMass n u <= n^2 * energy n u.

The proof of the point estimate divides only by n² after proving n>0. The final theorem separately handles n=0. At n=1 the zero-sum condition forces the sole value to zero and the edge energy is empty. Full and empty path cases therefore have their intended meaning.

This is a deterministic inequality for a real field on the natural indices of the path. It does not assume a spectral-gap theorem or a stochastic estimate. For the later 2M-slot field its constant is (2M)²=4M²; the source does not itself transport a time-dependent expectation into this field or prove heat-energy decay.

## Current proof boundary

This phase closes the exact finite rate-summed operator correspondence that was still missing from the preceding Young-encoding stage. It also supplies the deterministic product-source sign and path Poincare bound. It still lacks the mixed process's true observable Dynkin/compensation and moment equations, continuity/differentiability or semigroup arguments, heat decay under the actual law, off-diagonal covariance control, cross-size clock restriction and the original synchronous quadratic upper bound. The complete Theta theorem remains unproved.

The independent final-binding artifact checks only actual completed logs and frozen sources; it does not alter the earlier 230-source report/binding. No human-expert approval, global novelty or completed stochastic upper bound is implied.
