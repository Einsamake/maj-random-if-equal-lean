# Candidate self-contained quadratic upper bound via a finite exclusion interface

2026-10-25. **This is a mathematical plan, not a proved Lean result.** No new Lean source or build was made for this note. The route seeks only one fixed-time success probability, which the existing scheduling and restart tools can amplify. It does not reproduce the stronger FSS exponential tail.

## Primary source actually read

FSS, *Stretched exponential fixation in stochastic Ising models at zero temperature*, author-submitted mp_arc 01-287, 2001-07-25: https://web.ma.utexas.edu/mp_arc-bin/mpa?yn=01-287 . Actual PostScript: https://web.ma.utexas.edu/mp_arc-bin/mpp/fss.ps?hd=ps&la=25&lz=6221&yn=01-287 . Saved `FSS_2001_original.ps` (371565 bytes; SHA256 `353551eb6467f454a69ee5d5ce9b0afb0261b19fdb30a67a62bcc6ad46c0f2ce`), converted locally to PDF/TXT. I read §3 pp.6–8, and visually inspected rendered p.6 to verify the clock factor and coordinate statement. This is not a claim to have read/proved the whole paper. Its two-dimensional upper bound maps a quadrant interface to symmetric exclusion, then uses a finite-particle comparison, a Liggett exponential-moment comparison and a random-walk central limit estimate. Its later multiscale fixation and higher-dimensional induction are unnecessary for our target. The proposed finite-path moment argument below is my inference, not a theorem quoted from FSS.

## 1. A slower process with the correct comparison direction

Let the target original square have SIDE N, with cells indexed 0,...,N−1. Set M=8N. Consider an auxiliary square of SIDE M, with the same rate-one per-cell clocks and fair heat-bath rule; fix SOUTH/WEST exterior values to 0 and NORTH/EAST exterior values to 1. Values beyond corners are irrelevant to nearest-neighbour inputs. Start all M² interior cells at 1.

The original N-square all-one perturbation, extended by zero to the M-square, is initially <= the auxiliary configuration. Its true boundary values are all 0, also <= the auxiliary boundary values. Under common marks and per-site clocks inside M, majority4 monotonicity should prove pointwise domination at every finite event word. The original process stays supported in the N-square. Consequently, if the auxiliary cell (N−1,N−1) is 0 and the auxiliary zeros form a southwest order ideal, the whole original N-square is 0. Thus

    P(original CLOCK nonzero at t) <= P(auxiliary(N−1,N−1)=1 at t).

This uses a genuinely SLOWER auxiliary process: it has more 1s initially and extra 1 boundary conditions. No cleanup, permanent corner erasure, or state-dependent censoring is used.

A true cross-domain clock/identity-mark law transport is still required: restrict the larger square's independent site-clock streams and marks along the injective inclusion of the N-square vertices. The field definitions and product-law transport are available at the generic level, but I did not locate an existing completed finite-square CLOCK restriction theorem. It must not be inferred from the synchronous field restriction alone.

## 2. Exact finite path encoding and off-by-one conventions

In human coordinates let cells be (x,y) with 1<=x,y<=M; the corresponding actual zero-index cell is (x−1,y−1). A southwest zero ideal has row lengths

    M >= lambda_1 >= lambda_2 >= ... >= lambda_M >= 0.

Its northeast boundary is the path from (0,M) to (M,0), using M east/H steps and M south/V steps. Empty ideal is V^M H^M; full ideal is H^M V^M. Label the 2M step slots by −M,...,−1,0,...,M−1 and define occupation eta_i=1 precisely at V slots. There are always M particles, initially occupying the left half.

A local mixed-boundary majority update preserves the ideal. The only possible changes are adding/removing an ideal corner. Each has exactly two zero inputs and two one inputs, including at the domain boundary. Therefore a change occurs with probability 1/2 at its rate-one site clock: a path VH swaps to HV at rate 1/2, and conversely HV to VH at rate 1/2. This is the finite symmetric simple exclusion generator on the 2M-slot path; swaps beyond either endpoint are absent. No rate is divided by M², and no additional factor two is permitted.

Let J = sum_{i=0}^{M−1} eta_i, the number of particles in the RIGHT half of slots. Because particle count is M, the first M steps contain exactly J horizontal steps. The boundary after step M is therefore (J,J). Monotonicity of both path coordinates shows

    auxiliary human cell (N,N) is 0 <-> lambda_N >= N <-> J >= N,

for N<=M. At equality J=N the path runs on the upper/right boundary of the cell; the cell is included in the ideal. The correct actual cell is (N−1,N−1). Hence P(original nonzero at t) <= P(J(t)<N).

This encoding and all corner/boundary cases are still to be Lean proved. Generator equality is enough for the moment argument; independent physical clocks attached to fixed PATH edges need not be manufactured from the state-dependent mapping of path edges to grid cells.

## 3. Only the first and second moments are needed

Let r=2M be the number of path slots. Let Q be the reflecting path random-walk generator with each existing edge traversed at rate 1/2. Put rho_i(t)=E[eta_i(t)]. The actual generator identity should give

    rho_i' = (Q rho)_i,
    sum_i rho_i = M,
    0 <= rho_i <= 1.

Write u_i=rho_i−1/2 and E(t)=sum_i u_i². Summation by parts, including the reflecting endpoints, gives

    E'(t) = −sum_{edges {i,i+1}} (u_{i+1}−u_i)².

A deliberately loose finite-path Poincare inequality for mean-zero vectors is

    sum_i u_i² <= r² * sum_edges (u_{i+1}−u_i)².

It follows by writing each u_i as the average of all differences u_i−u_j, then Cauchy–Schwarz along each path segment. Thus

    E(t) <= (M/2) exp(−t/(4M²)).

The centered right-half indicator has squared norm M/2, so Cauchy–Schwarz yields

    |E[J(t)]−M/2| <= (M/2) exp(−t/(8M²)).

For every t>=8M², exp(−t/(8M²))<=exp(−1)<=1/2, and hence

    E[J(t)] >= M/4.

The coefficient is consistent with edge rate 1/2: d(sum u²)/dt is minus ONE edge-difference sum. A coefficient two here would silently speed up the process.

## 4. Elementary pair covariance comparison, not full negative association

For distinct slots i,j put

    m_ij=E[eta_i eta_j],  c_ij=m_ij−rho_i rho_j.

Let Q2 act on unordered distinct pairs by moving either coordinate along an existing path edge at rate 1/2, suppressing a move onto the other coordinate. The actual SSEP generator gives m'=Q2 m. Expanding the product derivatives gives exactly

    c_ij' = (Q2 c)_ij − (1/2) * 1_{i~j} * (rho_i−rho_j)².

This includes reflecting endpoints: missing edges contribute no term. Initial occupations are deterministic, so c_ij(0)=0. A finite cooperative-ODE maximum principle should imply c_ij(t)<=0. No full negative association theorem, infinite-particle construction, CLT, or exponential-moment comparison is needed.

Then

    Var(J) = sum_right rho_i(1−rho_i) + 2 sum_{i<j,right} c_ij
           <= M/4.

For M=8N and t>=8M²=512N², E[J]>=2N and Var(J)<=2N. Chebyshev therefore gives

    P(J<N) <= 2/N.

For N>=16 this is <=1/8, leaving room for the factor two in the EXISTING upper-direction synchronous comparison. A threshold N>=8 gives only <=1/4, still a useful clock bound but not directly a half-tail after adding scheduling error.

## 5. Return to the original synchronous expectation

The candidate target is the original finite CLOCK statement, for every N>=16 and every real t>=512N²,

    clockProbability (N−2) t <= 1/8.

Use the SECOND conjunct of `SquareGridLaw.two_way_clock_tail` at an actual scheduling time >=512N². Its synchronized time is `2*rankThreshold k+1`, and its right side is `2*clockProbability + 2*epsilon`. Choose k=O(N²) so epsilon<=1/8; this would give original synchronous tail<=1/2 at an actual deterministic block length O(N²). Existing top domination and `SquareRandomRestart` then yield true geometric tails; `ExtendedBlockTail` gives a finite ENNReal expectation without assuming prior finiteness. Original normalization/symmetry then covers all exact-N patterns and both homogeneous backgrounds. Finite small N can be absorbed into a fixed large square with an explicit constant.

This probability input is currently UNPROVED. The current lower-bound proof does not supply it.

## 6. Engineering gaps and suggested next complete stages

1. Define the mixed-boundary update, ideal/path bijection, and actual corner-swap generator. Prove same-clock domination of the original finite square; the sign direction matters.
2. Give a generic actual finite-observable clock Dynkin/compensation interface that can instantiate the mixed-boundary chain. Current weighted Dynkin is specialized to modified/frozen cleanup trajectories, so it should not be cited as if already this generic chain. The underlying actual marked-clock predictable compensation is reusable.
3. Derive finite one- and two-point moment integral equations from genuine generator identities. Justify differentiability/continuity (e.g. bounded observables plus true ring-count increment estimates, then FTC), rather than postulating an ODE as the final stochastic input.
4. Prove finite path Poincare, heat-energy Gronwall and pair cooperative maximum principle. These are deterministic finite-dimensional analysis and can be isolated from probability.
5. Prove the second-moment/Chebyshev bound under the real mixed-boundary law and close its cross-domain clock restriction. Only then integrate scheduling/restart/exact-N upper normalization.

Naive alternative rejected: permanently deleting each available southwest corner creates a directed growth/last-passage process, but suppresses reverse tie flips and accelerates zero growth. It cannot dominate the original 1 configuration in the needed direction. Deleting updates using the current spin/coin history is also not covered by the current clock-only finite-word PW comparison. Any such shortcut needs a separate valid theorem; it cannot be assumed.

No theorem above is promoted to formal completion by this document. The current main theorem remains unproved; independent AI analysis is not a human expert certification.
