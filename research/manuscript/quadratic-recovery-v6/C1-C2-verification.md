# C1 and C2 verification record

The proof drafts were prepared on `paper/c1-c2` at baseline `fe0da72171bacfbafe097bd018e6b9ffa46c0c43`. They are English Markdown addenda for the v5 manuscript. Both results are paper proofs. The Lean references identify existing inputs and restart patterns at the existing scale.

## Independent reader on 17 November 2026

An independent AI reader with no project history was asked to read only the two texts, with undergraduate probability and discrete mathematics as background. The drafts contain no figures. The reader restated each argument and worked examples before reviewing the revisions.

| Draft | SHA-256 at first read | SHA-256 at reread |
| --- | --- | --- |
| [C1](C1-clock-literature.md) | `9685c9d957485c86d0851a63ae151f87d887d2b1ac9d982529dbf3f4112c0dc0` | `12d321e89a5d1bad3c5cefd67bb84e43235453a777acb5f6bfb2941dcab4dc50` |
| [C2](C2-first-moment-upper.md) | `b67b018e196023a67720abfc1cfe1bb52cd6114507577e4969b54905c787b7a4` | `227dfc77b73ea7c177756537cff68763e99c25e66501ca5f7e24e4477de2ee2a` |

- **C1 first read.** The reader reconstructed the spin mapping, odd-side clock window, nested-square comparison, transfer in both directions, and synchronous restart. They inferred the general parity calculation and the lower expectation inequality. The role of the index in the comparison and the meaning of CMST and v5 needed explanation.
- **C1 revision and reread.** The text now introduces CMST and the v5 draft, derives both parity cases, distinguishes physical time, conflict rank, and synchronous rounds, and gives the two inequalities used in the lower expectation argument. The reader reproduced the parity calculation and explained why the lower time must be strictly before $cL^2$ while equality is allowed at the upper time $L^2/c$. With illustrative $c=1/2$, $\gamma=1/4$, they obtained $N_0=710$. At $N=710$ and $711$, their $k_-$ values were $5648$ and $5680$, with common $k_+=45453$ and $B_N=11{,}636{,}225$. The reader noted that the final $+1$ is still supplied by the cited bridge. The derivation in v5 §3.3.9 combines the $2q$ scans with the checkerboard relation $p_m(2q+1)\le2 A_{\mathrm{even}}(2q)$.
- **C2 first read.** The reader reproduced the first-moment argument, the uniform chance of clearing in the original clock process, and the two restart arguments. They asked why the right-half count forces southwest zeros, why $M/2$ is the reference value, and for the intermediate steps in the probability rearrangement and coupling.
- **C2 revision and reread.** The text now maps particle positions to diagonal zeros, gives the example with row lengths $(2,2,0)$ and slots $(0,3,4)$, explains the mean density and heat estimate, and shows the ring-by-ring comparison and rearrangement. The reader explained why the auxiliary event concerns one endpoint and why the original state stays zero after clearing. They recomputed all values at $N=16$, including $14h=3{,}727{,}584$, $E_N(k_N)\le3/640$, and $2b_N=594{,}543{,}106$. They also checked that $J\ge17$ suffices for the needed $J\ge16$.

On reread the reader reported that the substantive clarity issues were resolved and found no internal mathematical error conditional on the cited inputs. The reader exercise checks how the proof reads with those inputs available.

## Source and arithmetic checks

- Checked the model against CMST §2 and (2.17), and the window against Theorem 2 in the cited version. The C1 derivation accounts for both endpoints, the even-square coupling, and both bridge errors. Checked the bridge and restart against v5 Lemmas 1, 2, and 6. [CMST v2](https://arxiv.org/html/1007.3599v2#S3.SS2)
- Checked C2 against v5 (14), (H4)–(H8), Lemma 5, and §4.2.1, and located the Lean statements in both drafts' correspondence tables. Compared the conditional law at deterministic clock times with the observed-history argument in §4.2.1. Checked the dependency distinction between the new paper route and the current Lean imports. The original v5 handoff manuscript matches the handoff SHA-256 `2b3411cb3c8f661650b3f1e7390d58aa8d91db10ec2ef75e0e8d9ab8361b59d0`.
- Recomputed C1 rounding, parity, and strict/non-strict cutoff inequalities in Python across illustrative choices of $c,\gamma$ and both parities. Recomputed the C2 staircase example, the exact comparison $(6/7)^{14}<1/8$, and the $N=16$ scales and scheduling bound using integer and rational arithmetic. Checked both final draft hashes, local links, and displayed-equation delimiter pairs.

## Final Lean proofs

The final source was built in the analysis project on branch `paper/c1-c2` at base commit `fe0da72171bacfbafe097bd018e6b9ffa46c0c43`. The toolchain was Lean `4.35.0-rc4` and the mathlib revision was `54c01c3314d33d15d77893cbe4e0472ff26bb34d`.

| Route | Final declarations |
| --- | --- |
| C1 | [ClockLiteratureTransfer.lean](../../../formal/analysis/MathResearchAnalysis/ClockLiteratureTransfer.lean) proves `tau_theta_of_odd_clock_window`. From the explicit input `OddClockWindow` and positive literature constants, it proves two quadratic expectation bounds on the exact-size profile. The assembly uses a lower tail for the filled square and the uniform synchronous block tail for the upper bound. |
| C2 clock restart | [DeterministicClockRestart.lean](../../../formal/analysis/MathResearchAnalysis/DeterministicClockRestart.lean) proves `endpoint_joint` and `endpoint_probability` for the original marked clock measure at deterministic nonnegative times. It splits the independent gaps and marks on each count slice, applies exponential memorylessness jointly, and matches the shifted chronological word and its marks to the original suffix. |
| C2 recovery | [FirstMomentClockUpper.lean](../../../formal/analysis/MathResearchAnalysis/FirstMomentClockUpper.lean) instantiates the clock law in `restartLaw`, proves the geometric synchronous `recovery_block_tail`, and closes `tau_explicit_upper` for every $N\ge16$ with constant $2{,}322{,}432N^2+514$. The end theorem has only a size and a size-threshold argument. |

The final validation was run on 18 November 2026 (Asia/Shanghai) with the following commands in `formal/analysis`, after activating the pinned toolchain.

```powershell
$env:LEAN_NUM_THREADS='4'
lake --no-ansi build '+MathResearchAnalysis.ClockLiteratureTransfer' '+MathResearchAnalysis.DeterministicClockRestart' '+MathResearchAnalysis.FirstMomentClockUpper'
lake env lean --trust=0 C1C2Axioms.lean
```

Both commands returned exit code `0`. Lake reported `Build completed successfully (4027 jobs).` It also reported a style warning preferring `let` in place of `letI` for a finite-measure instance used in a proposition. The [audit entry point](../../../formal/analysis/C1C2Axioms.lean) checks the even/odd bracketing at actual sides 16 and 17, the zero-ring threshold, and the block length and final expectation bound at $N=16$. The generic rounding theorem enforces the strict lower clock cutoff and the inclusive upper cutoff.

### Final source fingerprints

| Source | SHA-256 |
| --- | --- |
| ClockLiteratureTransfer.lean | `71a4e290592d5debbf3417c351db69f8b983ebf0167e5fda2dd6b2e0fe0772bf` |
| DeterministicClockRestart.lean | `46f0e473b118d53be5c20a19c80da79ed3951c8750608e944b6dd4162213e440` |
| FirstMomentClockUpper.lean | `b3ce4278e6e2cc23b972f8b349603834a12aeae8eb9bbc5ce38257d2f47fc92b` |
| C1C2Axioms.lean | `b4750880e4219ece2080c4391d22135dc646a142a45ff5204b7abdb90c95fa31` |

### Axiom output

Each of the 12 audited declarations used the same three standard axioms.

```text
'MathResearchAnalysis.ClockLiteratureTransfer.clockProbability_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MathResearchAnalysis.ClockLiteratureTransfer.transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathResearchAnalysis.ClockLiteratureTransfer.exists_comparison_rounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MathResearchAnalysis.ClockLiteratureTransfer.tau_theta_of_odd_clock_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MathResearchAnalysis.DeterministicClockRestart.endpoint_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MathResearchAnalysis.DeterministicClockRestart.endpoint_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MathResearchAnalysis.FirstMomentClockUpper.count_failure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathResearchAnalysis.FirstMomentClockUpper.one_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathResearchAnalysis.FirstMomentClockUpper.restartLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathResearchAnalysis.FirstMomentClockUpper.survival_step_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathResearchAnalysis.FirstMomentClockUpper.recovery_block_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MathResearchAnalysis.FirstMomentClockUpper.tau_explicit_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```


### Publication links

On 18 November 2026, the two addenda's local v5 links were replaced by a pinned link to the published A/B revision. The reader fingerprints above identify the versions actually read. The proof text and Lean source were preserved during this link update. The published revision retains the cited bridge and staircase equations; its §3.4 supplies the deterministic-time clock discussion.
| Current addendum | SHA-256 |
| --- | --- |
| C1-clock-literature.md | `215bde022a8d5e85f4ace751a30161a9f7f708a123b3181f553cfae38d559cc5` |
| C2-first-moment-upper.md | `3325caa0fd0d5f4e2d417ff040b63f474a161f9e090ba7d0ae850375ec46861e` |
