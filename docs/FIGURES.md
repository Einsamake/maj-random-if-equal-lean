# Figures and reproduction

**English** | [简体中文：原图](images/README.md) · [简体中文：证明方法配图](academic-figures/README.md)

The [original figure collection](images/) includes a diagram of the local rule, sample trajectories, diagrams for the clock comparison, and the staircase and local-clearing illustrations. The [proof-method figures](academic-figures/) illustrate the weighted boundary, the protected-loss threshold, the finite comparison principle, and the staircase-to-particle encoding.

| Figure or group | What it shows |
| --- | --- |
| [Four-neighbour rule](images/01-rule.png) | The centre site has no vote. |
| [Evolution](images/02-evolution.png), [animation](images/03-evolution.gif) | A sample trajectory for a fixed initial condition and seed $0$, with static frames at rounds $0,1,2,7$. |
| [Three recovery-time samples](images/04-recovery-times.png) | The same $3\times3$ initial state gives recovery times $7,4,10$ for seeds $0,5,8$. These three outcomes do not estimate the worst expected recovery time. |
| [Clock-time partition](images/09-clock-time.png) | A deterministic example: intervals of lengths $0.6,1.1,0.9$ observed up to time $2.2$ contribute lengths $0.6,1.1,0.5$. |
| [Staircase encoding](images/06-particle-encoding.png) | One legal corner flip on a $5\times5$ mixed-boundary square corresponds to an adjacent particle exchange. |
| [Local clearing](images/07-local-clearing.png) | The geometric construction with target side $16$ and auxiliary side $129$. Its probability bound is theoretical. |

Reproduction inputs are available as [simulation data](images/simulation-data.json), [clock data](images/clock-time-data.json), [encoding data](images/particle-encoding-data.json), [clearing data](images/local-clearing-data.json), and [toy checks for the proof-method figures](academic-figures/toy-checks.json). The plotting sources are listed in the [original figure instructions](images/README.md) and [proof-method figure instructions](academic-figures/README.md). Different fonts and renderers may change image bytes; the archived fingerprints refer to the original runs.
