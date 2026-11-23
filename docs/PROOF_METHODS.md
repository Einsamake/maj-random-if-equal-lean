# Proof methods

**English** | [简体中文](proof-discovery/README.md)

The methods below are used in the original proof of the quadratic recovery theorem. The [proof guide](PROOF_GUIDE.md) gives their place in the full argument.

| Method | Role in the proof | Original notes (Chinese) |
| --- | --- | --- |
| Monotone comparison | It is enough to study the filled square: using the same tie-breaking coins preserves inclusion of occupied sets. | [Model and recovery theorem](proof-discovery/00-results.md), [comparison route](proof-discovery/01-route.md) |
| Weighted missing area | A layer of zero weight removes a boundary correction. Losing a protected site requires order $L^3$ missing weight, while the expected weight loss over a time interval of length $t$ is bounded above by terms of orders $Lt$ and $L^2$. | [Boundary weight](proof-discovery/02-boundary-weight.md) |
| Positive-part energy | A finite comparison principle controls the sign of covariance between distinct particle sites. | [Finite comparison principle](proof-discovery/03-positive-energy.md) |
| Local clearing and restart | A staircase interface is encoded by particles on a finite path. A probability bound for clearing a corner transfers to the target square, then a conditional restart at each time-block boundary yields the geometric upper tail. | [Clearing and restart](proof-discovery/04-enough-probability.md) |
| Structure beyond this example | The notes state the assumptions for each argument and illustrate the finite comparison on a directed three-cycle. | [Scope](proof-discovery/05-candidates.md), [three-site example](proof-discovery/06-first-reuse.md) |

The [figures](FIGURES.md) illustrate finite calculations and the staircase encoding. General statements and their proof dependencies are listed in [Verification](VERIFICATION.md).
