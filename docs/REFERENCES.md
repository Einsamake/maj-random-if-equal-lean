# References and sources

[简体中文](REFERENCES.zh-CN.md)

<a id="文献与出处"></a>

<a id="fates-marcovici-taati-2022"></a>

## Fatès–Marcovici–Taati 2022

[1] N. Fatès, I. Marcovici and S. Taati. *Self-stabilisation of cellular automata on tilings*. Fundamenta Informaticae, **185**(1), 2022. DOI [10.3233/FI-222103](https://doi.org/10.3233/FI-222103). [arXiv:2101.12682v3](https://arxiv.org/abs/2101.12682v3), 5 March 2022.

Section 4.2 defines the synchronous four-neighbour Maj-Random-If-Equal rule. Proposition 4.1 gives a cubic upper bound on the worst expected stabilisation time. Question 7.4 in §7.2 asks for the precise order of that time and conjectures quadratic growth. The repository takes this question and model as its starting point.

The paper discusses continuous-time updates separately in [Example 4.2 of the journal PDF](https://marcovici.perso.math.cnrs.fr/Publications/Fates_Marcovici_Taati_FI2022.pdf#page=30), numbered [Example 4.3 in the arXiv HTML rendering](https://arxiv.org/html/2101.12682v3). Continuous time and single-site updates differ from simultaneous discrete rounds. When the repository uses an auxiliary clock process, it proves a comparison with the original synchronous process. This citation identifies the source of the question and model. Questions of literature priority require a separate search.

<a id="形式化结果的引用"></a>

## Citing the formal results

The original asymptotic theorem is `MathResearchAnalysis.OriginalQuadraticRecovery.tau_theta_quadratic` in [OriginalQuadraticRecovery.lean](../formal/analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean). See [research results](RESEARCH_RESULTS.md) for explicit constants, parameter ranges and subsequent quantitative improvements, and [verification and reproduction](VERIFICATION.md) for toolchains and source versions.

When citing the repository, record its URL, the commit you used and the specific declaration. The [deliverables inventory](../deliverables/README.md) identifies the material archived on 26 October 2026. That date records the archive. The sources of individual waiting-network results are listed in the [waiting-network research index](../research/exploration/README.md) (in Chinese).
