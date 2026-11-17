from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent;p=R/'paper/paper.md';s=p.read_text(encoding='utf-8')
s=s.replace('Then $0\\leq a_N\\leq1/2$, $a_N\\to0$ as $N\\to\\infty$, and,',
 'Then $0\\leq a_N\\leq\\min(1/2,5/N)$, so $a_N=O(N^{-1})$, and,',1)
anchor='Together with $32/(8N+1)\\to0$, this proves $a_N\\to0$ and the recovery-by-deadline conclusion.'
addition=r'''Together with $32/(8N+1)\to0$, this proves $a_N\to0$. Its explicit rate follows from $k_N+1\geq2N$ and $64N^2\leq2^N$ for $N\geq16$. Also $N\leq2^N$, so $(2^N)^2\geq64N^3$. Hence
$$
\frac{12}{5}N^2 2^{-(k_N+1)}
\leq\frac{12N^2}{5(2^N)^2}\leq\frac1N,
\qquad \frac{32}{8N+1}\leq\frac4N.
$$
This proves $a_N\leq5/N$ and the stated recovery-by-deadline conclusion.'''
assert anchor in s;s=s.replace(anchor,addition,1)
old='The companion [source map](scheduling-source-map.json) fixes the declarations, line locations, and source fingerprints for these correspondences. The [edit record](edit-record-scheduling.json) separates the three editing passes from the independent simulated-reader review to be recorded by the integrating editor. Nothing in this section changes a formal source or claims a new kernel audit. Its probabilistic results concern the original product clock law; its final endpoint comparison uses the finite censoring lemma proved in §3.2 (S18).'
new='The probabilistic estimates above concern the original product clock law. The final endpoint comparison uses the finite censoring lemma proved in §3.2 (S18). The corresponding declarations are listed in §9.'
assert old in s;s=s.replace(old,new,1)
old2='The companion [source map](budget-source-map.json) records the existing definitions, conclusions and source fingerprints. The finite reachable weighted-counter construction and its application of the common original-clock identity in §3.4 are proved here in ordinary mathematics. The source map also identifies the corresponding formal event-by-event proof of this physical budget; that route is separate from the finite-machine derivation given here. No new Lean declaration or kernel check is claimed for the augmented-state construction.'
new2='The finite reachable weighted-counter construction above permits the application of the common original-clock identity in §3.4. The formal source also contains an event-by-event derivation of the same physical budget; the source correspondence is recorded in §9.'
assert old2 in s;s=s.replace(old2,new2,1)
row='| Lemma 6 and final upper bound |'
pos=s.index(row);end=s.index('\n',pos)
rows='''
| Exact filled-square extremizer and original-law block tail | [OriginalRecoveryResults](../lean/OriginalRecoveryResults.lean): tau_eq_full_square, original_recovery_block_tail |
| Accurate failure rate and restart | [SharpRecoveryTail](../lean/SharpRecoveryTail.lean): recovery_block_tail, finiteExpected_le, tau_le; [SharpFailureRate](../lean/SharpFailureRate.lean): failure_le_five_div, failure_isBigO_inv |
| Fixed positive moments and exponential interval | [RecoveryMoments](../lean/RecoveryMoments.lean): recovery_rpow_le, recovery_exponential_le, expConstant_lt_top |
| Original infinite-grid conclusions and the shared current-state formula | [OriginalConsequences](../lean/OriginalConsequences.lean): quadratic_bounds, original_sharp_block_tail, original_rpow_le, original_exponential_lt_top, finite_machine_dynkin |'''
s=s[:end]+rows+s[end:]
old3='This manuscript task has not rerun that audit or changed its frozen sources. The companion [revision-source-map.json](revision-source-map.json) records the declarations used in the revised sections; [edit-record.json](edit-record.json) records their editing passes. The inherited v5 source maps retain their original provenance. Kernel validation does not certify that this exposition is complete, that its model correspondence has human specialist approval, or that it has historical priority. These require separate assessment.'
new3='The new interfaces preserve the original infinite-grid measure, both homogeneous backgrounds, exact enclosing-square size, and extended recovery time. The [revision validation record](../validation.json) separates the fresh project-source replay, the new-module builds and per-declaration axiom output, the source fingerprints, and the independent AI semantic check. It also records that the locked external Lean and mathlib dependencies are reused. The [source dictionary](revision-source-map.json) identifies the proof interfaces used in the revised sections. These checks are distinct from human specialist refereeing and historical-priority assessment.'
assert old3 in s;s=s.replace(old3,new3,1)
p.write_text(s,encoding='utf-8',newline='\n')
(R/'paper/review/root-edit-pass.json').write_text(json.dumps({'paper_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'passes':[{'purpose':'mathematical conditions and endpoints','changes':['Theorems3/4 with full proofs','0<=a<=min(1/2,5/N)','extended-valued powers/exponentials and AE finiteness before representatives']},{'purpose':'remove stale workflow prose','changes':['remove unperformed simulated-reader promises','separate old proof provenance from new replay']},{'purpose':'scope and source dictionary','changes':['original-model aggregate interfaces mapped','C1/C2 excluded','external dependency reuse explicitly retained']}],'reader_review':'waived by explicit user instruction on 2026-11-17'},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(hashlib.sha256(p.read_bytes()).hexdigest())
