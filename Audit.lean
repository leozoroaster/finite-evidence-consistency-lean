import FiniteEvidenceConsistency

set_option pp.universes true in
#check @FiniteEvidence.finiteEvidence_characterization_relation

#print FiniteEvidence.Consistent
#print FiniteEvidence.MistakeSet
#print FiniteEvidence.Conflict
#print FiniteEvidence.IsTraceOf
#print FiniteEvidence.TraceOf

/-- info: 'FiniteEvidence.order_implies_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FiniteEvidence.order_implies_consistent

/-- info: 'FiniteEvidence.finite_strictDrops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FiniteEvidence.finite_strictDrops

/-- info: 'FiniteEvidence.CanonicalRun.exists_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FiniteEvidence.CanonicalRun.exists_run

/-- info: 'FiniteEvidence.transcript_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FiniteEvidence.transcript_length_le

/-- info: 'FiniteEvidence.transcript_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FiniteEvidence.transcript_replay

/-- info: 'FiniteEvidence.transcript_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FiniteEvidence.transcript_comparison

/-- info: 'FiniteEvidence.kb_wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FiniteEvidence.kb_wellFounded

/-- info: 'FiniteEvidence.consistent_implies_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FiniteEvidence.consistent_implies_order

/-- info: 'FiniteEvidence.finiteEvidence_characterization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FiniteEvidence.finiteEvidence_characterization

/-- info: 'FiniteEvidence.exists_leastSubtrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FiniteEvidence.exists_leastSubtrace

/-- info: 'FiniteEvidence.finiteEvidence_characterization_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FiniteEvidence.finiteEvidence_characterization_relation

/-- info: 'FiniteEvidence.stabilization_and_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FiniteEvidence.stabilization_and_agreement
