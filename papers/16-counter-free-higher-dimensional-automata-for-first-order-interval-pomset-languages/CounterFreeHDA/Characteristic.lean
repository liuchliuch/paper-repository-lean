import CounterFreeHDA.CharacteristicLanguage

/-! Full actual characteristic realization (Lemma 3.1).
`st_representation` constructs an elementary ST label for every bounded-width
interval pomset. `Arrow.lemma_3_1_a` identifies every complete path label with
exactly a subsumption of the original pomset. `Arrow.lemma_3_1_b` proves the
prescribed-endpoint path/map equivalence with no representation premise.
The reverse language inclusion uses actual event-occurrence injections and
surjectivity at the distinguished cells, proved by `RunLabeling.ofRun` and
`RunLabeling.subsumption_complete`. -/
