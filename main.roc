app "whelk"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [
        pf.Stdout,
        WhelkReasoner.{ assert },
    ]
    provides [main] to pf

main =
    partOf = Role "part_of"
    overlaps = Role "overlaps"
    axioms = Set.fromList [
        ConceptInclusion { subclass: AtomicConcept "A", superclass: AtomicConcept "B" },
        ConceptInclusion { subclass: AtomicConcept "B", superclass: AtomicConcept "C" },
        ConceptInclusion { subclass: AtomicConcept "A", superclass: AtomicConcept "D" },
        ConceptInclusion {
            subclass: Conjunction { left: AtomicConcept "C", right: AtomicConcept "D" },
            superclass: AtomicConcept "E",
        },
        ConceptInclusion {
            subclass: ExistentialRestriction { role: overlaps, concept: AtomicConcept "X" },
            superclass: AtomicConcept "Y",
        },
        ConceptInclusion {
            subclass: AtomicConcept "B",
            superclass: ExistentialRestriction { role: partOf, concept: AtomicConcept "X" },
        },
        ConceptInclusion {
            subclass: AtomicConcept "F",
            superclass: ExistentialRestriction { role: partOf, concept: AtomicConcept "B" },
        },
        RoleInclusion {
            subproperty: partOf,
            superproperty: overlaps,
        },
        RoleComposition {
            first: partOf,
            second: partOf,
            superproperty: partOf,
        },
    ]
    state = assert axioms
    out = Dict.walk state.closureSubsBySubclass "" \output, subclass, superclasses ->
        when subclass is
            AtomicConcept sub ->
                Set.walk superclasses output \accum, superclass ->
                    when superclass is
                        AtomicConcept sup -> Str.concat accum "\(sub) SubClassOf \(sup)\n"
                        _ -> accum

            _ -> output
    Stdout.line out
