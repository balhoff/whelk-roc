app "whelk"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.2.1/wx1N6qhU3kKva-4YqsVJde3fho34NqiLD3m620zZ-OI.tar.br" }
    imports [pf.Stdout]
    provides [main] to pf

main =
    axioms = Set.fromList [
        ConceptInclusion { subclass: AtomicConcept "A", superclass: AtomicConcept "B" },
        ConceptInclusion { subclass: AtomicConcept "B", superclass: AtomicConcept "C" },
    ]
    state = {
        prop: Dict.single owl.bottom (Set.empty {}),
    }
    # state = {
    #     todo : Nil,
    #     hier: Dict.empty {},
    #     hierList: Dict.empty {},
    #     hierComps: Dict.empty {},
    #     assertions: Nil,
    #     inits: Set.empty {},
    #     assertedConceptInclusionsBySubclass: Dict.empty {},
    #     closureSubsBySuperclass: Dict.single (owl.bottom) (Set.empty {}),
    #     #closureSubsBySubclass: Dict.single owl.top (Set.empty {}),
    #     assertedNegConjs: Set.empty {},
    #     assertedNegConjsByOperandRight: Dict.empty {},
    #     assertedNegConjsByOperandLeft: Dict.empty {},
    #     linksBySubject: Dict.empty {},
    #     linksByTarget: Dict.empty {},
    #     negExistsMapByConcept: Dict.empty {},
    #     propagations: Dict.empty {},
    # }
    dbg
        state

    # state = assert axioms
    # state = emptyState
    # out = Dict.walk state.closureSubsBySubclass "" \output, subclass, superclasses ->
    #     when subclass is
    #         AtomicConcept sub ->
    #             Set.walk superclasses output \accum, superclass ->
    #                 when superclass is
    #                     AtomicConcept sup -> Str.concat accum "\(sub) SubClassOf \(sup)\n"
    #                     _ -> accum
    #         _ -> output
    Stdout.line (Num.toStr (Set.len axioms))

Role : [Role Str]

Entity : [
    AtomicConcept Str,
    Role Str,
]

Conjunction : { left : Concept, right : Concept }

ExistentialRestriction : { role : Role, concept : Concept }

Concept : [
    AtomicConcept Str,
    Conjunction { left : Concept, right : Concept },
    ExistentialRestriction { role : Role, concept : Concept },
]

owl : { bottom : Concept, top : Concept }
owl = {
    bottom: AtomicConcept "http://www.w3.org/2002/07/owl#Nothing",
    top: AtomicConcept "http://www.w3.org/2002/07/owl#Thing",
}

ConceptInclusion : { subclass : Concept, superclass : Concept }

RoleInclusion : { subproperty : Role, superproperty : Role }

RoleComposition : { first : Role, second : Role, superproperty : Role }

Axiom : [
    ConceptInclusion { subclass : Concept, superclass : Concept },
    RoleInclusion { subproperty : Role, superproperty : Role },
    RoleComposition { first : Role, second : Role, superproperty : Role },
]

QueueItem : [
    Conc Concept,
    Sub Concept Concept,
    SubPlus Concept Concept,
    Link Concept Role Concept,
]

LinkedList a : [Nil, Cons { first : a, rest : LinkedList a }]
push : LinkedList a, a -> LinkedList a
push = \list, item -> Cons { first: item, rest: list }
linkedToList : LinkedList a -> List a
linkedToList = \list ->
    when list is
        Nil -> []
        Cons { first, rest } -> List.prepend (linkedToList rest) first

getOrElse : Dict k v, k, v -> v
getOrElse = \dict, key, defaultValue ->
    when Dict.get dict key is
        Ok value -> value
        Err _ -> defaultValue

signature : Concept -> Set Entity
signature = \concept ->
    when concept is
        AtomicConcept id -> Set.single (AtomicConcept id)
        Conjunction { left, right } -> Set.union (signature left) (signature right)
        ExistentialRestriction { role: Role id, concept: filler } -> Set.union (Set.single (Role id)) (signature filler)

conceptSignature : Concept -> Set Concept
conceptSignature = \concept ->
    when concept is
        AtomicConcept id -> Set.single concept
        Conjunction { left, right } -> Set.union (conceptSignature left) (conceptSignature right) |> Set.union (Set.single concept)
        ExistentialRestriction { role: Role id, concept: filler } -> Set.union (conceptSignature filler) (Set.single concept)

axiomSignature : Axiom -> Set Entity
axiomSignature = \axiom ->
    when axiom is
        ConceptInclusion { subclass, superclass } -> Set.union (signature subclass) (signature superclass)
        RoleInclusion { subproperty: Role sub, superproperty: Role sup } -> Set.fromList [Role sub, Role sup]
        RoleComposition { first: Role first, second: Role second, superproperty: Role sup } -> Set.fromList [Role first, Role second, Role sup]

State : {
    todo : LinkedList QueueItem,
    hier : Dict Role (Set Role),
    hierList : Dict Role (List Role),
    hierComps : Dict Role (Dict Role (List Role)),
    assertions : LinkedList ConceptInclusion,
    inits : Set Concept,
    assertedConceptInclusionsBySubclass : Dict Concept (List ConceptInclusion),
    closureSubsBySuperclass : Dict Concept (Set Concept),
    closureSubsBySubclass : Dict Concept (Set Concept),
    assertedNegConjs : Set Conjunction,
    assertedNegConjsByOperandRight : Dict Concept (Dict Concept Conjunction),
    assertedNegConjsByOperandLeft : Dict Concept (Dict Concept Conjunction),
    linksBySubject : Dict Concept (Dict Role (Set Concept)),
    linksByTarget : Dict Concept (Dict Role (List Concept)),
    negExistsMapByConcept : Dict Concept (Set ExistentialRestriction),
    propagations : Dict Concept (Dict Role (List ExistentialRestriction)),
}

emptyState : State
emptyState = {
    todo: Nil,
    hier: Dict.empty {},
    hierList: Dict.empty {},
    hierComps: Dict.empty {},
    assertions: Nil,
    inits: Set.empty {},
    assertedConceptInclusionsBySubclass: Dict.empty {},
    closureSubsBySuperclass: Dict.single owl.bottom (Set.empty {}),
    closureSubsBySubclass: Dict.single owl.top (Set.empty {}),
    assertedNegConjs: Set.empty {},
    assertedNegConjsByOperandRight: Dict.empty {},
    assertedNegConjsByOperandLeft: Dict.empty {},
    linksBySubject: Dict.empty {},
    linksByTarget: Dict.empty {},
    negExistsMapByConcept: Dict.empty {},
    propagations: Dict.empty {},
}

assert : Set Axiom -> State
assert = \axioms ->
    axiomsList = Set.toList axioms
    allRoles = List.joinMap axiomsList \ax -> Set.toList (axiomSignature ax)
        |> List.keepOks \e ->
            when e is
                Role id -> Ok (Role id)
                _ -> Err {}
    allRoleInclusions = List.keepOks axiomsList \ax ->
        when ax is
            RoleInclusion ri -> Ok ri
            _ -> Err {}
    hier = List.walk allRoles (saturateRoles allRoleInclusions) \accum, role ->
        Dict.update accum role \possibleValue ->
            when possibleValue is
                Missing -> Present (Set.single role)
                Present roleSet -> Present (Set.insert roleSet role)
    hierList = Dict.walk hier (Dict.empty {}) \accum, role, supers ->
        Dict.insert accum role (Set.toList supers)
    allRoleCompositions = List.keepOks axiomsList \ax ->
        when ax is
            RoleComposition rc -> Ok rc
            _ -> Err {}
    hierComps = indexRoleCompositions hier allRoleCompositions
    concIncs = List.keepOks axiomsList \ax ->
        when ax is
            ConceptInclusion ci -> Ok ci
            _ -> Err {}
    extend concIncs { emptyState & hier: hier, hierList: hierList, hierComps: hierComps }

extend : List ConceptInclusion, State -> State
extend = \axioms, state ->
    distinctConcepts = List.walk axioms (Set.empty {}) \accum, { subclass, superclass } ->
        Set.union (conceptSignature subclass) (conceptSignature superclass) |> Set.union accum
    atomicConcepts =
        Set.toList distinctConcepts
        |> List.keepOks \concept ->
            when concept is
                AtomicConcept _ -> Ok (Conc concept)
                _ -> Err {}
    acLinkedList = List.walk atomicConcepts Nil \accum, ac -> push accum ac
    assertions = List.concat axioms (linkedToList state.assertions) |> List.walk Nil \accum, ax -> push accum ax
    computeClosure { state & assertions: assertions, todo: acLinkedList }

computeClosure : State -> State
computeClosure = \state ->
    when state.assertions is
        Cons { first, rest } -> processAssertedConceptInclusion first { state & assertions: rest } |> computeClosure
        Nil ->
            when state.todo is
                Cons { first, rest } -> process first { state & todo: rest } |> computeClosure
                Nil -> state

processAssertedConceptInclusion : ConceptInclusion, State -> State
processAssertedConceptInclusion = \ci, state ->
    updated = Dict.update state.assertedConceptInclusionsBySubclass ci.subclass \possibleValue ->
        when possibleValue is
            Missing -> Present [ci]
            Present cis -> Present (List.append cis ci)
    # FIXME run rules
    { state & assertedConceptInclusionsBySubclass: updated }
    |> rSubLeft ci
    |> rPlusAndA ci
# R+∃a
# R⊔aleft

process : QueueItem, State -> State
process = \item, state ->
    when item is
        Link subject role target -> processLink subject role target state
        Sub subclass superclass -> processSub subclass superclass state
        SubPlus subclass superclass -> processSubPlus subclass superclass state
        Conc concept -> processConcept concept state

processLink = \subject, role, target, state ->
    crash "processLink"

processSub = \subclass, superclass, state ->
    emptySubClassSet = Set.single owl.bottom
    subs = getOrElse state.closureSubsBySuperclass superclass emptySubClassSet
    if Set.contains subs subclass then
        state
    else
        closureSubsBySuperclass = Dict.insert state.closureSubsBySuperclass superclass (Set.insert subs subclass)
        closureSubsBySubclass = Dict.update state.closureSubsBySubclass subclass \possibleSupers ->
            when possibleSupers is
                Missing -> Present (Set.single superclass)
                Present supers -> Present (Set.insert supers superclass)
        { state & closureSubsBySubclass: closureSubsBySubclass, closureSubsBySuperclass: closureSubsBySuperclass }
        |> rBottomLeft subclass superclass

processSubPlus = \subclass, superclass, state ->
    crash "processSubPlus"

processConcept = \concept, state ->
    if Set.contains state.inits concept then
        state
    else
        updatedClosureSubsBySubclass = Dict.update state.closureSubsBySubclass owl.bottom \possibleValue ->
            when possibleValue is
                Missing -> Present (Set.single concept)
                Present supers -> Present (Set.insert supers concept)
        { state & inits: Set.insert state.inits concept, closureSubsBySubclass: updatedClosureSubsBySubclass }
        |> r0 concept
        |> rTop concept

r0 = \state, concept -> { state & todo: push state.todo (Sub concept concept) }

rTop = \state, concept -> { state & todo: push state.todo (Sub concept owl.top) }

rSubLeft = \state, ci ->
    todo =
        getOrElse state.closureSubsBySuperclass ci.subclass (Set.empty {})
        |>
        Set.walk state.todo \accum, other ->
            push accum (Sub other ci.superclass)
    { state & todo: todo }

rBottomLeft = \state, subclass, superclass ->
    if superclass == owl.bottom then
        todo =
            getOrElse state.linksByTarget subclass (Dict.empty {})
            |>
            Dict.walk state.todo \accum, _, subjects ->
                List.walk subjects accum \accum2, subject ->
                    push accum2 (Sub subject owl.bottom)
        { state & todo: todo }
    else
        state

rPlusAndA = \state, ci ->
    newNegativeConjunctions =
        conceptSignature ci.subclass
        |> Set.toList
        |> List.keepOks \concept ->
            when concept is
                Conjunction conj if !(Set.contains state.assertedNegConjs conj) -> Ok conj
                _ -> Err {}
    # FIXME
    crash "rPlusAndA"

saturateRoles : List RoleInclusion -> Dict Role (Set Role)
saturateRoles = \roleInclusions ->
    subToSuper = List.walk roleInclusions (Dict.empty {}) \accum, { subproperty, superproperty } ->
        Dict.update accum subproperty \possibleValue ->
            when possibleValue is
                Missing -> Present (Set.single superproperty)
                Present supSet -> Present (Set.insert supSet superproperty)
    allSupers : Role, Set Role -> Set Role
    allSupers = \role, exclude ->
        currentExclude = Set.insert exclude role
        superProps = getOrElse subToSuper role (Set.empty {})
        Set.walk superProps (Set.empty {}) \accum, superProp ->
            if Set.contains currentExclude superProp then
                accum
            else
                Set.union (allSupers superProp currentExclude) accum |> Set.insert superProp
    Dict.walk subToSuper (Dict.empty {}) \accum, role, _ ->
        Dict.insert accum role (allSupers role (Set.empty {}))

indexRoleCompositions : Dict Role (Set Role), List RoleComposition -> Dict Role (Dict Role (List Role))
indexRoleCompositions = \hier, chains ->
    roleComps = List.walk chains (Dict.empty {}) \accum, { first, second, superproperty } ->
        Dict.update accum { first, second } \possibleValue ->
            when possibleValue is
                Missing -> Present (Set.single superproperty)
                Present superProperties -> Present (Set.insert superProperties superproperty)
    hierCompsTuples : Set [T Role Role Role]
    hierCompsTuples =
        (
            Dict.toList hier
            |> List.joinMap \T r1 s1s ->
                Set.toList s1s
                |> List.joinMap \s1 ->
                    Dict.toList hier
                    |> List.joinMap \T r2 s2s ->
                        Set.toList s2s
                        |> List.joinMap \s2 ->
                            getOrElse roleComps { first: s1, second: s2 } (Set.empty {})
                            |> Set.toList
                            |> List.map \s ->
                                T r1 r2 s
        )
        |> Set.fromList
    hierCompsRemove =
        (
            Set.toList hierCompsTuples
            |> List.joinMap \T r1 r2 s ->
                getOrElse hier s (Set.empty {})
                |> Set.toList
                |> List.joinMap \superS ->
                    if (superS != s) && (Set.contains hierCompsTuples (T r1 r2 superS)) then
                        [T r1 r2 superS]
                    else
                        []
        )
        |> Set.fromList
    hierCompsFiltered = Set.difference hierCompsTuples hierCompsRemove
    Set.walk hierCompsFiltered (Dict.empty {}) \accum, T r1 r2 s ->
        Dict.update accum r1 \possibleDict ->
            when possibleDict is
                Missing -> Present (Dict.single r2 [s])
                Present r2ss ->
                    updatedInner = Dict.update r2ss r2 \possibleList ->
                        when possibleList is
                            Missing -> Present [s]
                            Present ss -> Present (List.append ss s)
                    Present updatedInner
