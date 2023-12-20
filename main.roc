app "whelk"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [pf.Stdout, LinkedList.{ LinkedList }]
    provides [main] to pf

main =
    axioms = Set.fromList [
        ConceptInclusion { subclass: AtomicConcept "A", superclass: AtomicConcept "B" },
        ConceptInclusion { subclass: AtomicConcept "B", superclass: AtomicConcept "C" },
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
    # _ <- Task.await (Stdout.line (Num.toStr (Set.len axioms)))
    Stdout.line out

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

signature : Concept -> Set Entity
signature = \concept ->
    when concept is
        AtomicConcept id -> Set.single (AtomicConcept id)
        Conjunction { left, right } -> Set.union (signature left) (signature right)
        ExistentialRestriction { role: Role id, concept: filler } -> Set.union (Set.single (Role id)) (signature filler)

conceptSignature : Concept -> Set Concept
conceptSignature = \concept ->
    when concept is
        AtomicConcept _ -> Set.single concept
        Conjunction { left, right } -> Set.union (conceptSignature left) (conceptSignature right) |> Set.union (Set.single concept)
        ExistentialRestriction { concept: filler } -> Set.union (conceptSignature filler) (Set.single concept)

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
    todo: LinkedList.empty {},
    hier: Dict.empty {},
    hierList: Dict.empty {},
    hierComps: Dict.empty {},
    assertions: LinkedList.empty {},
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
    allRoles = Set.walk axioms (Set.empty {}) \rs, ax ->
        axiomSignature ax
        |> Set.walk rs \rs2, entity ->
            when entity is
                Role id -> Set.insert rs2 (Role id)
                _ -> rs2
    allRoleInclusions = List.keepOks axiomsList \ax ->
        when ax is
            RoleInclusion ri -> Ok ri
            _ -> Err {}
    hier = Set.walk allRoles (saturateRoles allRoleInclusions) \accum, role ->
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
    assertions = LinkedList.concat state.assertions (LinkedList.fromList axioms)
    computeClosure { state & assertions: assertions, todo: LinkedList.fromList atomicConcepts }

computeClosure : State -> State
computeClosure = \state ->
    when LinkedList.pop state.assertions is
        Cons { first, rest } -> processAssertedConceptInclusion first { state & assertions: rest } |> computeClosure
        Nil ->
            when LinkedList.pop state.todo is
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
    rolesToTargets = Dict.get state.linksBySubject subject |> Result.withDefault (Dict.empty {})
    targetsSet = Dict.get rolesToTargets role |> Result.withDefault (Set.empty {})
    if Set.contains targetsSet target then
        state
    else
        updatedTargetsSet = Set.insert targetsSet target
        updatedRolesToTargets = Dict.insert rolesToTargets role updatedTargetsSet
        linksBySubject = Dict.insert state.linksBySubject subject updatedRolesToTargets
        # rolesToSubjects = Dict.get state.linksByTarget target |> Result.withDefault (Dict.empty {})
        # subjects = Dict.get rolesToSubjects role |> Result.withDefault []
        # updatedSubjects = List.append subjects subject
        # updatedRolesToSubjects = Dict.insert rolesToSubjects role updatedSubjects
        # linksByTarget = Dict.insert state.linksByTarget target updatedRolesToSubjects
        linksByTarget = Dict.update state.linksByTarget target \possibleRolesToSubjects ->
            when possibleRolesToSubjects is
                Missing -> Present (Dict.single role [subject])
                Present rolesToSubjects ->
                    Present
                        (
                            Dict.update rolesToSubjects role \possibleSubjects ->
                                when possibleSubjects is
                                    Missing -> Present [subject]
                                    Present subjects -> Present (List.append subjects subject)
                        )
        { state & linksBySubject: linksBySubject, linksByTarget: linksByTarget }
        |> rBottomRight subject role target
        |> rPlusSomeRight subject role target
        |> rRingRight subject role target
        |> rRingLeft subject role target
        |> rSquiggle subject role target

processSub = \subclass, superclass, state ->
    emptySubClassSet = Set.single owl.bottom
    subs = Dict.get state.closureSubsBySuperclass superclass |> Result.withDefault emptySubClassSet
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
    emptySubClassSet = Set.single owl.bottom
    subs = Dict.get state.closureSubsBySuperclass superclass |> Result.withDefault emptySubClassSet
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

r0 = \state, concept -> { state & todo: LinkedList.push state.todo (Sub concept concept) }

rTop = \state, concept -> { state & todo: LinkedList.push state.todo (Sub concept owl.top) }

rSubLeft : State, ConceptInclusion -> State
rSubLeft = \state, ci ->
    todo =
        Dict.get state.closureSubsBySuperclass ci.subclass
        |> Result.withDefault (Set.empty {})
        |> Set.walk state.todo \accum, other ->
            LinkedList.push accum (Sub other ci.superclass)
    { state & todo: todo }

rBottomLeft : State, Concept, Concept -> State
rBottomLeft = \state, subclass, superclass ->
    if superclass == owl.bottom then
        todo =
            Dict.get state.linksByTarget subclass
            |> Result.withDefault (Dict.empty {})
            |> Dict.walk state.todo \accum, _, subjects ->
                List.walk subjects accum \accum2, subject ->
                    LinkedList.push accum2 (Sub subject owl.bottom)
        { state & todo: todo }
    else
        state

rBottomRight : State, Concept, Role, Concept -> State
rBottomRight = \state, subject, _role, target ->
    unsatisfiable = Dict.get state.closureSubsBySuperclass owl.bottom |> Result.withDefault (Set.empty {})
    if Set.contains unsatisfiable target then
        todo = LinkedList.push state.todo (Sub subject owl.bottom)
        { state & todo: todo }
    else
        state

rPlusAndA : State, ConceptInclusion -> State
rPlusAndA = \state, ci ->
    newNegativeConjunctions =
        conceptSignature ci.subclass
        |> Set.toList
        |> List.keepOks \concept ->
            when concept is
                Conjunction conj if !(Set.contains state.assertedNegConjs conj) -> Ok conj
                _ -> Err {}
    updatedAssertedNegConjs = Set.union state.assertedNegConjs (Set.fromList newNegativeConjunctions)
    (updatedByLeft, updatedByRight) = List.walk newNegativeConjunctions (state.assertedNegConjsByOperandLeft, state.assertedNegConjsByOperandRight) \(accumLeft, accumRight), conj ->
        updatedAssertedNegConjsByOperandLeft = Dict.update accumLeft conj.left \possibleByRightForLeft ->
            when possibleByRightForLeft is
                Missing -> Present (Dict.single conj.right conj)
                Present byRightForLeft -> Present (Dict.insert byRightForLeft conj.right conj)
        updatedAssertedNegConjsByOperandRight = Dict.update accumRight conj.right \possibleByLeftForRight ->
            when possibleByLeftForRight is
                Missing -> Present (Dict.single conj.left conj)
                Present byLeftForRight -> Present (Dict.insert byLeftForRight conj.left conj)
        (updatedAssertedNegConjsByOperandLeft, updatedAssertedNegConjsByOperandRight)
    rPlusAndB
        { state &
            assertedNegConjs: updatedAssertedNegConjs,
            assertedNegConjsByOperandLeft: updatedByLeft,
            assertedNegConjsByOperandRight: updatedByRight,
        }
        newNegativeConjunctions

rPlusAndB : State, List Conjunction -> State
rPlusAndB = \state, newNegativeConjunctions ->
    todo =
        todos1, conjunction <- List.walk newNegativeConjunctions state.todo
        leftSubclasses = Dict.get state.closureSubsBySubclass conjunction.left |> Result.withDefault (Set.empty {})
        rightSubclasses = Dict.get state.closureSubsBySuperclass conjunction.right |> Result.withDefault (Set.empty {})
        common = Set.intersection leftSubclasses rightSubclasses
        todos2, c <- Set.walk common todos1
        LinkedList.push todos2 (SubPlus c (Conjunction conjunction))
    { state & todo: todo }

# var newPropagations: List[(Concept, ExistentialRestriction)] = Nil
# var propagations = reasoner.propagations
# val ers = reasoner.negExistsMapByConcept.getOrElse(ci.superclass, Set.empty)
# for {
#   er <- ers
# } {
#   newPropagations = (ci.subclass, er) :: newPropagations
#   val current = propagations.getOrElse(ci.subclass, Map.empty)
#   val newList = er :: current.getOrElse(er.role, Nil)
#   propagations = propagations.updated(ci.subclass, current.updated(er.role, newList))
# }
# `R+∃left`(newPropagations, reasoner.copy(propagations = propagations), todo)
rPlusSomeBRight : State, Concept, Concept -> State
rPlusSomeBRight = \state, subclass, superclass ->
    ers = Dict.get state.negExistsMapByConcept superclass |> Result.withDefault (Set.empty {})
    Set.walk ers state \state1, er ->
        updatedPropagations = Dict.update state.propagations subclass \possibleProps ->
            when possibleProps is
                Missing -> Present (Dict.single er.role [er])
                Present props ->
                    Present
                        (
                            Dict.update props er.role \possibleERs ->
                                when possibleERs is
                                    Missing -> Present [er]
                                    Present propERs -> Present (List.append propERs er)
                        )
        rPlusSomeLeft { state1 & propagations: updatedPropagations } subclass er

rPlusSomeLeft : State, Concept, ExistentialRestriction -> State
rPlusSomeLeft = \state, concept, er ->
    todo =
        todos1, role, subjects <- Dict.get state.linksByTarget concept |> Result.withDefault (Dict.empty {}) |> Dict.walk state.todo
        superProperties = Dict.get state.hier role |> Result.withDefault (Set.empty {})
        if Set.contains superProperties er.role then
            todos2, subject <- List.walk subjects todos1
            LinkedList.push todos2 (SubPlus subject (ExistentialRestriction er))
        else
            todos1
    { state & todo: todo }

# rPlusSomeLeft : State, List[Propagation Concept ExistentialRestriction] -> State
# rPlusSomeLeft = \state, newPropagations ->
#     todo =
#         todos1, Propagation concept er <- List.walk newPropagations state.todo
#         todos2, role, subjects <- Dict.get state.linksByTarget concept |> Result.withDefault (Dict.empty {}) |> Dict.walk todos1
#         superProperties = Dict.get state.hier role |> Result.withDefault (Set.empty {})
#         if Set.contains superProperties er.role then
#             todos3, subject <- List.walk subjects todos2
#             push todos3 (SubPlus subject (ExistentialRestriction er))
#         else todos2
#     { state & todo: todo }

rPlusSomeRight : State, Concept, Role, Concept -> State
rPlusSomeRight = \state, subject, role, target ->
    roleToER = Dict.get state.propagations target |> Result.withDefault (Dict.empty {})
    todo =
        todos1, s <- Dict.get state.hierList role |> Result.withDefault [] |> List.walk state.todo
        todos2, f <- Dict.get roleToER s |> Result.withDefault [] |> List.walk todos1
        LinkedList.push todos2 (SubPlus subject (ExistentialRestriction f))
    { state & todo: todo }

rRingLeft : State, Concept, Role, Concept -> State
rRingLeft = \state, subject, role, target ->
    todo =
        todos1, r1, es <- Dict.get state.linksByTarget subject |> Result.withDefault (Dict.empty {}) |> Dict.walk state.todo
        r1s = Dict.get state.hierComps r1 |> Result.withDefault (Dict.empty {})
        todos2, s <- Dict.get r1s role |> Result.withDefault [] |> List.walk todos1
        todos3, e <- List.walk es todos2
        LinkedList.push todos3 (Link e s target)
    { state & todo: todo }

rRingRight : State, Concept, Role, Concept -> State
rRingRight = \state, subject, role, target ->
    r2s = Dict.get state.hierComps role |> Result.withDefault (Dict.empty {})
    linksByLinkSubject = Dict.get state.linksBySubject subject |> Result.withDefault (Dict.empty {})
    todo =
        todos1, r2, targets <- Dict.get state.linksBySubject target |> Result.withDefault (Dict.empty {}) |> Dict.walk state.todo
        todos2, s <- Dict.get r2s r2 |> Result.withDefault [] |> List.walk todos1
        linksWithS = Dict.get linksByLinkSubject s |> Result.withDefault (Set.empty {})
        todos3, d <- Set.walk targets todos2
        if !(Set.contains linksWithS d) then
            LinkedList.push todos3 (Link subject s d)
        else
            todos3
    { state & todo: todo }

rSquiggle : State, Concept, Role, Concept -> State
rSquiggle = \state, _subject, _role, target ->
    todo = LinkedList.push state.todo (Conc target)
    { state & todo: todo }

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
        superProps = Dict.get subToSuper role |> Result.withDefault (Set.empty {})
        Set.walk superProps (Set.empty {}) \accum, superProp ->
            if Set.contains currentExclude superProp then
                accum
            else
                Set.union (allSupers superProp currentExclude) accum |> Set.insert superProp
    Dict.walk subToSuper (Dict.empty {}) \accum, role, _ ->
        Dict.insert accum role (allSupers role (Set.empty {}))

indexRoleCompositions : Dict Role (Set Role), List RoleComposition -> Dict Role (Dict Role (List Role))
indexRoleCompositions = \hier, chains ->
    roleComps : Dict { first : Role, second : Role } (Set Role)
    roleComps = List.walk chains (Dict.empty {}) \accum, { first, second, superproperty } ->
        Dict.update accum { first, second } \possibleValue ->
            when possibleValue is
                Missing -> Present (Set.single superproperty)
                Present superProperties -> Present (Set.insert superProperties superproperty)

    hierCompsTuples : Set (Role, Role, Role)
    hierCompsTuples = Set.fromList
        (
            (r1, s1s) <- hier |> Dict.toList |> List.joinMap
            s1 <- s1s |> Set.toList |> List.joinMap
            (r2, s2s) <- hier |> Dict.toList |> List.joinMap
            s2 <- s2s |> Set.toList |> List.joinMap
            s <- Dict.get roleComps { first: s1, second: s2 } |> Result.withDefault (Set.empty {}) |> Set.toList |> List.map
            (r1, r2, s)
        )
    hierCompsRemove =
        (
            Set.toList hierCompsTuples
            |> List.joinMap \(r1, r2, s) ->
                Dict.get hier s
                |> Result.withDefault (Set.empty {})
                |> Set.toList
                |> List.joinMap \superS ->
                    if (superS != s) && (Set.contains hierCompsTuples (r1, r2, superS)) then
                        [(r1, r2, superS)]
                    else
                        []
        )
        |> Set.fromList
    hierCompsFiltered = Set.difference hierCompsTuples hierCompsRemove
    Set.walk hierCompsFiltered (Dict.empty {}) \accum, (r1, r2, s) ->
        Dict.update accum r1 \possibleDict ->
            when possibleDict is
                Missing -> Present (Dict.single r2 [s])
                Present r2ss ->
                    updatedInner = Dict.update r2ss r2 \possibleList ->
                        when possibleList is
                            Missing -> Present [s]
                            Present ss -> Present (List.append ss s)
                    Present updatedInner
