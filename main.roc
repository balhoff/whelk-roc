app "whelk"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.2.1/wx1N6qhU3kKva-4YqsVJde3fho34NqiLD3m620zZ-OI.tar.br" }
    imports [pf.Stdout]
    provides [main] to pf


main = 
    aRole = { id: "BFO:0000050" }
    Stdout.line "\(aRole.id)."

Role : [Role Str]

Entity : [
    AtomicConcept Str,
    Role Str
]

Conjunction : {left : Concept, right : Concept }

ExistentialRestriction : { role : Role, concept : Concept }

Concept : [
    AtomicConcept Str,
    Conjunction {left : Concept, right : Concept}, 
    ExistentialRestriction { role : Role, concept : Concept }
]

bottom : Concept
bottom = AtomicConcept ""

top : Concept
top = AtomicConcept ""

ConceptInclusion : {subclass : Concept, superclass : Concept}

RoleInclusion : {subproperty : Role, superproperty : Role}

RoleComposition : {first : Role, second : Role, superproperty : Role}

Axiom : [
    ConceptInclusion {subclass : Concept, superclass : Concept},
    RoleInclusion {subproperty : Role, superproperty : Role},
    RoleComposition {first : Role, second : Role, superproperty : Role}
]

QueueItem : [
    Conc Concept,
    Sub Concept Concept,
    SubPlus Concept Concept,
    Link Concept Role Concept
]

LinkedList a : [ Nil, Cons { first : a, rest : LinkedList a}]
push : LinkedList a, a -> LinkedList a
push = \list, item -> Cons {first: item, rest: list}
linkedToList : LinkedList a -> List a
linkedToList = \list -> when list is
    Nil -> []
    Cons {first, rest} -> List.prepend (linkedToList rest) first

signature : Concept -> Set Entity
signature = \concept ->
    when concept is
        AtomicConcept id -> Set.single (AtomicConcept id)
        Conjunction {left, right} -> Set.union (signature left) (signature right)
        ExistentialRestriction {role: Role id, concept: filler} -> Set.union (Set.single (Role id)) (signature filler)

conceptSignature : Concept -> Set Concept
conceptSignature = \concept ->
    when concept is
        AtomicConcept id -> Set.single concept
        Conjunction {left, right} -> Set.union (conceptSignature left) (conceptSignature right) |> Set.union (Set.single concept)
        ExistentialRestriction {role: Role id, concept: filler} -> Set.union (conceptSignature filler) (Set.single concept)

axiomSignature : Axiom -> Set Entity
axiomSignature = \axiom ->
    when axiom is
        ConceptInclusion {subclass, superclass} -> Set.union (signature subclass) (signature superclass)
        RoleInclusion {subproperty: Role sub, superproperty: Role sup} -> Set.fromList [Role sub, Role sup]
        RoleComposition {first : Role first, second : Role second, superproperty : Role sup} -> Set.fromList [Role first, Role second, Role sup]

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
    propagations : Dict Concept (Dict Role (List ExistentialRestriction))
}

emptyState : State
emptyState = {
    todo : Nil,
    hier: Dict.empty {},
    hierList: Dict.empty {},
    hierComps: Dict.empty {},
    assertions: Nil,
    inits: Set.empty {},
    assertedConceptInclusionsBySubclass: Dict.empty {},
    closureSubsBySuperclass: Dict.single bottom (Set.empty {}),
    closureSubsBySubclass: Dict.single top (Set.empty {}),
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
        |> List.keepOks \e -> when e is
            Role id -> Ok (Role id)
            _ -> Err {}
    allRoleInclusions = List.keepOks axiomsList \ax -> when ax is
        RoleInclusion ri -> Ok ri
        _ -> Err {}
    hier = List.walk allRoles (saturateRoles allRoleInclusions) \accum, role ->
        Dict.update accum role \possibleValue -> when possibleValue is
            Missing -> Present (Set.single role)
            Present roleSet -> Present (Set.insert roleSet role)
    hierList = Dict.walk hier (Dict.empty {}) \accum, role, supers -> 
        Dict.insert accum role (Set.toList supers)
    allRoleCompositions = List.keepOks axiomsList \ax -> when ax is
        RoleComposition rc -> Ok rc
        _ -> Err {}
    hierComps = indexRoleCompositions hier allRoleCompositions
    concIncs = List.keepOks axiomsList \ax -> when ax is
        ConceptInclusion ci -> Ok ci
        _ -> Err {}
    extend concIncs {emptyState & hier: hier, hierList: hierList, hierComps: hierComps}

extend : List ConceptInclusion, State -> State
extend = \axioms, state ->
    distinctConcepts = List.walk axioms (Set.empty {}) \accum, {subclass, superclass} ->
        Set.union (conceptSignature subclass) (conceptSignature superclass) |> Set.union accum
    atomicConcepts = Set.toList distinctConcepts |> List.keepOks \concept -> when concept is
        AtomicConcept id -> Ok (Conc concept)
        _ -> Err {}
    acLinkedList = List.walk atomicConcepts Nil \accum, ac -> push accum ac
    assertions = List.concat axioms (linkedToList state.assertions) |> List.walk Nil \accum, ax -> push accum ax
    computeClosure {state & assertions: assertions, todo: acLinkedList}

computeClosure : State -> State
computeClosure = \state ->
    crash ""

saturateRoles : List RoleInclusion -> Dict Role (Set Role)
saturateRoles = \roleInclusions ->
    crash ""

indexRoleCompositions : Dict Role (Set Role), List RoleComposition -> Dict Role (Dict Role (List Role))
indexRoleCompositions = \hier, chains ->
    crash ""
