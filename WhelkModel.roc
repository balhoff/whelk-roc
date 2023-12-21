interface WhelkModel
    exposes [
        Role,
        Entity,
        Conjunction,
        ExistentialRestriction,
        Concept,
        owl,
        ConceptInclusion,
        RoleInclusion,
        RoleComposition,
        Axiom,
        QueueItem,
        signature,
        conceptSignature,
        axiomSignature,
    ]
    imports []

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
