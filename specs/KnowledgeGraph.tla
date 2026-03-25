---- MODULE KnowledgeGraph ----
(******************************************************************)
(* TLA+ specification of ontograph KnowledgeGraph invariants.     *)
(* Models adding entities and relations with type constraints.    *)
(******************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    EntityTypes,
    RelationTypes,
    EntityNames,
    MaxEntities,
    MaxRelations

VARIABLES
    entities,
    relations

vars == <<entities, relations>>

(* Type invariant *)
TypeOK ==
    /\ \A name \in DOMAIN entities: entities[name] \in EntityTypes
    /\ \A r \in relations:
        /\ r[1] \in STRING
        /\ r[2] \in STRING
        /\ r[3] \in RelationTypes

(* No self-loops: source != target *)
NoSelfLoops ==
    \A r \in relations: r[1] /= r[2]

(* All relation endpoints reference existing entities *)
RelationsGrounded ==
    \A r \in relations:
        /\ r[1] \in DOMAIN entities
        /\ r[2] \in DOMAIN entities

(* Entity count bounded *)
EntityBounded ==
    Cardinality(DOMAIN entities) <= MaxEntities

(* Relation count bounded *)
RelationBounded ==
    Cardinality(relations) <= MaxRelations

Init ==
    /\ entities = [x \in {} |-> ""]
    /\ relations = {}

AddEntity(name, etype) ==
    /\ Cardinality(DOMAIN entities) < MaxEntities
    /\ name \in EntityNames
    /\ etype \in EntityTypes
    /\ name \notin DOMAIN entities
    /\ entities' = [x \in (DOMAIN entities \union {name}) |->
                        IF x = name THEN etype ELSE entities[x]]
    /\ UNCHANGED relations

MergeEntity(name) ==
    /\ name \in DOMAIN entities
    /\ UNCHANGED <<entities, relations>>

AddRelation(source, target, rtype) ==
    /\ Cardinality(relations) < MaxRelations
    /\ source \in DOMAIN entities
    /\ target \in DOMAIN entities
    /\ source /= target
    /\ rtype \in RelationTypes
    /\ <<source, target, rtype>> \notin relations
    /\ relations' = relations \union {<<source, target, rtype>>}
    /\ UNCHANGED entities

Next ==
    \/ \E name \in EntityNames, etype \in EntityTypes:
        AddEntity(name, etype)
    \/ \E name \in EntityNames:
        MergeEntity(name)
    \/ \E s \in DOMAIN entities, t \in DOMAIN entities, rt \in RelationTypes:
        AddRelation(s, t, rt)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
