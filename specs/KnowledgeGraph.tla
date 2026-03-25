---- MODULE KnowledgeGraph ----
(******************************************************************)
(* TLA+ specification of ontograph KnowledgeGraph invariants.     *)
(* Models the core state machine: adding entities and relations   *)
(* to a knowledge graph with type constraints.                    *)
(******************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    EntityTypes,
    RelationTypes,
    MaxEntities,
    MaxRelations

VARIABLES
    entities,
    relations,
    entity_count,
    relation_count

vars == <<entities, relations, entity_count, relation_count>>

EntityNames == {"Firm", "Bank", "Household", "CentralBank", "GoodsMarket"}

(* Type invariant *)
TypeOK ==
    /\ entity_count \in 0..MaxEntities
    /\ relation_count \in 0..MaxRelations

(* Entity count matches domain size *)
EntityDedup ==
    Cardinality(DOMAIN entities) = entity_count

(* No self-loops *)
NoSelfLoops ==
    \A r \in relations: r[1] /= r[2]

(* All relation endpoints reference existing entities *)
RelationsGrounded ==
    \A r \in relations:
        /\ r[1] \in DOMAIN entities
        /\ r[2] \in DOMAIN entities

(* Relation count matches set size *)
RelationCountConsistent ==
    Cardinality(relations) = relation_count

Init ==
    /\ entities = [x \in {} |-> ""]
    /\ relations = {}
    /\ entity_count = 0
    /\ relation_count = 0

AddEntity(name, etype) ==
    /\ entity_count < MaxEntities
    /\ name \in EntityNames
    /\ etype \in EntityTypes
    /\ IF name 
otin DOMAIN entities
       THEN /\ entities' = [x \in (DOMAIN entities \cup {name}) |-> IF x = name THEN etype ELSE entities[x]]
            /\ entity_count' = entity_count + 1
       ELSE /\ entities' = entities
            /\ entity_count' = entity_count
    /\ UNCHANGED <<relations, relation_count>>

AddRelation(source, target, rtype) ==
    /\ relation_count < MaxRelations
    /\ source \in DOMAIN entities
    /\ target \in DOMAIN entities
    /\ source /= target
    /\ rtype \in RelationTypes
    /\ <<source, target, rtype>> 
otin relations
    /\ relations' = relations \cup {<<source, target, rtype>>}
    /\ relation_count' = relation_count + 1
    /\ UNCHANGED <<entities, entity_count>>

Next ==
    \/ \E name \in EntityNames, etype \in EntityTypes:
        AddEntity(name, etype)
    \/ \E s \in DOMAIN entities, t \in DOMAIN entities, rt \in RelationTypes:
        AddRelation(s, t, rt)

Spec == Init /\ [][Next]_vars

====