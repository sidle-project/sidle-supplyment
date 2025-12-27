------------------- MODULE rwlock -------------------
EXTENDS Integers, Sequences, TLC

Range(s) == { s[i] : i \in 1..Len(s) }

(* --algorithm rwlock
variables 
    n1 = "n1", n2 = "n2", p = "p",
    nodes = [node1 |-> [val |-> 1, deleted |-> FALSE], 
             node2 |-> [val |-> 0, deleted |-> FALSE]], 
    root_child = n1,
    locks = [lk \in {n1, n2, p} |-> "free"];

define
    SuccessionProperty == 
        IF root_child = n1 THEN nodes.node1.deleted = FALSE
        ELSE nodes.node2.deleted = FALSE
end define;

macro write_lock(id) begin  
    await locks[id] = "free";
    locks[id] := "locked";
end macro;

macro unlock(id) begin
    locks[id] := "free";
end macro;

\* Migrator: Follows P -> N order
process migrator = "Migrator"
variable new_node = n2;
begin
    M1: write_lock(p);          \* Lock parent first
    M2: write_lock(root_child); \* Then lock child
    M_Update: 
        nodes.node2.val := nodes.node1.val;
        root_child := n2;       \* Update parent node pointer
    M3: nodes.node1.deleted := TRUE;
        unlock(n1);
    M4: unlock(p);
end process;

\* Reader: Also follows P -> N coupling order (Lock Coupling)
process reader \in {"R1", "R2"}
variable current_node = n1;
begin
    R1: write_lock(p);          \* Must lock parent node first to view pointer
        current_node := root_child;
    R2: write_lock(current_node); \* Coupling: Acquire child lock while holding parent lock
    R3: unlock(p);              \* Can safely release parent lock now
        \* Validation: Under Lock Crabbing protection, reads are always consistent
        \* reader will never see a deleted node
        if current_node = n1 then
            assert nodes.node1.deleted = FALSE;
        else
            assert nodes.node2.deleted = FALSE;
        end if;
    R4: unlock(current_node);
end process;

\* Writer: Simple update operation, also needs to follow order or be blocked by migration lock
process writer = "Writer"
variable target = n1;
begin
    W1: target := root_child;
    W2: write_lock(target);
        if target = n1 then nodes.node1.val := nodes.node1.val + 1;
        else nodes.node2.val := nodes.node2.val + 1;
        end if;
    W3: unlock(target);
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "174f5fdb" /\ chksum(tla) = "c0a7ec52")
VARIABLES pc, n1, n2, p, nodes, root_child, locks

(* define statement *)
SuccessionProperty ==
    IF root_child = n1 THEN nodes.node1.deleted = FALSE
    ELSE nodes.node2.deleted = FALSE

VARIABLES new_node, current_node, target

vars == << pc, n1, n2, p, nodes, root_child, locks, new_node, current_node, 
           target >>

ProcSet == {"Migrator"} \cup ({"R1", "R2"}) \cup {"Writer"}

Init == (* Global variables *)
        /\ n1 = "n1"
        /\ n2 = "n2"
        /\ p = "p"
        /\ nodes = [node1 |-> [val |-> 1, deleted |-> FALSE],
                    node2 |-> [val |-> 0, deleted |-> FALSE]]
        /\ root_child = n1
        /\ locks = [lk \in {n1, n2, p} |-> "free"]
        (* Process migrator *)
        /\ new_node = n2
        (* Process reader *)
        /\ current_node = [self \in {"R1", "R2"} |-> n1]
        (* Process writer *)
        /\ target = n1
        /\ pc = [self \in ProcSet |-> CASE self = "Migrator" -> "M1"
                                        [] self \in {"R1", "R2"} -> "R1"
                                        [] self = "Writer" -> "W1"]

M1 == /\ pc["Migrator"] = "M1"
      /\ locks[p] = "free"
      /\ locks' = [locks EXCEPT ![p] = "locked"]
      /\ pc' = [pc EXCEPT !["Migrator"] = "M2"]
      /\ UNCHANGED << n1, n2, p, nodes, root_child, new_node, current_node, 
                      target >>

M2 == /\ pc["Migrator"] = "M2"
      /\ locks[root_child] = "free"
      /\ locks' = [locks EXCEPT ![root_child] = "locked"]
      /\ pc' = [pc EXCEPT !["Migrator"] = "M_Update"]
      /\ UNCHANGED << n1, n2, p, nodes, root_child, new_node, current_node, 
                      target >>

M_Update == /\ pc["Migrator"] = "M_Update"
            /\ nodes' = [nodes EXCEPT !.node2.val = nodes.node1.val]
            /\ root_child' = n2
            /\ pc' = [pc EXCEPT !["Migrator"] = "M3"]
            /\ UNCHANGED << n1, n2, p, locks, new_node, current_node, target >>

M3 == /\ pc["Migrator"] = "M3"
      /\ nodes' = [nodes EXCEPT !.node1.deleted = TRUE]
      /\ locks' = [locks EXCEPT ![n1] = "free"]
      /\ pc' = [pc EXCEPT !["Migrator"] = "M4"]
      /\ UNCHANGED << n1, n2, p, root_child, new_node, current_node, target >>

M4 == /\ pc["Migrator"] = "M4"
      /\ locks' = [locks EXCEPT ![p] = "free"]
      /\ pc' = [pc EXCEPT !["Migrator"] = "Done"]
      /\ UNCHANGED << n1, n2, p, nodes, root_child, new_node, current_node, 
                      target >>

migrator == M1 \/ M2 \/ M_Update \/ M3 \/ M4

R1(self) == /\ pc[self] = "R1"
            /\ locks[p] = "free"
            /\ locks' = [locks EXCEPT ![p] = "locked"]
            /\ current_node' = [current_node EXCEPT ![self] = root_child]
            /\ pc' = [pc EXCEPT ![self] = "R2"]
            /\ UNCHANGED << n1, n2, p, nodes, root_child, new_node, target >>

R2(self) == /\ pc[self] = "R2"
            /\ locks[current_node[self]] = "free"
            /\ locks' = [locks EXCEPT ![current_node[self]] = "locked"]
            /\ pc' = [pc EXCEPT ![self] = "R3"]
            /\ UNCHANGED << n1, n2, p, nodes, root_child, new_node, 
                            current_node, target >>

R3(self) == /\ pc[self] = "R3"
            /\ locks' = [locks EXCEPT ![p] = "free"]
            /\ IF current_node[self] = n1
                  THEN /\ Assert(nodes.node1.deleted = FALSE, 
                                 "Failure of assertion at line 54, column 13.")
                  ELSE /\ Assert(nodes.node2.deleted = FALSE, 
                                 "Failure of assertion at line 56, column 13.")
            /\ pc' = [pc EXCEPT ![self] = "R4"]
            /\ UNCHANGED << n1, n2, p, nodes, root_child, new_node, 
                            current_node, target >>

R4(self) == /\ pc[self] = "R4"
            /\ locks' = [locks EXCEPT ![current_node[self]] = "free"]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << n1, n2, p, nodes, root_child, new_node, 
                            current_node, target >>

reader(self) == R1(self) \/ R2(self) \/ R3(self) \/ R4(self)

W1 == /\ pc["Writer"] = "W1"
      /\ target' = root_child
      /\ pc' = [pc EXCEPT !["Writer"] = "W2"]
      /\ UNCHANGED << n1, n2, p, nodes, root_child, locks, new_node, 
                      current_node >>

W2 == /\ pc["Writer"] = "W2"
      /\ locks[target] = "free"
      /\ locks' = [locks EXCEPT ![target] = "locked"]
      /\ IF target = n1
            THEN /\ nodes' = [nodes EXCEPT !.node1.val = nodes.node1.val + 1]
            ELSE /\ nodes' = [nodes EXCEPT !.node2.val = nodes.node2.val + 1]
      /\ pc' = [pc EXCEPT !["Writer"] = "W3"]
      /\ UNCHANGED << n1, n2, p, root_child, new_node, current_node, target >>

W3 == /\ pc["Writer"] = "W3"
      /\ locks' = [locks EXCEPT ![target] = "free"]
      /\ pc' = [pc EXCEPT !["Writer"] = "Done"]
      /\ UNCHANGED << n1, n2, p, nodes, root_child, new_node, current_node, 
                      target >>

writer == W1 \/ W2 \/ W3

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == migrator \/ writer
           \/ (\E self \in {"R1", "R2"}: reader(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=========================================================================
